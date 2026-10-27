#!/usr/bin/env python3
"""Measure how well the lexical parser approximates the Lean 4 kernel.

The parser recovers declarations and their dependencies from Lean source text with regular
expressions. This script builds the same graph from the *elaborated* environment - the
constants the kernel actually holds after ``lake build`` - and scores one against the other.

How the ground truth is built
-----------------------------
``lean_kernel_deps.lean`` dumps every constant in the project's own modules with its flags,
source range and used constants (type and value, split into project-internal and external).
Each constant is then sorted into one of three buckets by the source text its declaration
range points at:

  source_supported    written with a command the parser handles (theorem/lemma/def/abbrev/
                      structure/class/axiom, and named instance/alias). The ground truth.
  source_unsupported  written with a command the parser cannot express (anonymous instance,
                      notation, inductive, macro, ...). Excluded and reported separately.
  generated           not written in the source at all: constructors, recursors, projections,
                      auxiliary definitions, `to_additive` and `deriving` siblings. Excluded,
                      and *contracted*: their dependencies are inlined into whatever referred
                      to them, so an A -> aux -> B chain scores as A -> B.

A declaration's kernel dependencies are the constants in its type and value, restricted to
the project itself; references into Mathlib and core are reported only descriptively, since
the parser cannot see them by construction.

Requirements
------------
Each project must be built (``lake exe cache get && lake build``), because the dump reads the
compiled environment; pass --build to do that here. A project that only partly compiles is
analysed on the modules that did, and the coverage is reported.

Examples
--------
    # Verify one project (already built):
    python validation/verify.py path/to/pfr

    # Build first, then verify several projects and pool the results:
    python validation/verify.py --build path/to/pfr path/to/flt

    # Re-score without re-running Lean (cheap; use when only the parser changed):
    python validation/verify.py --skip-extract path/to/pfr

    # Score a saved parse (from `lean-deps PROJECT -o parse.json`) instead of re-parsing:
    python validation/verify.py path/to/pfr --parse-json parse.json
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import subprocess
import sys
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

from lexical_lean_parser import DEFAULT_FILE_PATTERN, Declaration, parse_dependencies
from lexical_lean_parser import _lexer as lx

LEAN_TEMPLATE = Path(__file__).resolve().parent / "lean_kernel_deps.lean"


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def mean(xs) -> float:
    xs = list(xs)
    return statistics.mean(xs) if xs else 0.0


# A name component that Lean prints without «» quotes.
_PLAIN_COMPONENT = re.compile(rf"[{lx._ID_FIRST}][{lx._ID_REST}]*")


def module_name(rel: Path) -> str:
    """The module a source file compiles to, exactly as Lean prints (and imports) it.

    Path components that are not identifiers are quoted: `Arxiv/0805.3777/TensorRank.lean`
    is `Arxiv.«0805.3777».TensorRank`.
    """
    return ".".join(c if _PLAIN_COMPONENT.fullmatch(c) else f"«{c}»"
                    for c in rel.with_suffix("").parts)


def module_path(module: str) -> Path:
    """The source file of a module, relative to the project: the inverse of `module_name`."""
    return Path(*(q or plain for q, plain in re.findall(r"«([^»]*)»|([^.]+)", module))
                ).with_suffix(".lean")


# ---------------------------------------------------------------------------
# Source-level classification of kernel constants
# ---------------------------------------------------------------------------

SUPPORTED_KW = {"theorem", "lemma", "def", "abbrev", "structure", "class", "axiom", "constant"}
# Commands the parser can express only when the source writes an explicit name. An anonymous
# `instance : Foo := ...` is named by Lean after its type, which no surface parser can
# reproduce, so those stay out of the ground truth.
CONDITIONAL_KW = {"instance", "alias"}
UNSUPPORTED_KW = {
    "inductive", "example", "syntax", "macro", "macro_rules", "elab",
    "elab_rules", "notation", "opaque", "irreducible_def", "initialize", "builtin_initialize",
    "register_simp_attr", "declare_config_elab", "deriving", "attribute", "add_decl_doc",
    "unif_hint", "partial_fixpoint", "termination_by",
}
KEYWORDS = SUPPORTED_KW | UNSUPPORTED_KW | CONDITIONAL_KW
MODIFIERS = {
    "private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "scoped",
    "local", "mutual", "public", "recursive",
}

DOC_RE = re.compile(r"/--.*?-/|/-.*?-/|--[^\n]*", re.DOTALL)
IDENT_RE = re.compile(r"(_root_\.)?[^\s(){}\[\],:;`\"]+")
KW_TOKEN_RE = re.compile(
    rf"(?<![\w.'])({'|'.join(sorted(KEYWORDS, key=len, reverse=True))})(?![\w'])")
NOTATION_RE = re.compile(
    r"(?<![\w.'])(notation3|notation|infixl|infixr|infix|prefix|postfix)(?![\w'])")
LOOKBACK_LINES = 8


@cache
def source_lines(repo_dir: Path, module: str) -> tuple[str, ...]:
    """Lines of the source file a module was compiled from."""
    path = repo_dir / module_path(module)
    if not path.exists():
        return ()
    return tuple(path.read_text(encoding="utf-8", errors="ignore").splitlines())


def selection_line(repo_dir: Path, row: dict) -> str | None:
    """The source line holding the constant's selection range (its name), if known."""
    rng = row["range"]
    lines = source_lines(repo_dir, row["module"])
    if rng is None or not lines or rng["selLine"] > len(lines):
        return None
    return lines[rng["selLine"] - 1]


def strip_attributes(text: str) -> str:
    """Remove ``@[...]`` attribute blocks, honouring nested brackets."""
    out, i = [], 0
    while i < len(text):
        if text.startswith("@[", i):
            depth, i = 0, i + 1
            while i < len(text):
                if text[i] == "[":
                    depth += 1
                elif text[i] == "]":
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def node_id(row: dict) -> str:
    """Source-level identity of a constant, with private name mangling undone."""
    return row["userName"] or row["name"]


def in_attribute(repo_dir: Path, row: dict) -> bool:
    """Whether the selection range points inside an ``@[...]`` attribute.

    If it does, an attribute such as ``to_additive`` produced the constant, rather than it
    being written as a declaration of its own.
    """
    if (line := selection_line(repo_dir, row)) is None:
        return False
    col, depth, i = row["range"]["selCol"], 0, 0
    while i < len(line):
        if line.startswith("@[", i):
            depth += 1
            i += 2
            continue
        if depth and line[i] == "[":
            depth += 1
        elif depth and line[i] == "]":
            depth -= 1
        if i == col and depth:
            return True
        i += 1
    return False


def command_at_range(repo_dir: Path, row: dict) -> str | None:
    """The command keyword written at the range, for commands with no identifier.

    Anonymous ``instance``s and notation commands have nothing to point at, so Lean anchors
    their range on the keyword itself.
    """
    if (line := selection_line(repo_dir, row)) is None:
        return None
    for tok in line[row["range"]["selCol"]:].split():
        if tok not in MODIFIERS:
            return tok if tok in KEYWORDS else None
    return None


def notation_command(repo_dir: Path, row: dict) -> str | None:
    """Detect notation-like commands, whose ranges do not point at an identifier."""
    if (line := selection_line(repo_dir, row)) is None:
        return None
    m = NOTATION_RE.search(line)
    return m.group(1) if m else None


def source_probe(repo_dir: Path, row: dict) -> tuple[str | None, str | None]:
    """Return (identifier written at the declaration range, nearest command keyword).

    The selection range points exactly at the identifier of the declaring command, so that
    identifier is a suffix of the kernel's full name whenever the constant really was
    declared there.
    """
    if (line := selection_line(repo_dir, row)) is None:
        return None, None
    rng = row["range"]
    lines = source_lines(repo_dir, row["module"])
    m = IDENT_RE.match(line, rng["selCol"])
    start = max(0, rng["selLine"] - 1 - LOOKBACK_LINES)
    before = "\n".join(lines[start:rng["selLine"] - 1]) + "\n" + line[: rng["selCol"]]
    kws = KW_TOKEN_RE.findall(strip_attributes(DOC_RE.sub(" ", before)))
    return (m.group(0) if m else None), (kws[-1] if kws else None)


def classify(repo_dir: Path, row: dict) -> tuple[str, str]:
    """Sort one kernel constant into (bucket, detail)."""
    if row["isCtor"] or row["isRec"] or row["isAuxRec"] or row["isNoConfusion"] or row["isProj"]:
        return "generated", "structural"
    name = node_id(row)
    if row["isInternalDetail"] and not row["isPrivate"]:
        return "generated", "internal-name"
    if row["isPrivate"] and re.search(r"(^|\.)_", name):
        return "generated", "internal-name"
    if in_attribute(repo_dir, row):
        return "generated", "attribute-generated"

    ident, kw = source_probe(repo_dir, row)
    if ident is None:
        return "generated", "no-declaration-range"

    written = ident.removeprefix("_root_.")
    declared = bool(written) and (name == written or name.endswith("." + written))
    if (kw_at := command_at_range(repo_dir, row)) is not None:
        kw = kw_at
    if not declared and (nk := notation_command(repo_dir, row)) is not None:
        return "source_unsupported", nk
    if kw in CONDITIONAL_KW:
        # Named ones are within reach of the parser; anonymous ones are not.
        return ("source_supported", kw) if declared else ("source_unsupported", f"{kw} (anonymous)")
    if kw in UNSUPPORTED_KW:
        return "source_unsupported", kw
    if kw in SUPPORTED_KW:
        # Right command, but the name written there is not this constant's: an elaborator
        # sibling (to_additive, deriving, equation lemma, ...).
        return ("source_supported", kw) if declared else ("generated", f"sibling-of-{kw}")
    return "generated", f"other-command:{kw}"


def load_kernel(dump: Path, repo_dir: Path) -> tuple[dict, dict]:
    """Read the kernel dump and classify every constant in it."""
    with dump.open() as f:
        rows = [json.loads(line) for line in f]
    return {r["name"]: r for r in rows}, {r["name"]: classify(repo_dir, r) for r in rows}


# ---------------------------------------------------------------------------
# Parser side
# ---------------------------------------------------------------------------


def full_name(namespace: str | None, name: str) -> str:
    return f"{namespace}.{name}" if namespace else name


def _finalise(decls: dict, edges: dict, dupes: list) -> tuple[dict, dict, list]:
    """Drop self-edges and edges pointing outside the declaration set under analysis."""
    trimmed = {fn: {t for t in targets if t != fn and t in decls}
               for fn, targets in edges.items() if fn in decls}
    return decls, {fn: t for fn, t in trimmed.items() if t}, dupes


def load_parser_json(path: Path, modules: set[str]) -> tuple[dict, dict, list]:
    """Load a parse saved by ``lean-deps PROJECT --format json``, restricted to `modules`."""
    decls, dupes = {}, []
    edges = defaultdict(set)
    for file_key, items in json.loads(path.read_text()).items():
        module = module_name(Path(file_key))
        if module not in modules:
            continue
        for d in items:
            if d["kind"] == "import":
                continue
            fn = full_name(d.get("namespace"), d["name"])
            if fn in decls:
                dupes.append(fn)
            decls[fn] = {"kind": d["kind"], "module": module}
            for dep in d["depends_on"]:
                edges[fn].add(full_name(dep.get("namespace"), dep["name"]))
    return _finalise(decls, edges, dupes)


def run_parser(repo_dir: Path, file_pattern: str, modules: set[str]) -> tuple[dict, dict, list]:
    """Run the parser in-process, so the parse is guaranteed to match the working tree."""
    deps = parse_dependencies(repo_dir, file_pattern=file_pattern)
    decls, dupes = {}, []
    edges: dict[str, set[str]] = defaultdict(set)
    for file, items in deps.items():
        module = module_name(file.relative_to(repo_dir))
        if module not in modules:
            continue
        for d in items:
            if not isinstance(d, Declaration):
                continue
            fn = d.full_name
            if fn in decls:
                dupes.append(fn)
            # `text` is everything the parser tokenises, for attributing errors to causes.
            decls[fn] = {"kind": d.kind, "module": module, "indexed_as": d.name,
                         "text": f"{d.definition}\n{d.body}"}
            for dep in d.depends_on:
                edges[fn].add(dep.full_name)
    return _finalise(decls, edges, dupes)


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------


def prf(tp: int, fp: int, fn: int) -> dict:
    """Precision, recall and F1 alongside the raw counts."""
    p = tp / (tp + fp) if tp + fp else 0.0
    r = tp / (tp + fn) if tp + fn else 0.0
    return {"precision": p, "recall": r, "f1": 2 * p * r / (p + r) if p + r else 0.0,
            "tp": tp, "fp": fp, "fn": fn}


def jaccard(a: set, b: set) -> float:
    return len(a & b) / len(a | b) if (a or b) else 1.0


def spearman(xs: list[float], ys: list[float]) -> float:
    """Spearman rank correlation, with midranks for ties."""

    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(order):
            j = i
            while j + 1 < len(order) and v[order[j + 1]] == v[order[i]]:
                j += 1
            for k in range(i, j + 1):
                r[order[k]] = (i + j) / 2 + 1
            i = j + 1
        return r

    if len(xs) < 2:
        return 0.0
    rx, ry = rank(xs), rank(ys)
    mx, my = mean(rx), mean(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry, strict=True))
    den = (sum((a - mx) ** 2 for a in rx) * sum((b - my) ** 2 for b in ry)) ** 0.5
    return num / den if den else 0.0


def link_partners(by_kname: dict) -> None:
    """Record, as `partners`, the generated constants that hold a declaration's dependencies.

    A structure's fields and parents are in its constructor's type, not in its own; the body of
    a `partial def` is in `<name>._unsafe_rec`, the kernel constant being an opaque stub.
    """
    for name, row in by_kname.items():
        if row.get("isCtor"):
            parent = by_kname.get(name.rpartition(".")[0])
            if parent is not None:
                parent.setdefault("partners", []).append(name)
        elif not row.get("hasValue") and f"{name}._unsafe_rec" in by_kname:
            row.setdefault("partners", []).append(f"{name}._unsafe_rec")


def contracted_deps(kname: str, by_kname: dict, generated: set[str], cache: dict) -> set[str]:
    """Project-internal dependencies of a constant, inlining generated intermediaries."""
    if kname in cache:
        return cache[kname]
    cache[kname] = set()  # cycle guard
    out: set[str] = set()
    if (row := by_kname.get(kname)) is not None:
        for dep in set(row["typeDepsInternal"] + row["valueDepsInternal"]
                       + row.get("partners", [])):
            if dep in generated:
                out |= contracted_deps(dep, by_kname, generated, cache)
            else:
                drow = by_kname.get(dep)
                out.add(node_id(drow) if drow else dep)
    cache[kname] = out
    return out


def token_in(text: str, tok: str) -> bool:
    return re.search(rf"(?<![\w.']){re.escape(tok)}(?![\w'])", text) is not None


def written_anywhere(target: str, text: str) -> bool:
    """Whether any dotted suffix of the target's name is written as a token in the text."""
    parts = target.split(".")
    return any(token_in(text, ".".join(parts[i:])) for i in range(len(parts)))


NOTATION_DEF_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:local\s+|scoped\s+)*"
    r"(?:notation3|notation|infixl|infixr|infix|prefix|postfix)\b[^=]*=>(?P<rhs>.*)$")
NAME_TOKEN = re.compile(r"[A-Za-z_][\w'.]*")


def notation_targets(repo_dir: Path, modules: set[str]) -> set[str]:
    """Leaf names on the right-hand side of the project's notation commands."""
    targets: set[str] = set()
    for module in modules:
        for line in source_lines(repo_dir, module):
            if m := NOTATION_DEF_RE.match(line):
                targets.update(t.split(".")[-1] for t in NAME_TOKEN.findall(m.group("rhs")))
    return targets


def declaration_text(repo_dir: Path, row: dict) -> str:
    rng = row["range"]
    if rng is None:
        return ""
    lines = source_lines(repo_dir, row["module"])
    return "\n".join(lines[max(0, rng["startLine"] - 1):min(len(lines), rng["endLine"])])


MISS_NOTATION = "target reachable only through a notation declared in this project"
MISS_INVISIBLE = ("target never written in the source "
                  "(instance synthesis, variable binder, coercion)")
MISS_UNTOKENISED = ("target written only outside the text the parser tokenises "
                    "(`variable` binders, attributes, multi-line notation)")
MISS_QUALIFIED = "written qualified but indexed unqualified (or vice versa)"
MISS_RESOLUTION = ("token present and indexed, dropped during resolution "
                   "(ambiguity / namespace preference / argument filter)")
FALSE_SHADOW = ("name occurs in the text but is not a real dependency "
                "(local hypothesis / bound variable shadowing a global name)")
FALSE_ABSENT = "name does not occur in the tokenised text at all"
FALSE_NOBODY = "source declaration has no kernel body (partial/opaque def)"


def analyse(repo_dir: Path, by_kname: dict, cls: dict, p_decls: dict, p_edges: dict,
            p_dupes: list, attribute_causes: bool) -> dict:
    """Score the parser's declarations and dependencies against the kernel."""
    generated = {k for k, (b, _) in cls.items() if b == "generated"}
    gt = {node_id(by_kname[k]): by_kname[k]
          for k, (b, _) in cls.items() if b == "source_supported"}
    unsupported = {node_id(by_kname[k]): d
                   for k, (b, d) in cls.items() if b == "source_unsupported"}

    out: dict = {"corpus": {
        "kernel_constants_in_repo_modules": len(by_kname),
        "kernel_generated_constants": len(generated),
        "kernel_source_declarations_supported_commands": len(gt),
        "kernel_source_declarations_unsupported_commands": len(unsupported),
        "parser_declarations": len(p_decls),
        "parser_duplicate_full_names": len(p_dupes),
    }, "unsupported_commands": dict(Counter(unsupported.values()).most_common())}

    # ---- declarations
    gt_names, p_names = set(gt), set(p_decls)
    tp, fp, fn = gt_names & p_names, p_names - gt_names, gt_names - p_names
    out["nodes"] = prf(len(tp), len(fp), len(fn)) | {
        "ground_truth": len(gt_names), "parser": len(p_names),
        "missed_by_kind": dict(Counter(gt[n]["kind"] for n in fn).most_common()),
        "missed_by_module": dict(Counter(gt[n]["module"] for n in fn).most_common(8)),
        "kind_agreement": {f"kernel:{a}->parser:{b}": c for (a, b), c in Counter(
            (gt[n]["kind"], p_decls[n]["kind"]) for n in tp).most_common()},
        "missed_examples": sorted(fn)[:12],
        "spurious_examples": sorted(fp)[:12],
    }

    # A declaration found but filed under the wrong namespace shows up as a missed node and a
    # spurious node that share a module and a leaf name. Counting the pairs separates
    # "namespace tracking is broken" from "the declaration was not seen".
    missed_by_leaf: dict[tuple[str, str], set[str]] = defaultdict(set)
    for n in fn:
        missed_by_leaf[(gt[n]["module"], n.split(".")[-1])].add(n)
    ns_errors = {}
    for n in fp:
        if cands := missed_by_leaf.get((p_decls[n]["module"], n.split(".")[-1])):
            ns_errors[n] = sorted(cands)[0]
    out["nodes"]["namespace_attribution_errors"] = len(ns_errors)
    out["nodes"]["namespace_attribution_examples"] = [
        f"{k}  should be  {v}" for k, v in sorted(ns_errors.items())[:8]]
    relaxed = prf(len(tp) + len(ns_errors), len(fp) - len(ns_errors), len(fn) - len(ns_errors))
    out["nodes"]["f1_if_namespaces_were_correct"] = relaxed["f1"]

    # ---- kernel edges, contracted and restricted to ground-truth targets
    link_partners(by_kname)
    cache: dict = {}
    k_edges: dict[str, set[str]] = {}
    dropped = 0
    for name, row in gt.items():
        deps = contracted_deps(row["name"], by_kname, generated, cache) - {name}
        k_edges[name] = {d for d in deps if d in gt_names}
        dropped += len(deps) - len(k_edges[name])

    ext = [len(set(r["typeDepsExternal"] + r["valueDepsExternal"])) for r in gt.values()]
    k_total = sum(len(v) for v in k_edges.values())
    out["dependency_context"] = {
        "kernel_internal_edges": k_total,
        "kernel_edges_to_unsupported_declarations_dropped": dropped,
        "kernel_external_constant_refs": sum(ext),
        "kernel_external_refs_mean_per_decl": mean(ext),
        "share_of_kernel_refs_external": sum(ext) / (sum(ext) + k_total) if k_total else 0,
        "parser_edges": sum(len(v) for v in p_edges.values()),
    }

    def matched(edges: dict, n: str) -> set[str]:
        return {d for d in edges.get(n, set()) if d in tp}

    # ---- edges over the declarations both sides agree exist
    per_decl = []
    tp_e = fp_e = fn_e = 0
    for n in sorted(tp):
        k, p = matched(k_edges, n), matched(p_edges, n)
        tp_e += len(k & p)
        fp_e += len(p - k)
        fn_e += len(k - p)
        if k or p:
            per_decl.append((n, prf(len(k & p), len(p - k), len(k - p)),
                             jaccard(k, p), len(k), len(p)))
    out["edges_matched_nodes"] = prf(tp_e, fp_e, fn_e) | {
        "kernel_edges": tp_e + fn_e, "parser_edges": tp_e + fp_e,
        "macro_precision": mean(x[1]["precision"] for x in per_decl),
        "macro_recall": mean(x[1]["recall"] for x in per_decl),
        "macro_f1": mean(x[1]["f1"] for x in per_decl),
        "mean_jaccard": mean(x[2] for x in per_decl),
        "decls_with_exactly_right_dep_set": sum(1 for x in per_decl if x[2] == 1.0),
        "decls_compared": len(per_decl),
    }

    a = b = c = 0
    for n in set(k_edges) | set(p_edges):
        k, p = k_edges.get(n, set()), p_edges.get(n, set())
        a += len(k & p)
        b += len(p - k)
        c += len(k - p)
    out["edges_all"] = prf(a, b, c)

    def module_of(n: str) -> str:
        return gt[n]["module"] if n in gt else p_decls[n]["module"]

    for label, cross in (("cross_file", True), ("within_file", False)):
        a = b = c = 0
        for n in tp:
            k = {d for d in matched(k_edges, n) if (module_of(d) != module_of(n)) == cross}
            p = {d for d in matched(p_edges, n) if (module_of(d) != module_of(n)) == cross}
            a += len(k & p)
            b += len(p - k)
            c += len(k - p)
        out[f"edges_{label}"] = prf(a, b, c)

    # ---- are missed edges at least recovered transitively?
    p_adj = {n: matched(p_edges, n) for n in tp}

    def reachable(src: str) -> set[str]:
        seen, stack = set(), [src]
        while stack:
            for v in p_adj.get(stack.pop(), ()):
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return seen

    hit = tot = 0
    for n in tp:
        if k := matched(k_edges, n):
            hit += len(k & reachable(n))
            tot += len(k)
    out["edges_matched_nodes"]["recall_via_transitive_closure"] = hit / tot if tot else 0

    # ---- degree agreement
    names = sorted(tp)
    kout = [len(matched(k_edges, n)) for n in names]
    pout = [len(matched(p_edges, n)) for n in names]
    kin = Counter(d for n in tp for d in matched(k_edges, n))
    pin = Counter(d for n in tp for d in matched(p_edges, n))
    out["degree_agreement"] = {
        "out_degree_spearman": spearman(kout, pout),
        "in_degree_spearman": spearman([kin.get(n, 0) for n in names],
                                       [pin.get(n, 0) for n in names]),
        "kernel_mean_out_degree": mean(kout),
        "parser_mean_out_degree": mean(pout),
        "kernel_decls_with_no_internal_deps": sum(1 for v in kout if v == 0),
        "parser_decls_with_no_internal_deps": sum(1 for v in pout if v == 0),
    }

    per_decl.sort(key=lambda x: (x[2], -x[3]))
    out["worst_declarations"] = [
        {"name": x[0], "jaccard": round(x[2], 3), "kernel_deps": x[3], "parser_deps": x[4]}
        for x in per_decl[:10]]

    if attribute_causes:
        out |= attribute_edge_errors(repo_dir, gt, k_edges, p_decls, p_edges, tp)
        add_ceiling(out)
    return out


def attribute_edge_errors(repo_dir: Path, gt: dict, k_edges: dict, p_decls: dict,
                          p_edges: dict, matched: set) -> dict:
    """Explain every wrong edge in terms of the stage of the parser that let it through.

    Needs the text the parser tokenised, so it only runs when the parser ran in-process.
    """
    fn_cause: Counter = Counter()
    fp_cause: Counter = Counter()
    examples: dict[str, list] = {}
    notations = notation_targets(repo_dir, {r["module"] for r in gt.values()})

    def note(bucket: Counter, key: str, msg: str) -> None:
        bucket[key] += 1
        if len(examples.setdefault(key, [])) < 6:
            examples[key].append(msg)

    for u in sorted(matched):
        row = gt[u]
        k = {d for d in k_edges.get(u, set()) if d in matched}
        p = {d for d in p_edges.get(u, set()) if d in matched}
        source = declaration_text(repo_dir, row)
        tokenised = p_decls[u].get("text", "")
        for v in k - p:
            indexed = p_decls.get(v, {}).get("indexed_as", v.split(".")[-1])
            if not written_anywhere(v, source):
                cause = MISS_NOTATION if v.split(".")[-1] in notations else MISS_INVISIBLE
                note(fn_cause, cause, f"{u} -> {v}")
            elif not written_anywhere(v, tokenised):
                note(fn_cause, MISS_UNTOKENISED, f"{u} -> {v}")
            elif not token_in(tokenised, indexed):
                note(fn_cause, MISS_QUALIFIED, f"{u} -> {v}  (indexed as '{indexed}')")
            else:
                note(fn_cause, MISS_RESOLUTION, f"{u} -> {v}  (indexed as '{indexed}')")
        for v in p - k:
            if not row["hasValue"]:
                note(fp_cause, FALSE_NOBODY, f"{u} -> {v}")
            elif written_anywhere(v, tokenised):
                note(fp_cause, FALSE_SHADOW, f"{u} -> {v}")
            else:
                note(fp_cause, FALSE_ABSENT, f"{u} -> {v}")

    total = sum(fn_cause.values())
    return {
        "missed_edges_by_cause": dict(fn_cause.most_common()),
        "invented_edges_by_cause": dict(fp_cause.most_common()),
        "share_of_misses_invisible_to_any_surface_parser":
            fn_cause[MISS_INVISIBLE] / total if total else 0,
        "error_examples": examples,
    }


def add_ceiling(out: dict) -> None:
    """Rescore recall against the edges a surface parser could possibly see.

    Two ceilings: everything not invisible in the source text, and that minus the edges only
    reachable through the project's notation (which the parser expands, but not always).
    """
    causes = out["missed_edges_by_cause"]
    em = out["edges_matched_nodes"]
    total, tp, precision = em["kernel_edges"], em["tp"], em["precision"]
    invisible = causes.get(MISS_INVISIBLE, 0)
    notation = causes.get(MISS_NOTATION, 0)

    def score(ceiling: int) -> dict:
        recall = tp / ceiling if ceiling > 0 else 0.0
        f1 = 2 * precision * recall / (precision + recall) if precision + recall else 0.0
        return {"achievable_edges": ceiling, "recall": recall, "f1": f1}

    out["edges_against_achievable_ceiling"] = {
        "kernel_edges": total,
        "unreachable_from_source_text": invisible,
        "reachable_only_through_notation": notation,
        "excluding_notation": score(total - invisible - notation),
        "including_notation": score(total - invisible),
    }


# ---------------------------------------------------------------------------
# Lean side
# ---------------------------------------------------------------------------


def compiled_modules(repo_dir: Path) -> set[str]:
    """Modules that actually built, read off the ``.olean`` files lake produced."""
    for base in (repo_dir / ".lake/build/lib/lean", repo_dir / ".lake/build/lib"):
        if base.exists() and (found := {module_name(p.relative_to(base))
                                        for p in base.rglob("*.olean")}):
            return found
    return set()


def dumped_modules(dump: Path) -> set[str]:
    """Modules with at least one constant in a kernel dump."""
    with dump.open() as f:
        return {json.loads(line)["module"] for line in f if line.strip()}


def source_modules(repo_dir: Path, file_pattern: str) -> set[str]:
    """Modules the parser would consider, per the file pattern."""
    regex = re.compile(file_pattern)
    out = set()
    for path in repo_dir.rglob("*.lean"):
        rel = path.relative_to(repo_dir)
        if ".lake" not in rel.parts and regex.search(rel.as_posix()):
            out.add(module_name(rel))
    return out


def extract_kernel_dump(repo_dir: Path, out_path: Path, modules: set[str],
                        memory_mb: int) -> None:
    """Render the Lean template for this project and run it with ``lake env lean``."""
    roots = sorted({m.split(".")[0] for m in modules})
    log(f"Importing {len(modules)} modules under roots {roots}")
    imports = "\n".join(f"import {m}" for m in sorted(modules))
    script = (LEAN_TEMPLATE.read_text()
              .replace("-- @IMPORTS@", imports)
              .replace("@OUTPUT@", str(out_path))
              .replace("@ROOTS@", ", ".join(f"`{r}" for r in roots)))
    script_path = out_path.with_name("kernel_deps_generated.lean")
    script_path.write_text(script)
    result = subprocess.run(
        ["lake", "env", "lean", f"--memory={memory_mb}", str(script_path)],
        cwd=repo_dir, capture_output=True, text=True, check=False)
    log(result.stdout.strip())
    if result.returncode != 0:
        log(result.stderr[:4000])
        msg = "Lean extraction failed. Is the project built at this commit?"
        raise RuntimeError(msg)


def build_project(repo_dir: Path) -> None:
    """Fetch the Mathlib cache (if the project uses Mathlib) and build the project."""
    cmds = [["lake", "build"]]
    manifest = repo_dir / "lake-manifest.json"
    if manifest.exists() and '"mathlib"' in manifest.read_text():
        cmds.insert(0, ["lake", "exe", "cache", "get"])
    for cmd in cmds:
        log(f"$ {' '.join(cmd)}")
        if subprocess.run(cmd, cwd=repo_dir, check=False).returncode != 0:
            msg = f"{' '.join(cmd)} failed"
            raise RuntimeError(msg)


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def report(out: dict, repo: str, commit: str) -> str:
    """Render the headline numbers for one project as Markdown."""
    c, n, e = out["corpus"], out["nodes"], out["edges_matched_nodes"]
    dc, dg = out["dependency_context"], out["degree_agreement"]
    lines = [
        f"# Parser vs. Lean 4 kernel - {repo} @ {commit}", "",
        "## Corpus", "",
        "| | count |", "|---|---|",
        f"| modules analysed | {c['modules_analysed']} / {c['modules_in_repo']} "
        f"({c['module_coverage']:.1%}) |",
        f"| kernel constants in project modules | {c['kernel_constants_in_repo_modules']} |",
        f"| generated (contracted away) | {c['kernel_generated_constants']} |",
        f"| source declarations, supported commands (ground truth) | "
        f"{c['kernel_source_declarations_supported_commands']} |",
        f"| source declarations, unsupported commands | "
        f"{c['kernel_source_declarations_unsupported_commands']} |",
        f"| parser declarations | {c['parser_declarations']} |", "",
        "Unsupported commands: " + (", ".join(
            f"`{k}` {v}" for k, v in out["unsupported_commands"].items()) or "none"), "",
        "## Declaration extraction", "",
        "| metric | value |", "|---|---|",
        f"| precision | {n['precision']:.3f} |",
        f"| recall | {n['recall']:.3f} |",
        f"| F1 | {n['f1']:.3f} |",
        f"| missed / spurious | {n['fn']} / {n['fp']} |", "",
        "## Dependency edges (declarations both sides agree exist)", "",
        "| metric | value |", "|---|---|",
        f"| kernel edges | {e['kernel_edges']} |",
        f"| parser edges | {e['parser_edges']} |",
        f"| micro precision | {e['precision']:.3f} |",
        f"| micro recall | {e['recall']:.3f} |",
        f"| micro F1 | {e['f1']:.3f} |",
        f"| macro precision / recall | {e['macro_precision']:.3f} / {e['macro_recall']:.3f} |",
        f"| mean Jaccard per declaration | {e['mean_jaccard']:.3f} |",
        f"| exactly right dep sets | {e['decls_with_exactly_right_dep_set']} / "
        f"{e['decls_compared']} |",
        f"| cross-file recall | {out['edges_cross_file']['recall']:.3f} |",
        f"| within-file recall | {out['edges_within_file']['recall']:.3f} |",
        f"| out-degree Spearman | {dg['out_degree_spearman']:.3f} |",
        f"| in-degree Spearman | {dg['in_degree_spearman']:.3f} |",
        f"| recall via transitive closure | {e['recall_via_transitive_closure']:.3f} |", "",
        f"{dc['share_of_kernel_refs_external']:.1%} of kernel references point outside the "
        f"project ({dc['kernel_external_constant_refs']} refs, mean "
        f"{dc['kernel_external_refs_mean_per_decl']:.1f} per declaration); out of scope by "
        "construction.", "",
    ]
    for title, key in (("Why edges are missed", "missed_edges_by_cause"),
                       ("Why edges are invented", "invented_edges_by_cause")):
        if key in out:
            lines += [f"## {title}", ""]
            if causes := out[key]:
                lines += ["| cause | count |", "|---|---|"]
                lines += [f"| {k} | {v} |" for k, v in causes.items()]
            else:
                lines.append("None.")
            lines.append("")
    if (ceil := out.get("edges_against_achievable_ceiling")) and ceil["kernel_edges"]:
        tot = ceil["kernel_edges"]
        lo, hi = ceil["excluding_notation"], ceil["including_notation"]
        lines += [
            "## Against the achievable ceiling", "",
            f"Of {tot} kernel edges, {ceil['unreachable_from_source_text']} "
            f"({ceil['unreachable_from_source_text'] / tot:.1%}) are unreachable from the "
            f"source text at all, and {ceil['reachable_only_through_notation']} "
            f"({ceil['reachable_only_through_notation'] / tot:.1%}) only through notation.", "",
            "| ceiling | achievable edges | recall | F1 |", "|---|---|---|---|",
            f"| excluding notation-only edges | {lo['achievable_edges']} | {lo['recall']:.3f} "
            f"| {lo['f1']:.3f} |",
            f"| including notation-only edges | {hi['achievable_edges']} | {hi['recall']:.3f} "
            f"| {hi['f1']:.3f} |", "",
        ]
    return "\n".join(lines)


def pooled_report(results: dict[str, dict], skipped: dict[str, str]) -> str:
    """Render the cross-project comparison and the pooled error causes as Markdown."""
    lines = [
        "# Parser vs. Lean 4 kernel - all projects", "",
        "| project | modules | decls (GT) | decl F1 | edges | edge P | edge R | edge F1 "
        "| out-deg ρ |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for repo, res in sorted(results.items()):
        c, n, e = res["corpus"], res["nodes"], res["edges_matched_nodes"]
        lines.append(
            f"| {repo} | {c['modules_analysed']}/{c['modules_in_repo']} "
            f"| {c['kernel_source_declarations_supported_commands']} | {n['f1']:.3f} "
            f"| {e['kernel_edges']} | {e['precision']:.3f} | {e['recall']:.3f} "
            f"| {e['f1']:.3f} | {res['degree_agreement']['out_degree_spearman']:.3f} |")

    def total(*keys: str) -> int:
        return sum(r[keys[0]][keys[1]] for r in results.values())

    etp, efp, efn = (total("edges_matched_nodes", k) for k in ("tp", "fp", "fn"))
    lines += [
        "", "## Pooled totals", "",
        f"- {len(results)} projects, "
        f"{total('corpus', 'kernel_source_declarations_supported_commands')} ground-truth "
        f"declarations, {total('nodes', 'tp')} found by the parser",
        f"- {etp + efn} kernel edges: {etp} found, {efn} missed, {efp} invented",
        f"- pooled edge precision {etp / max(etp + efp, 1):.3f}, "
        f"recall {etp / max(etp + efn, 1):.3f}", "",
    ]
    for title, key in (("Missed edges by cause", "missed_edges_by_cause"),
                       ("Invented edges by cause", "invented_edges_by_cause")):
        pooled: Counter = Counter()
        for r in results.values():
            pooled.update(r.get(key, {}))
        if pooled:
            lines += [f"## {title}", "", "| cause | count |", "|---|---|"]
            lines += [f"| {k} | {v} |" for k, v in pooled.most_common()] + [""]
    unsupported: Counter = Counter()
    for r in results.values():
        unsupported.update(r["unsupported_commands"])
    if unsupported:
        lines += ["## Declarations written with unsupported commands", "",
                  ", ".join(f"`{k}` {v}" for k, v in unsupported.most_common()), ""]
    if skipped:
        lines += ["## Skipped", ""]
        lines += [f"- **{r}**: {why}" for r, why in sorted(skipped.items())] + [""]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def verify(repo_dir: Path, out_root: Path, file_pattern: str, parse_json: Path | None,
           build: bool, skip_extract: bool, memory_mb: int) -> dict:
    """Verify one project; write its results under `out_root` and return them."""
    if not (repo_dir / "lakefile.toml").exists() and not (repo_dir / "lakefile.lean").exists():
        msg = f"not a Lake project: {repo_dir}"
        raise RuntimeError(msg)
    commit = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"], cwd=repo_dir,
        capture_output=True, text=True, check=False).stdout.strip() or "worktree"
    out_dir = out_root / f"{repo_dir.name}_{commit}"
    out_dir.mkdir(parents=True, exist_ok=True)
    dump = out_dir / "kernel_decls.jsonl"

    if build:
        build_project(repo_dir)

    # Both sides are restricted to the modules that compiled; coverage is reported alongside.
    src_mods = source_modules(repo_dir, file_pattern)
    compiled = compiled_modules(repo_dir)
    if not compiled and skip_extract and dump.exists():
        # Re-scoring a saved dump needs no build: it lists the modules that compiled.
        compiled = dumped_modules(dump)
    analysed = src_mods & compiled
    if not analysed:
        msg = f"no compiled modules in {repo_dir}; build it first (--build)"
        raise RuntimeError(msg)
    coverage = len(analysed) / len(src_mods)
    if analysed != src_mods:
        log(f"Partial build: analysing {len(analysed)}/{len(src_mods)} modules ({coverage:.1%})")

    if not skip_extract:
        extract_kernel_dump(repo_dir, dump, analysed, memory_mb)
    if not dump.exists():
        msg = f"no kernel dump at {dump}; drop --skip-extract"
        raise RuntimeError(msg)

    by_kname, cls = load_kernel(dump, repo_dir)
    log(f"Classified {len(by_kname)} kernel constants")

    if parse_json:
        p_decls, p_edges, p_dupes = load_parser_json(parse_json, analysed)
    else:
        p_decls, p_edges, p_dupes = run_parser(repo_dir, file_pattern, analysed)
    res = analyse(repo_dir, by_kname, cls, p_decls, p_edges, p_dupes,
                  attribute_causes=parse_json is None)
    res["corpus"] |= {"modules_analysed": len(analysed), "modules_in_repo": len(src_mods),
                      "module_coverage": coverage}

    (out_dir / "comparison.json").write_text(json.dumps(res, indent=2))
    summary = report(res, repo_dir.name, commit)
    (out_dir / "SUMMARY.md").write_text(summary + "\n")
    print(summary)
    log(f"Wrote {out_dir}/comparison.json and {out_dir}/SUMMARY.md")
    return res


def main(argv: list[str] | None = None) -> int:
    """Verify each project given on the command line, and pool the results."""
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("projects", nargs="+", type=Path, help="Lean project directories.")
    ap.add_argument("-o", "--out-dir", type=Path, default=Path("parser_verification"),
                    help="Where to write results (default: ./parser_verification).")
    ap.add_argument("-p", "--file-pattern", default=DEFAULT_FILE_PATTERN,
                    help="Regex selecting source files by project-relative path.")
    ap.add_argument("--parse-json", type=Path, help="Score this saved parse (from "
                    "`lean-deps --format json`) instead of running the parser. One project "
                    "only; disables per-cause error attribution.")
    ap.add_argument("--build", action="store_true", help="Build each project first.")
    ap.add_argument("--skip-extract", action="store_true",
                    help="Reuse existing kernel dumps instead of running Lean.")
    ap.add_argument("--lean-memory", type=int, default=16384,
                    help="Memory limit for Lean in MB (default: 16384).")
    args = ap.parse_args(argv)
    if args.parse_json and len(args.projects) > 1:
        ap.error("--parse-json takes exactly one project")

    results, skipped = {}, {}
    for project in args.projects:
        repo_dir = project.resolve()
        try:
            results[repo_dir.name] = verify(repo_dir, args.out_dir, args.file_pattern,
                                            args.parse_json, args.build, args.skip_extract,
                                            args.lean_memory)
        except RuntimeError as e:
            log(f"Skipping {repo_dir.name}: {e}")
            skipped[repo_dir.name] = str(e)

    if len(args.projects) > 1:
        pooled = pooled_report(results, skipped)
        (args.out_dir / "POOLED.md").write_text(pooled + "\n")
        (args.out_dir / "pooled.json").write_text(
            json.dumps({"results": results, "skipped": skipped}, indent=2))
        print("\n" + pooled)
        log(f"Wrote {args.out_dir}/POOLED.md")
    return 1 if skipped and not results else 0


if __name__ == "__main__":
    sys.exit(main())
