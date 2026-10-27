"""Parse Lean 4 source files into declarations and resolve the dependencies between them."""

from __future__ import annotations

import logging
import os
import re
from collections import defaultdict
from collections.abc import Iterable
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

from lexical_lean_parser import _lexer as lx
from lexical_lean_parser.model import Comment, Declaration, DepMap, Identifier, Import, Notation

logger = logging.getLogger(__name__)

DEFAULT_FILE_PATTERN = (
    r"^(?!(?:.*/)?(?:\.lake|\.venv|\.git|\.github|\.vscode|[Tt]ests?|scripts?|blueprint"
    r"|bench|attic|docs|deprecated)/)(?!lakefile\.lean$)(?!(?:.*/)?[Tt]ests?\.lean$).*\.lean$"
)
"""Default filter for `find_lean_files`: `.lean` files outside build, test and docs folders."""


@dataclass
class ParsedFile:
    """Everything extracted from a single file, before cross-file resolution."""

    file: Path | None
    imports: list[Import] = field(default_factory=list)
    declarations: list[Declaration] = field(default_factory=list)
    comments: list[Comment] = field(default_factory=list)
    notations: list[Notation] = field(default_factory=list)

    @property
    def items(self) -> list[Identifier]:
        """Imports, declarations and comments, in that order."""
        return [*self.imports, *self.declarations, *self.comments]


# ---------------------------------------------------------------------------
# Single-file extraction
# ---------------------------------------------------------------------------


def find_lean_files(root: Path, file_pattern: str | None = None) -> list[Path]:
    """The Lean files under `root` whose root-relative POSIX path matches `file_pattern`.

    Hidden and symlinked directories are skipped. The result is sorted.
    """
    regex = re.compile(file_pattern or DEFAULT_FILE_PATTERN)
    root = Path(root).resolve()
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        here = Path(dirpath)
        dirnames[:] = [d for d in dirnames
                       if not d.startswith(".") and not (here / d).is_symlink()]
        for name in filenames:
            path = here / name
            if path.is_file() and regex.search(path.relative_to(root).as_posix()):
                files.append(path)
    return sorted(files)


def parse_declarations(
    text: str,
    namespaces: list[tuple[str | None, int, int]],
    starts: list[int] | None = None,
    *,
    code: str | None = None,
    variables: list[tuple[frozenset[str], int, int]] | None = None,
    opens: list[tuple[frozenset[str], int, int]] | None = None,
    scoped_opens: list[tuple[frozenset[str], int, int]] | None = None,
) -> list[Declaration]:
    """Extract the `def`/`theorem`/`structure`/... declarations from preprocessed source.

    Args:
        text: Source with comments and attributes removed.
        namespaces: The output of `namespace_ranges` for `text`.
        starts: Line starts of `text`, to record line numbers; omitted, they are None.
        code: `text` with string contents masked (`mask_strings`), in which declarations are
            searched for; omitted, it is computed. Their text is still read from `text`.
        variables: The output of `variable_ranges` for `text`; omitted, it is computed.
        opens: The output of `open_ranges` for `text`; omitted, it is computed.
        scoped_opens: The output of `scoped_open_ranges` for `text`; omitted, it is computed.

    """
    code = lx.mask_strings(text) if code is None else code
    variables = lx.variable_ranges(code) if variables is None else variables
    variable_types = lx.variable_type_ranges(code)
    opens = lx.open_ranges(code) if opens is None else opens
    scoped_opens = lx.scoped_open_ranges(code) if scoped_opens is None else scoped_opens
    leading = len(code) - len(code.lstrip())
    stripped = text[leading:len(code.rstrip())]
    declarations = []
    for match in lx.DECLARATION.finditer(code.strip()):
        kind = match.group("kind")
        rest = stripped[match.start("rest"):match.end("rest")]
        if (header := lx.split_header(rest)) is None:
            # An anonymous `instance : Foo := ...`. Lean derives its name from the type,
            # which cannot be reproduced here, so it is left out rather than guessed at. A
            # name spliced into a syntax quotation (`def $name`) is not a declaration either.
            if kind != "instance" and not rest.startswith("$"):
                logger.warning("Could not read the name of a `%s` declaration", kind)
            continue
        name, body = header
        if (ix := lx.find_assignment(body)) is not None:
            definition, value = body[:ix], body[ix + 2:]
        elif m := lx.EQUATIONS.search(body):
            # Defined by pattern matching: `theorem foo : P` followed by `| 0 => ...` arms.
            definition, value = body[:m.start()], body[m.start():]
        else:  # a signature only, as for an `axiom` or a `structure`
            definition, value = body, ""
        # `namespaces` holds offsets into `text`, not into `stripped`.
        namespace = lx.namespace_at(match.start() + leading, namespaces)
        # `_root_.Foo.bar` escapes the enclosing namespace: the declaration is `Foo.bar`. Names
        # in it still resolve in the namespaces it is written in.
        opened = lx.names_at(match.start() + leading, opens)
        if name.startswith("_root_."):
            name = name.removeprefix("_root_.")
            if namespace:
                parts = namespace.split(".")
                opened |= {".".join(parts[:i]) for i in range(1, len(parts) + 1)}
            namespace = None
        start_line = end_line = None
        if starts is not None:
            abs_start, abs_end = match.start() + leading, match.end() + leading
            start_line = lx.line_of(abs_start, starts)
            end_line = lx.line_of(max(abs_end - 1, abs_start), starts)
        declarations.append(Declaration(
            kind=kind, name=name, definition=definition.strip(), body=value.strip(),
            namespace=namespace, start_line=start_line, end_line=end_line,
            variables=lx.names_at(match.start() + leading, variables),
            variable_types=lx.names_at(match.start() + leading, variable_types),
            opens=opened,
            scoped_opens=lx.names_at(match.start() + leading, scoped_opens),
        ))
    return declarations


def parse_aliases(
    text: str,
    namespaces: list[tuple[str | None, int, int]],
    starts: list[int] | None = None,
) -> list[Declaration]:
    """Extract `alias` declarations, which introduce real declarations under a new name."""
    aliases = []
    for match in lx.ALIAS.finditer(text):
        target = match.group("target")
        # `alias ⟨_, foo⟩ := bar` names one declaration per non-placeholder component.
        if target.startswith("⟨"):
            names = [n for n in lx.TOKENIZER.findall(target) if n != "_"]
        else:
            names = [target]
        namespace = lx.namespace_at(match.start(), namespaces)
        line = lx.line_of(match.start(), starts) if starts is not None else None
        for name in names:
            aliases.append(Declaration(
                kind="alias",
                name=name.removeprefix("_root_."),
                definition="",
                body=match.group("rhs").strip(),
                namespace=None if name.startswith("_root_.") else namespace,
                start_line=line,
                end_line=line,
            ))
    return aliases


def parse_notations(
    text: str,
    file: Path | None = None,
    namespaces: list[tuple[str | None, int, int]] | None = None,
) -> list[Notation]:
    """Extract the single-line notation commands of a file."""
    notations = []
    for match in lx.NOTATION.finditer(text):
        lhs, sep, rhs = match.group("rest").partition("=>")
        if not sep or not rhs.strip():
            continue  # multi-line notation, or a `syntax`-style declaration with no target
        literals = [lit.strip() for lit in lx.STRING_LITERAL.findall(lhs) if lit.strip()]
        if not literals or all(lx.BUILTIN_SHAPE.fullmatch(lit) for lit in literals):
            continue
        # Whatever is left of the left-hand side once the quoted fragments are removed names
        # the notation's parameters.
        params = tuple(lx.TOKENIZER.findall(
            lx.NOTATION_OPTION.sub(" ", lx.STRING_LITERAL.sub(" ", lhs))))
        namespace = lx.namespace_at(match.start(), namespaces) if namespaces else None
        scope = (match.group("scoped_ns") or namespace) if match.group("scoped") else None
        notations.append(Notation(literals=literals, rhs=rhs.strip(), file=file,
                                  is_local=bool(match.group("local")), params=params,
                                  namespace=namespace, scope=scope))
    return notations


def local_binder_names(text: str) -> set[str]:
    """Names bound locally within a declaration, which never refer to a global constant."""
    names: set[str] = set()
    for pattern in lx.BINDERS:
        for match in pattern.finditer(text):
            names.update(lx.binder_names(match.group("names")))
    # Only ever drop unqualified names: `h.trans` still refers to something global.
    return {name for name in names if "." not in name}


def _count_todos(declarations: list[Declaration], comments: list[Comment]) -> None:
    """Attach to each declaration the TODO comments inside it or ending right above it."""
    todos = [c for c in comments if "todo" in c.text.lower()]
    for d in declarations:
        if d.start_line is None or d.end_line is None:
            continue
        d.n_todos = sum(
            1 for c in todos
            if c.end_line == d.start_line - 1
            or (c.start_line >= d.start_line and c.end_line <= d.end_line)
        )


def parse_text(text: str, file: Path | None = None) -> ParsedFile:
    """Extract imports, declarations, comments and notations from one file's source.

    Dependencies are not resolved here: that needs every file, see `parse_dependencies`.
    Line numbers refer to the original `text`.
    """
    text = text.replace("\r\n", "\n")
    starts = lx.line_starts(text)
    spans = lx.comment_spans(text)
    comments = [
        Comment(text=text[s:e], file=file, start_line=lx.line_of(s, starts),
                end_line=lx.line_of(max(e - 1, s), starts))
        for s, e in spans
    ]
    # Blank out comments, attributes and Verso markup but keep newlines, so line numbers
    # stay correct.
    text = lx.blank_spans(text, spans)
    if doc := lx.VERSO_DOC.search(text):
        text = lx.blank_spans(text, [(doc.start(), len(text))])
    text = lx.blank_spans(text, lx.attribute_spans(text))
    # Commands are searched for in `code`, where keywords inside strings are masked;
    # notations are read from `text`, since they are written as strings.
    code = lx.mask_strings(text)
    namespaces = lx.namespace_ranges(code)
    starts = lx.line_starts(text)
    notations = parse_notations(text, file, namespaces)
    imports = [Import(kind, name, file=file) for kind, name in lx.IMPORT.findall(code) if name]
    declarations = parse_declarations(text, namespaces, starts, code=code) + parse_aliases(
        code, namespaces, starts)
    for d in declarations:
        d.file = file
        if not d.body and not d.definition:
            logger.warning("Empty declaration %s %s in %s", d.kind, d.name, file)
    _count_todos(declarations, comments)
    return ParsedFile(file, imports, declarations, comments, notations)


def parse_file(path: Path) -> ParsedFile:
    """`parse_text` applied to the contents of `path`."""
    path = Path(path)
    # `utf-8-sig` drops a byte-order mark, which would otherwise hide a first-line import.
    return parse_text(path.read_text(encoding="utf-8-sig", errors="ignore"), path)


# ---------------------------------------------------------------------------
# Cross-file resolution
# ---------------------------------------------------------------------------


def resolve_notation_targets(notations: list[Notation], targets: list[set] | None = None,
                             ) -> list[set]:
    """For each notation, everything it ultimately expands to.

    Right-hand sides are routinely written in terms of other notation
    (``local notation3 "k" => d[X₁ # X₂]``), so expansion is iterated to a fixed point. The
    loop is bounded by the number of notations, which also makes it safe against cycles.

    Args:
        notations: The notations.
        targets: What each notation refers to directly; by default its `target_tokens`.

    """
    targets = [set(t) for t in targets] if targets is not None \
        else [n.target_tokens() for n in notations]
    uses = [
        [j for j, other in enumerate(notations)
         if j != i and other.applies_to(n.file) and other.appears_in(n.rhs)]
        for i, n in enumerate(notations)
    ]
    for _ in range(len(notations)):
        changed = False
        for i, referenced in enumerate(uses):
            for j in referenced:
                if not targets[j] <= targets[i]:
                    targets[i] |= targets[j]
                    changed = True
        if not changed:
            break
    return targets


def import_closure(root: Path, parsed: list[ParsedFile]) -> dict[Path, set[Path]]:
    """For each parsed file, the parsed files it imports, directly or transitively.

    Modules are matched to files by path relative to `root`, or by any trailing part of it,
    so that a source directory (`src/Foo/Bar.lean` imported as `Foo.Bar`) needs no
    configuration. Files under `root` that were not parsed still pass their imports on.
    """
    root = Path(root).resolve()
    keys = {Path(p.file).resolve(): p.file for p in parsed if p.file is not None}
    imports = {path: [i.name for i in p.imports]
               for p in parsed if p.file is not None for path in [Path(p.file).resolve()]}
    for path in find_lean_files(root, r"\.lean$"):
        if path not in imports:
            text = path.read_text(encoding="utf-8-sig", errors="ignore")
            imports[path] = [m.group("name") for m in lx.IMPORT.finditer(text)]
    by_module: dict[str, list[Path]] = defaultdict(list)
    for path in imports:
        parts = (path.relative_to(root) if path.is_relative_to(root) else path).with_suffix("")
        parts = parts.parts
        for i in range(len(parts)):
            by_module[".".join(parts[i:])].append(path)

    closure: dict[Path, set[Path]] = {}
    for start, key in keys.items():
        seen: set[Path] = set()
        stack = [start]
        while stack:
            for module in imports.get(stack.pop(), ()):
                for path in by_module.get(module, ()):
                    if path not in seen:
                        seen.add(path)
                        stack.append(path)
        closure[key] = {keys[path] for path in seen if path in keys}
    return closure


class _Resolver:
    """Resolves the names written in a declaration to the declarations they refer to."""

    def __init__(self, declarations: Iterable[Declaration], notations: list[Notation],
                 imported: dict[Path, set[Path]] | None = None) -> None:
        # What each file imports (see `import_closure`). A name can only refer to a
        # declaration in its own file or in one it imports; files not in it see everything.
        self.imported = imported or {}
        # Index declarations by full name, by name as written, and by every dotted suffix of
        # the full name: `lemma baz` inside `namespace Foo.Bar` can be referred to as
        # `Foo.Bar.baz`, `Bar.baz` or `baz` depending on where the reference is.
        self.full: dict[str, list[Declaration]] = defaultdict(list)
        self.written: dict[str, list[Declaration]] = defaultdict(list)
        self.suffix: dict[str, list[Declaration]] = defaultdict(list)
        self.namespaces: set[str] = set()  # every namespace that holds a declaration
        self._opened: dict[tuple, list[str]] = {}
        for d in declarations:
            self.full[d.full_name].append(d)
            prefix = d.full_name.split(".")[:-1]
            self.namespaces.update(".".join(prefix[:i]) for i in range(1, len(prefix) + 1))
            self.written[d.name].append(d)
            parts = d.full_name.split(".")
            for i in range(1, len(parts)):
                self.suffix[".".join(parts[i:])].append(d)
        # A notation's right-hand side is resolved where the notation is declared, not where
        # it is used: `H[X]` means `ProbabilityTheory.entropy` even outside that namespace.
        direct = []
        for n in notations:
            site = Declaration("notation", "_", "", "", namespace=n.namespace, file=n.file)
            direct.append({
                target for token in n.target_tokens()
                for target in self.disambiguate(self.lookup(token, site, set(n.params)), site)
            })
        self.notations = list(zip(notations, resolve_notation_targets(notations, direct),
                                  strict=True))

    def lookup(self, token: str, decl: Declaration, local: set[str]) -> list[Declaration]:
        """Candidates for `token`, resolved the way Lean resolves names.

        A dotted token that names nothing is retried without its last component, since
        `foo.mp` and `foo.symm` are field notation on `foo` - unless what is left is one of
        the `local` names, as in `h.trans`.
        """
        while not (hits := self._lookup(token, decl)) and "." in token:
            token = token.rpartition(".")[0]
            if token in local:
                break
        return hits

    def lookup_scoped(self, token: str, decl: Declaration) -> list[Declaration]:
        """Candidates for `token` in the namespaces enclosing `decl`, innermost first.

        A declaration named `Foo.bar` has namespace `Foo` open in its own body, as in Lean.
        """
        parts = decl.full_name.split(".")[:-1]
        for i in range(len(parts), 0, -1):
            if hits := self.visible(self.full.get(".".join(parts[:i]) + "." + token), decl):
                return hits
        return []

    def opened(self, decl: Declaration) -> list[str]:
        """The project namespaces opened where `decl` is.

        As in Lean, `open Foo` opens every existing `Foo` it can name: relative to the
        enclosing namespaces (`Bar.Foo` inside `namespace Bar`) and to the other opened ones
        (`open SymCC Factory` opens `SymCC.Factory`).
        """
        key = (decl.opens, decl.full_name.rpartition(".")[0])
        if (cached := self._opened.get(key)) is not None:
            return cached
        parts = key[1].split(".") if key[1] else []
        bases = [".".join(parts[:i]) for i in range(len(parts), 0, -1)]
        found = [ns for ns in sorted(decl.opens) if ns in self.namespaces]
        for base in bases:
            found += [f"{base}.{ns}" for ns in sorted(decl.opens)
                      if f"{base}.{ns}" in self.namespaces]
        for _ in range(2):  # an `open` may name a namespace inside another opened one
            found += [f"{base}.{ns}" for base in found for ns in sorted(decl.opens)
                      if f"{base}.{ns}" in self.namespaces]
        self._opened[key] = result = list(dict.fromkeys(found))
        return result

    def lookup_opened(self, token: str, decl: Declaration) -> list[Declaration]:
        """Candidates for `token` in the namespaces opened where `decl` is."""
        hits = [h for ns in self.opened(decl) for h in self.full.get(f"{ns}.{token}", ())]
        return self.visible(list(dict.fromkeys(hits)), decl)

    def _lookup(self, token: str, decl: Declaration) -> list[Declaration]:
        if hits := self.lookup_scoped(token, decl):
            return hits
        # Top-level and opened names compete, as in Lean; `disambiguate` settles any tie.
        if hits := list(dict.fromkeys(self.visible(self.full.get(token), decl)
                                      + self.lookup_opened(token, decl))):
            return hits
        # Only a dotted reference may match a proper suffix of a longer full name; letting
        # bare names do so would resolve `map` to every `Foo.map` in the repository.
        return self.visible(self.suffix.get(token), decl) if "." in token else []

    def sees(self, decl: Declaration, file: Path | None) -> bool:
        """Whether something declared in `file` is in scope in `decl`'s file."""
        if file is None or file == decl.file or decl.file not in self.imported:
            return True
        return file in self.imported[decl.file]

    def visible(self, hits: list[Declaration] | None, decl: Declaration) -> list[Declaration]:
        """The `hits` that are in scope in `decl`'s file."""
        return [h for h in hits or () if self.sees(decl, h.file)]

    @staticmethod
    def disambiguate(hits: list[Declaration], decl: Declaration) -> list[Declaration]:
        """Narrow an ambiguous reference by proximity.

        Lean resolves every reference to exactly one constant, so emitting all candidates
        would guarantee wrong edges. Prefer the same file, then the same namespace, and drop
        the reference when neither singles one out.
        """
        if len(hits) <= 1:
            return hits
        if len(same_file := [h for h in hits if h.file == decl.file]) == 1:
            return same_file
        if len(same_ns := [h for h in hits if h.namespace == decl.namespace]) == 1:
            return same_ns
        return []

    @staticmethod
    def scope_open(scope: str | None, decl: Declaration) -> bool:
        """Whether the scoped notation of namespace `scope` is active in `decl`.

        It is when `scope` encloses `decl` or is opened, by `open` or `open scoped`, under
        any of the names it can be opened by (`open B` for `A.B` inside `namespace A`).
        """
        if scope is None:
            return True
        enclosing = decl.full_name.rpartition(".")[0]
        if f"{enclosing}.".startswith(f"{scope}."):
            return True
        return any(scope == ns or scope.endswith(f".{ns}")
                   for ns in decl.opens | decl.scoped_opens)

    def notation_targets(self, text: str, decl: Declaration) -> set[Declaration]:
        """The declarations that the notation used in `text` stands for."""
        # `ρ[X # A]` names neither `rho` nor `condRho`, but depends on both.
        active = [
            (notation, targets) for notation, targets in self.notations
            if notation.applies_to(decl.file) and self.sees(decl, notation.file)
            and self.scope_open(notation.scope, decl) and notation.marker in text
        ]
        # Lean's tokenizer reads the longest token it knows, so where `∗` and `∗ₙ` are both
        # notation, the `∗` at the start of `∗ₙ` is not a use of `∗`.
        literals = {lit for notation, _ in active for lit in notation.literals}

        def longest(m: re.Match) -> bool:
            return not any(
                len(other) > len(lit) and text.startswith(other, m.start(i))
                for i, lit in enumerate(m.groups(), 1) for other in literals
            )

        uses = [
            (m.start(), m.end(), len(notation.literals), targets)
            for notation, targets in active
            for m in notation.usage.finditer(text) if longest(m)
        ]
        # Where several notations match the same text, as `I[X : Y | Z]` matches both itself
        # and `I[X : Y]`, Lean reads it as the most specific one: the one with more fragments.
        found: set[Declaration] = set()
        for start, end, n, targets in uses:
            if not any(s <= start and end <= e and n < m for s, e, m, _ in uses):
                found |= targets
        return found

    def resolve(self, decl: Declaration, skip_self_refs: bool) -> None:
        """Fill in the `depends_on*` fields of `decl`."""
        # Both halves matter: for `lemma foo ... : Statement := by tac` the statement is in
        # `definition` and only the proof is in `body`. They are resolved separately so that
        # each dependency records which half it came from.
        excluded = (lx.IGNORED_TOKENS | set(decl.arguments) | decl.variables
                    | local_binder_names(f"{decl.definition}\n{decl.body}"))
        # Field notation on an argument resolves in the namespace of its type, as in Lean:
        # with `(g : Goal)`, `g.priority` is `Goal.priority`. Only for types written as a
        # capitalised name, so that hypotheses like `(h : a ≤ b)` are left alone.
        typed = dict(entry.split(":", 1) for entry in decl.variable_types)
        typed |= {name: m.group() for name, ty in decl.arguments.items()
                  if (m := lx.TOKENIZER.match(ty.strip())) and m.group()[0].isupper()}
        typed = {name: head for name, head in typed.items() if head not in excluded}

        def resolve_all(text: str) -> list[Declaration]:
            text = lx.mask_strings(text, keep_interpolations=True)
            text = lx.FIELD_ASSIGNMENT.sub(r"\g<pre>", lx.TACTIC_CALL.sub(r"\g<pre>", text))
            if decl.kind in ("structure", "class"):
                text = lx.FIELD_DECLARATION.sub("", text)
            candidates = [
                target
                for token in sorted(set(lx.TOKENIZER.findall(text)) - excluded)
                for target in self.disambiguate(self.lookup(token, decl, excluded), decl)
            ]
            candidates += [
                target
                for token in sorted(set(lx.TOKENIZER.findall(text)))
                if (root := token.partition(".")[0]) in typed and "." in token
                for target in self.disambiguate(self.lookup(
                    f"{typed[root]}.{token.partition('.')[2]}", decl, excluded), decl)
            ]
            # `(f x).sum` inside `namespace Series` most likely means `Series.sum`.
            candidates += [
                target
                for token in sorted(set(lx.FIELD_TOKENIZER.findall(text)) - excluded)
                for target in self.disambiguate(self.lookup_scoped(token, decl), decl)
            ]
            candidates += sorted(self.notation_targets(text, decl), key=lambda d: d.full_name)
            found: list[Declaration] = []
            seen: set[Declaration] = set()
            for target in candidates:
                is_self = target is decl or target.full_name == decl.full_name
                if (skip_self_refs and is_self) or target in seen:
                    continue
                seen.add(target)
                found.append(target)
            return found

        decl.depends_on_def = resolve_all(decl.definition)
        decl.depends_on_body = resolve_all(decl.body)
        decl.depends_on = list(dict.fromkeys(decl.depends_on_def + decl.depends_on_body))


def parse_dependencies(
    root: Path,
    file_pattern: str | None = None,
    skip_self_refs: bool = True,
    files: Iterable[Path] | None = None,
) -> DepMap:
    """Parse a Lean project and resolve the dependencies between its declarations.

    Args:
        root: The project directory.
        file_pattern: Regex selecting files by their root-relative POSIX path; defaults to
            `DEFAULT_FILE_PATTERN`. Ignored when `files` is given.
        skip_self_refs: Drop references from a declaration to itself.
        files: Parse exactly these files instead of searching `root`.

    Returns:
        Every parsed file mapped to its imports, declarations and comments, with each
        declaration's `depends_on`, `depends_on_def` and `depends_on_body` filled in.

    """
    paths = list(files) if files is not None else find_lean_files(root, file_pattern)
    with ThreadPoolExecutor() as ex:
        parsed = list(ex.map(parse_file, paths))

    resolver = _Resolver(
        (d for p in parsed for d in p.declarations),
        [n for p in parsed for n in p.notations],
        import_closure(root, parsed),
    )
    for p in parsed:
        for decl in p.declarations:
            resolver.resolve(decl, skip_self_refs)
    return {p.file: p.items for p in parsed}
