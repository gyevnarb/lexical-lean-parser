# lexical-lean-parser

A fast, dependency-free parser that extracts the declarations of a Lean 4 project and the
dependency graph between them, straight from the source text.

It reads `.lean` files with regular expressions rather than elaborating them, so it needs no
Lean toolchain, no `lake build` and no Mathlib cache, and parses a project of a few hundred
files in under a second. That makes it practical to parse every commit of a repository's
history.

The price is approximation: dependencies the elaborator inserts without a name in the
source (instance synthesis, coercions, `variable` binders) are invisible to it. Use the
[validation script](#validation) to measure how close it gets on your project.

## Installation

```bash
pip install lexical-lean-parser            # core: no dependencies
pip install "lexical-lean-parser[graph]"   # + networkx dependency graphs
pip install "lexical-lean-parser[draw]"    # + Graphviz rendering (needs Graphviz installed)
```

Requires Python 3.10+.

## Command line

```bash
lean-deps path/to/project                     # JSON: file -> declarations -> depends_on
lean-deps path/to/project -f text             # readable outline
lean-deps path/to/project --commit v1.0 -o deps.json   # any git revision
```

See `lean-deps --help` for file filtering, imports, and verbose output (source text and line
numbers).

## Python

```python
from pathlib import Path
from lexical_lean_parser import parse_dependencies, build_dependency_graph

root = Path("path/to/project")
deps = parse_dependencies(root)          # {file: [Import | Declaration | Comment, ...]}

for items in deps.values():
    for d in items:
        if hasattr(d, "depends_on"):
            print(d.kind, d.full_name, "->", [t.full_name for t in d.depends_on])

G = build_dependency_graph(deps, root)   # networkx.DiGraph (needs the `graph` extra)
```

Each `Declaration` records its `kind`, `name`, `namespace`, `definition` (signature),
`body`, `file`, `start_line`/`end_line`, the number of TODO comments in or above it
(`n_todos`), and its dependencies, split by where the reference occurs: `depends_on_def`
(signature), `depends_on_body` (proof or term), and their union `depends_on`.

Other entry points: `parse_text` / `parse_file` for single files (no cross-file resolution),
`parse_commit` / `build_graph_at_commit` for git revisions, `deps_to_dict` / `deps_to_str`
for serialisation, and `draw_dependency_graph` for DOT/PDF output.

## What it understands

- `def`, `theorem`, `lemma`, `abbrev`, `structure`, `class`, `axiom`, named `instance`s,
  and `alias` (including `alias ⟨_, foo⟩ := bar`).
- `namespace` / `section` / `end` scoping, including dotted namespaces and `_root_.` names,
  nested comments, and strings (keywords inside them are ignored).
- Name resolution the way Lean does it: only declarations in the same file or a
  (transitively) imported one, innermost namespace outwards (including the declaration's
  own `Foo.` prefix), then `open`ed namespaces and the top level; qualified suffixes, field
  notation (`foo.mp`), and ambiguous names disambiguated by file and namespace (or dropped,
  never guessed).
- Local binders (`have`, `intro`, `obtain`, `fun`, `∀`, signature arguments, `variable`),
  structure fields, named arguments, leading-dot names (`.ok x`), string literals and tactic
  invocations (`ext`) are not mistaken for references to global constants.
- Single-line `notation`/`notation3`/`infix`/... commands are expanded, so `ρ[X # A]`
  depends on whatever `ρ[` stands for. Each is resolved where it is declared, and
  overlapping notations are told apart by the most specific match.

By default, files under `.lake`, tests, scripts, docs, `blueprint/` and similar folders are
skipped (`DEFAULT_FILE_PATTERN`); pass your own regex to change that. Anonymous instances,
`inductive`, `macro`/`syntax`/`elab`, multi-line notations, and notation written only with
brackets and commas (indistinguishable from `⟨a, b⟩`) are not handled.

## Accuracy

Checked against the Lean 4 kernel on nineteen public projects, from PFR, Carleson and FLT to
Batteries and Cedar. The parser finds 98–100% of declarations, and 92–100% of the
dependencies it reports are real ones. Its recall is 0.42–1.00, depending on how many
dependencies the elaborator inserts without their names appearing in the source. See
[VALIDATION.md](VALIDATION.md) for the full results, where the errors come from, and how to
reproduce them.

## Validation

`validation/verify.py` compares the parser's output with the ground truth held by the Lean 4
kernel: it dumps every constant of a built project with its dependencies (via
`validation/lean_kernel_deps.lean`), and reports precision/recall for declarations and edges,
plus a breakdown of *why* each wrong edge happened. It needs a Lean toolchain and works from a
source checkout:

```bash
git clone https://github.com/gyevnarb/lexical-lean-parser && cd lexical-lean-parser
uv run python validation/verify.py --build validation/example     # small self-contained demo
uv run python validation/verify.py --build path/to/pfr path/to/flt # several projects, pooled
```

Results are written to `./parser_verification/`.

## Development

```bash
uv run pytest
uv run ruff check .
```

## License

MIT
