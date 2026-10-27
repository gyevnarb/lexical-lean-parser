# Changelog

## 0.1.0 (unreleased)

First standalone release, extracted from the `lean-completion` research project.

- Zero runtime dependencies; graph building (`[graph]`) and drawing (`[draw]`) are optional.
- `lean-deps` command-line tool; `parse_commit` / `checkout` parse any git revision via
  `git archive`, without touching the working tree.
- `validation/verify.py` scores the parser against the Lean 4 kernel; see
  [VALIDATION.md](VALIDATION.md) for results on nineteen projects.

Parser fixes, each with a regression test:

- **Declarations:** correct namespaces, start lines and names (`theorem foo: P`, `def foo.{u}`,
  `instance (priority := n) foo`); nested block comments, strings (multi-line, raw,
  interpolated) and Verso `#doc` blocks no longer produce declarations; adjacent commands
  (`open ... in`, `attribute`, `mutual` bodies) are no longer swallowed.
- **Name resolution follows Lean's scoping:** names resolve only within the file and its
  transitive imports, through the enclosing namespaces, `open` (including relative opens and
  `open scoped`) and the top level. `variable` binders, local binders (`obtain`, `let x ← ...`),
  field names, named arguments, leading-dot names and name literals are not references.
- **Field notation:** `foo.mp` resolves to `foo`, and `g.priority` resolves through the type of
  `g` when it is an argument or `variable`.
- **Identifiers** use Lean's character classes (`find?`, `𝒥₂`).
- **Notation** resolves where it is declared, matches the most specific and longest token
  (`∗ₙ` is not also `∗`), and respects `scoped` / `scoped[NS]`.
- **Files:** byte-order marks, CRLF line endings and `public import` are handled.
