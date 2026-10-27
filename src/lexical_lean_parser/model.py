"""The objects a parse produces: declarations, imports, comments and notations."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from functools import cached_property
from pathlib import Path

from lexical_lean_parser._lexer import TOKENIZER, bracket_groups, first_top_level_colon


@dataclass(eq=False)
class Declaration:
    """A named Lean declaration such as a `theorem`, `def` or `structure`.

    Attributes:
        kind: The declaring keyword (`theorem`, `def`, `alias`, ...).
        name: The name as written after the keyword, without the enclosing namespace.
        definition: The signature: binders and type (for a theorem, its statement).
        body: The text after `:=`: the proof or definitional term.
        namespace: The enclosing namespace, or None at the top level.
        start_line: First line of the declaration (1-indexed).
        end_line: Last line of the declaration (1-indexed).
        file: The file the declaration was found in.
        n_todos: The number of TODO comments in or directly above the declaration.
        variables: Names bound by `variable` commands in scope, which are local to it.
        variable_types: For those whose type is a capitalised name, `name:Head`
            (``l:List`` for ``variable {l : List α}``), to resolve field notation `l.foo`.
        opens: Namespaces opened by `open` commands in scope.
        scoped_opens: Namespaces opened by `open scoped`, which activates only their notation.
        depends_on: Every declaration this one refers to; the union of the two below.
        depends_on_def: Dependencies referred to in the signature.
        depends_on_body: Dependencies referred to in the body.

    Two declarations are equal when their kind, namespace, name and definition are.

    """

    kind: str
    name: str
    definition: str
    body: str
    namespace: str | None = None
    start_line: int | None = None
    end_line: int | None = None
    file: Path | None = None
    n_todos: int = 0
    variables: frozenset[str] = field(default=frozenset(), repr=False)
    variable_types: frozenset[str] = field(default=frozenset(), repr=False)
    opens: frozenset[str] = field(default=frozenset(), repr=False)
    scoped_opens: frozenset[str] = field(default=frozenset(), repr=False)
    depends_on: list[Declaration] = field(default_factory=list, repr=False)
    depends_on_def: list[Declaration] = field(default_factory=list, repr=False)
    depends_on_body: list[Declaration] = field(default_factory=list, repr=False)

    @property
    def full_name(self) -> str:
        """The fully qualified name, including the namespace."""
        return f"{self.namespace}.{self.name}" if self.namespace else self.name

    @property
    def arguments(self) -> dict[str, str]:
        """Binder names in the signature, mapped to their types.

        For example ``(x y : ℕ) {f : α → β}`` gives ``{"x": "ℕ", "y": "ℕ", "f": "α → β"}``.
        """
        if not self.definition:
            return {}
        binders = self.definition[: first_top_level_colon(self.definition)].strip()
        arguments = {}
        for group in bracket_groups(binders):
            parts = group.inner.split(":")
            if len(parts) == 2:
                for name in TOKENIZER.findall(parts[0]):
                    arguments[name.strip()] = parts[1].strip()
        return arguments

    def to_dict(self, verbose: bool = False) -> dict:
        """A JSON-serialisable representation; `verbose` adds the source text and file."""
        out = {
            "kind": self.kind,
            "namespace": self.namespace,
            "name": self.name,
            "n_todos": self.n_todos,
            "depends_on": [
                {"kind": dep.kind, "namespace": dep.namespace, "name": dep.name}
                for dep in self.depends_on
            ],
        }
        if verbose:
            out["body"] = self.body
            out["definition"] = self.definition
            out["file"] = str(self.file) if self.file else None
            out["start_line"] = self.start_line
            out["end_line"] = self.end_line
        return out

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Declaration):
            return NotImplemented
        return self._key() == other._key()

    def __hash__(self) -> int:
        return hash(self._key())

    def _key(self) -> tuple:
        return (self.kind, self.namespace, self.name, self.definition)


@dataclass(eq=False)
class Import:
    """An `import` command. Two imports are equal when their names are."""

    kind: str
    name: str
    namespace: str | None = None
    file: Path | None = None

    @property
    def full_name(self) -> str:
        """The imported module name."""
        return self.name

    def to_dict(self, verbose: bool = False) -> dict:  # noqa: ARG002
        """A JSON-serialisable representation."""
        return {
            "kind": self.kind,
            "name": self.name,
            "namespace": self.namespace,
            "file": str(self.file) if self.file else None,
        }

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Import):
            return NotImplemented
        return (self.kind, self.name) == (other.kind, other.name)

    def __hash__(self) -> int:
        return hash((self.kind, self.name))


@dataclass
class Comment:
    """A line or block comment, with the lines it spans (1-indexed)."""

    text: str
    file: Path | None = None
    start_line: int | None = None
    end_line: int | None = None


@dataclass
class Notation:
    """A notation command: the literal fragments it is written with, and what it means.

    Attributes:
        literals: The quoted fragments of the left-hand side, e.g. ``["ρ[", " # ", "]"]``.
        rhs: The right-hand side source text, e.g. ``"rho X A volume"``.
        file: The file it was declared in.
        is_local: Whether it was declared `local`, and so applies to that file only.
        params: The parameters bound by the left-hand side, e.g. ``("X", "A")``.
        namespace: The namespace it was declared in, where its right-hand side is resolved.
        scope: For a `scoped` notation, its namespace: it applies only where that namespace
            is open (or encloses the use).

    """

    literals: list[str]
    rhs: str
    file: Path | None = None
    is_local: bool = False
    params: tuple[str, ...] = ()
    namespace: str | None = None
    scope: str | None = None

    @property
    def marker(self) -> str:
        """The most distinctive literal fragment, used as a cheap pre-filter."""
        return max(self.literals, key=len)

    @cached_property
    def usage(self) -> re.Pattern:
        """Matches a use of this notation: its literal fragments, in order, on one line.

        Each fragment is a group, so that the caller can tell where each one starts.

        The arguments between fragments may not contain the closing fragment, so that a use
        of `d[X # Y]` is not taken for a use of `d[X # Y | W]` that runs on past its `]`.
        """
        last = re.escape(self.literals[-1])
        gap = rf"(?:(?!{last})[^\n])*?" if len(self.literals) > 1 else ""
        body = gap.join(f"({re.escape(lit)})" for lit in self.literals)
        if re.fullmatch(r"[\w']+", self.literals[0]):
            # A purely alphanumeric opener (`k`, `U`) must not match inside another word.
            body = rf"(?<![\w'.]){body}"
        if re.fullmatch(r"[\w']+", self.literals[-1]):
            body = rf"{body}(?![\w'])"
        return re.compile(body)

    def appears_in(self, text: str) -> bool:
        """Whether this notation is used in `text`.

        Matching the whole fragment sequence rather than a single marker is what keeps
        overlapping notations apart: `ρ[X # A]` means `rho`, `ρ[X | Z # A]` means `condRho`,
        and they share their first fragment.
        """
        return self.marker in text and self.usage.search(text) is not None

    def target_tokens(self) -> set[str]:
        """Tokens on the right-hand side that could name a constant.

        The notation's own parameters are bound by the left-hand side and name nothing
        global, so ``"ρ[" X " # " A "]" => rho X A volume`` contributes `rho` and `volume`,
        not `X` and `A`.
        """
        return set(TOKENIZER.findall(self.rhs)) - set(self.params)

    def applies_to(self, file: Path | None) -> bool:
        """Whether this notation can be in scope in `file` (see also `scope`)."""
        return not self.is_local or self.file == file


Identifier = Declaration | Import | Comment
DepMap = dict[Path, list[Identifier]]
"""Parse result: every file mapped to the imports, declarations and comments found in it."""
