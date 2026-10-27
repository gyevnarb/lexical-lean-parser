"""Regular expressions and small text utilities shared by the parser."""

from __future__ import annotations

import bisect
import re
from collections.abc import Callable
from dataclasses import dataclass

# ---------------------------------------------------------------------------
# Declarations
# ---------------------------------------------------------------------------

DECLARATION_KINDS = ("def", "theorem", "lemma", "axiom", "structure", "class", "abbrev",
                     "instance")
_HEADER_KINDS = "|".join(DECLARATION_KINDS)
_MODIFIERS = "private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public|meta"
# Commands that, written at the start of a line, cannot continue the previous declaration.
_COMMANDS = (
    f"{_HEADER_KINDS}|{_MODIFIERS}|universe|inductive|example|alias|namespace|end|section"
    "|open|variable|omit|include|notation3|notation|infixl|infixr|infix|prefix|postfix"
    "|macro_rules|macro|syntax|elab_rules|elab|attribute|set_option|export|mutual|deriving"
    "|initialize|opaque|irreducible_def|add_decl_doc|suppress_compilation"
)
# A declaration runs from its keyword to the first of: blank line(s) followed by an
# unindented line, a line starting with a command keyword or a `#command`, a line starting
# with a declaration keyword at any indentation (for projects that indent inside a
# namespace), or the end of the text. `rest` holds the name, signature and body, which
# `split_header` separates.
DECLARATION = re.compile(
    rf"(?<!\S)(?<!\bderiving\s)(?P<kind>{_HEADER_KINDS})\s+"
    r"(?P<rest>[\s\S]*?)"
    rf"(?=\n(?:[ \t]*\n)+\S|\n(?:{_COMMANDS})\b|\n#"
    rf"|\n[ \t]+(?:(?:{_MODIFIERS})\s+)*(?:{_HEADER_KINDS})\s|\Z)"
)

# The declaration name: dotted, each component plain or «guillemet-quoted», optionally
# followed by universe parameters `.{u, v}`, which are not part of the name. A plain
# component cannot start with a digit or ASCII punctuation other than `_`, which rules out
# prose (`structure - ...`) and antiquotations (`def $name`).
_NAME_PART = r"(?:«[^»\n]*»|(?![\d!-/:-@\[-^`{-~])[^\s:(){}\[\]⦃⦄⟨⟩«»,.]+)"
DECLARATION_NAME = re.compile(rf"(?P<name>{_NAME_PART}(?:\.{_NAME_PART})*)(?:\.\{{[^}}\n]*\}})?")
# Written between the keyword and the name: `class inductive Foo`, `instance (priority := 10)`.
_PRE_NAME = re.compile(r"(?:(?:inductive|abbrev)\s+|\(\s*priority\s*:=[^)]*\)\s*)")

# `alias foo := bar` and `alias ⟨_, foo⟩ := bar`. Parsed separately from the other
# declarations because the name is not simply the token after the keyword.
ALIAS = re.compile(
    r"^[ \t]*(?:(?:protected|private|scoped|local)\s+)*alias\s+"
    r"(?P<target>⟨[^⟩\n]*⟩|[^\s:=]+)\s*:=\s*(?P<rhs>.*)$",
    re.MULTILINE,
)

# The first pattern-matching arm of a declaration written with equations (`| 0 => ...`).
EQUATIONS = re.compile(r"\n[ \t]*\|")

IMPORT = re.compile(
    r"^(?:(?:public|private|meta)[ \t]+)*(import)[ \t]+(?:all[ \t]+)?(?P<name>[^\s]*)[ \t]*$",
    re.MULTILINE,
)
# A Verso document (`#doc (Manual) "Title" =>`): the rest of the file is markup, not Lean.
VERSO_DOC = re.compile(r"^#doc\b", re.MULTILINE)

# ---------------------------------------------------------------------------
# Identifiers
# ---------------------------------------------------------------------------

# Identifier characters, exactly as Lean defines them (`isIdFirst` / `isIdRest` in
# `Init/Meta/Defs.lean`): ASCII and Latin-1 letters, Greek except λ, Π and Σ, Coptic, the
# letterlike block (ℝ, ℭ) and mathematical alphanumerics (𝒥, 𝔓); after the first character
# also digits, `'`, `!`, `?` and subscripts.
_ID_FIRST = (
    "A-Za-z_\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f\u03b1-\u03ba\u03bc-\u03c9"
    "\u0391-\u039f\u03a1\u03a4-\u03a9\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f"
    "\U0001d49c-\U0001d59f"
)
_ID_REST = _ID_FIRST + "0-9'!?\u2080-\u209c\u1d62-\u1d6a\u2c7c"

# A declaration name must look like an identifier; anything else means the header regex
# captured punctuation, as with an anonymous `instance : Foo := ...`.
IDENTIFIER = re.compile(rf"[{_ID_FIRST}][{_ID_REST}.]*")

_TOKEN = rf"[{_ID_FIRST}][{_ID_REST}]*"
# Dotted identifier-like names, skipping the binding site of `let` and `have`, names right
# after a single `.` (see FIELD_TOKENIZER), and name literals (`` `Foo.bar ``, `decl_name% foo`),
# which are data rather than references to the constant.
TOKENIZER = re.compile(rf"(?<![{_ID_REST}`])(?<!(?<!\.)\.)(?<!\blet\s)(?<!\bhave\s)"
                       rf"(?<!\bdecl_name%\s){_TOKEN}(?:\.{_TOKEN})*")
# Names after a `.` that does not continue a name are resolved through a type, not as
# globals: field notation on a term (`(f x).sum`) through the term's type, and a leading-dot
# name (`.ok x`, `| .record r`) through the expected type. The former, matched here, very often
# names a declaration in the namespace being written, the latter mostly a constructor.
FIELD_TOKENIZER = re.compile(rf"(?<=[)\]⟩}}]\.){_TOKEN}(?:\.{_TOKEN})*")

# A field being given a value - `{ x := 1 }`, `where` lines `x := 1`, named arguments
# `(motive := ...)` - names a field or parameter, not a global constant.
FIELD_ASSIGNMENT = re.compile(rf"(?m)(?P<pre>(?:^|[{{(,]|\bwith\b)[ \t]*){_TOKEN}(?=[ \t]*:=)")
# A field declared in a `structure` or `class`: an indented `x y : T` line.
FIELD_DECLARATION = re.compile(rf"(?m)^[ \t]+(?:{_TOKEN}[ \t]+)*{_TOKEN}(?=[ \t]*:(?!=))")

# Tokens never treated as references.
IGNORED_TOKENS = frozenset({"blueprint_comment"})

# Tactics that share their name with lemmas projects commonly declare (`@[ext] theorem ext`).
# Invoked as a tactic - at the start of a line, or after `·`, `by`, `;` or `<;>` - the word
# refers to the tactic, not to the lemma.
_TACTICS = (
    "ext|funext|congr|symm|trans|constructor|left|right|use|exists|refine|apply|exact|intro"
    "|cases|induction|split|change|unfold|specialize|lift|abel|group|ring|bound|positivity"
    "|gcongr|convert|subst|contradiction|exfalso|trivial|rfl|decide|simp|omega|linarith|tauto"
)
TACTIC_CALL = re.compile(
    rf"(?m)(?P<pre>^[ \t]*(?:[·•][ \t]*)?|\bby[ \t]+|;[ \t]*|<;>[ \t]*)(?:{_TACTICS})(?![\w'.])"
)

# Names bound locally inside a proof or term. The tokenizer's lookbehinds skip the binding
# site itself (`have hU : ...`) but not later uses (`exact hU.trans _`), so a local hypothesis
# sharing its name with a global declaration would still resolve to it. Collecting the bound
# names lets them be subtracted from the token set instead.
# Each pattern captures a binder list; `binder_names` drops the type ascriptions from it.
BINDERS = (
    re.compile(r"\b(?:have|let|set|suffices)\s+(?P<names>[^:\n]*?)(?=:|←|<-|\bwith\b|\n|$)"),
    re.compile(r"\b(?:intro|rintro|intros|obtain)\b(?P<names>[^;\n]*?)(?=;|<;>|:=|\n|$)"),
    re.compile(r"\b(?:rcases|cases'|induction'|obtain)\b[^\n]*?\bwith\b(?P<names>[^;\n]*)"),
    re.compile(r"\bset\b[^\n]*?\bwith\s+←?\s*(?P<names>[^\s;]+)"),
    re.compile(r"\bchoose!?\s+(?P<names>[^\n]*?)\busing\b"),
    re.compile(r"(?:\bfun\b|λ)(?P<names>[^\n]*?)(?:=>|↦)"),
    re.compile(r"[∀∃∑∏⋃⋂⨆⨅](?P<names>[^,\n]*),"),
)
# Outside brackets, a binder predicate (`∀ x ∈ s`, `∃ ε > 0`) or a filter (`∀ᶠ x in f`) ends
# the bound names.
_BINDER_STOP = re.compile(r"[∈∉≤<≥>≠⊆⊂⊇⊃]|(?<![\w'])in(?![\w'])")

# ---------------------------------------------------------------------------
# Notation
# ---------------------------------------------------------------------------

# e.g. `notation3:max "ρ[" X " # " A "]" => rho X A volume`. A dependency introduced through
# notation is never written by name in the source, so without expanding these the referenced
# constants are invisible.
NOTATION = re.compile(
    r"^[ \t]*(?:(?P<local>local)\s+|(?P<scoped>scoped)(?:\[(?P<scoped_ns>[^\]\n]*)\])?\s+)?"
    r"(?:notation3|notation|infixl|infixr|infix|prefix|postfix)(?![\w'])"
    r"(?::[^\s\"]+)?[ \t]*(?P<rest>.*)$",
    re.MULTILINE,
)
STRING_LITERAL = re.compile(r'"([^"]*)"')
# Options such as `(name := foo)` or `(priority := high)` on a notation command.
NOTATION_OPTION = re.compile(r"\(\s*\w+\s*:=[^)]*\)")
# Notation written only with brackets and commas, such as `"⟨" X ", " Y "⟩"`, cannot be told
# apart from Lean's own anonymous constructor, tuple, list and set syntax.
BUILTIN_SHAPE = re.compile(r"[()\[\]{}⟨⟩,]+")

# ---------------------------------------------------------------------------
# Scopes
# ---------------------------------------------------------------------------

NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)\s*$")
VARIABLE = re.compile(r"^\s*variable(?![\w'])")
OPEN = re.compile(r"^open(?![\w'])")
# `variable (x : α) in`, `open Foo in`: the command applies to the next command only.
_COMMAND_IN = re.compile(r"(?<![\w'])in\s*$")
# What an `open` stops listing namespaces at: `open Foo (bar)`, `open Foo hiding bar`.
_OPEN_END = re.compile(r"[(]|(?<![\w'])(?:hiding|renaming|in)(?![\w'])")
END = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
SECTION = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected|unsafe|partial|scoped|local)\s+)*"
    r"section(?:\s+(\S+))?\s*$"
)

# ---------------------------------------------------------------------------
# Text utilities
# ---------------------------------------------------------------------------

_PAIRS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
_CLOSERS = {v: k for k, v in _PAIRS.items()}
_COMMENT_OR_STRING = re.compile(r'"|--|/-')
_BLOCK_DELIMITER = re.compile(r"/-|-/")
# The `r#` of a raw string literal `r#"..."#`, matched just before its opening quote.
_RAW_STRING_PREFIX = re.compile(r"(?<![\w'])r(#*)\Z")
_ATTRIBUTE_OR_STRING = re.compile(r'"|@\[')


def string_end(text: str, start: int) -> int | None:
    r"""The offset just past the string literal whose opening quote is at `start`.

    Returns None if the quote opens no string: it is the character literal `'"'` or `'\"'`.
    Strings may span lines and raw strings (`r#"..."#`) have no escapes, as in Lean. In an
    interpolated string (`s!"..."`, `m!"..."`) a `{...}` holds code, which may contain strings
    of its own. An unterminated string ends with its line, so a stray quote cannot swallow
    the whole file.
    """
    if text[start + 1:start + 2] == "'" and text[start - 1:start] in ("'", "\\"):
        return None
    if raw := _RAW_STRING_PREFIX.search(text, max(start - 64, 0), start):
        end = text.find('"' + raw.group(1), start + 1)
        if end >= 0:
            return end + 1 + len(raw.group(1))
    else:
        interpolated = text[start - 1:start] == "!"
        depth, end = 0, start + 1
        while end < len(text) and (depth or text[end] != '"'):
            ch = text[end]
            if ch == "\\":
                end += 2
                continue
            if depth and ch == '"' and (nested := string_end(text, end)) is not None:
                end = nested
                continue
            if interpolated and ch in "{}":
                depth = max(depth + (1 if ch == "{" else -1), 0)
            end += 1
        if end < len(text):
            return end + 1
    line_end = text.find("\n", start)
    return len(text) if line_end < 0 else line_end


def string_spans(text: str) -> list[tuple[int, int]]:
    """The (start, end) offsets of every string literal in comment-free source."""
    spans = []
    pos = 0
    while (start := text.find('"', pos)) >= 0:
        if (end := string_end(text, start)) is None:
            pos = start + 2
        else:
            spans.append((start, end))
            pos = end
    return spans


def mask_strings(text: str, keep_interpolations: bool = False) -> str:
    """Replace the contents of string literals with spaces, keeping offsets and newlines.

    Keywords inside strings (`throwError "... lemma {n}"`) then no longer look like code. With
    `keep_interpolations`, the code inside `{...}` (`m!"{foo x}"`) is kept.
    """
    out = list(text)
    for start, end in string_spans(text):
        depth = 0
        for i in range(start + 1, end - 1):
            ch = text[i]
            if keep_interpolations and ch in "{}":
                depth = max(depth + (1 if ch == "{" else -1), 0)
            elif depth:
                continue
            if ch != "\n":
                out[i] = " "
    return "".join(out)


def attribute_spans(text: str) -> list[tuple[int, int]]:
    """The (start, end) offsets of every `@[...]` attribute and the whitespace after it.

    Brackets nest (`@[simp, aesop (rule_sets := [Foo])]`), and `@[` inside a string literal is
    not an attribute.
    """
    spans = []
    pos = 0
    while m := _ATTRIBUTE_OR_STRING.search(text, pos):
        start = m.start()
        if m.group() == '"':
            end = string_end(text, start)
            pos = start + 2 if end is None else end
            continue
        depth, i = 0, start + 1
        while i < len(text):
            if text[i] == '"' and (end := string_end(text, i)) is not None:
                i = end
                continue
            depth += {"[": 1, "]": -1}.get(text[i], 0)
            i += 1
            if not depth:
                break
        if depth:  # unterminated: leave it alone
            pos = start + 2
            continue
        while i < len(text) and text[i].isspace():
            i += 1
        spans.append((start, i))
        pos = i
    return spans


def comment_spans(text: str) -> list[tuple[int, int]]:
    """The (start, end) offsets of every comment in Lean source.

    Block comments nest, as in Lean, and comment markers inside string literals are ignored.
    """
    spans = []
    pos = 0
    while m := _COMMENT_OR_STRING.search(text, pos):
        start = m.start()
        if m.group() == '"':
            end = string_end(text, start)
            pos = start + 2 if end is None else end
        elif m.group() == "--":
            end = text.find("\n", start)
            end = len(text) if end < 0 else end
            spans.append((start, end))
            pos = end
        else:
            depth, end = 1, start + 2
            while depth and (d := _BLOCK_DELIMITER.search(text, end)):
                depth += 1 if d.group() == "/-" else -1
                end = d.end()
            if depth:  # unterminated: Lean comments it out to the end of the file
                end = len(text)
            spans.append((start, end))
            pos = end
    return spans


def blank_spans(text: str, spans: list[tuple[int, int]]) -> str:
    """Replace each span with just its newlines, so later line numbers stay correct."""
    out, pos = [], 0
    for start, end in spans:
        out += [text[pos:start], "\n" * text.count("\n", start, end)]
        pos = end
    out.append(text[pos:])
    return "".join(out)


def line_starts(text: str) -> list[int]:
    """Character offsets at which each line begins (line 1 starts at offset 0)."""
    return [0, *(i + 1 for i, ch in enumerate(text) if ch == "\n")]


def line_of(pos: int, starts: list[int]) -> int:
    """The 1-indexed line containing character offset `pos`."""
    return bisect.bisect_right(starts, pos)


def find_top_level(text: str, target: str) -> int | None:
    """Index of the first `target` not enclosed in brackets (`()`, `[]`, `{}`, `⦃⦄`, `⟨⟩`).

    Brackets inside string literals do not count.
    """
    stack: list[str] = []
    in_string = False
    for i, ch in enumerate(text):
        if ch == '"' and text[i - 1:i] != "\\":
            in_string = not in_string
        elif in_string:
            continue
        elif ch in _PAIRS:
            stack.append(ch)
        elif ch in _CLOSERS:
            if stack and stack[-1] == _CLOSERS[ch]:
                stack.pop()
        elif not stack and text.startswith(target, i):
            return i
    return None


def find_assignment(text: str) -> int | None:
    """Index of the `:=` that starts a declaration's body.

    The first one outside brackets, so that default arguments `(h : P := by simp)` in the
    signature are skipped - or, if the brackets never balance, simply the first one.
    """
    ix = find_top_level(text, ":=")
    if ix is None and (ix := text.find(":=")) < 0:
        return None
    return ix


def first_top_level_colon(text: str) -> int | None:
    """Index of the first `:` not enclosed in brackets."""
    return find_top_level(text, ":")


def split_header(rest: str) -> tuple[str, str] | None:
    """Split what follows a declaration keyword into (name, signature and body).

    Returns None for an anonymous declaration, such as ``instance : Foo := ...``.
    """
    rest = _PRE_NAME.sub("", rest, count=1) if _PRE_NAME.match(rest) else rest
    if not (m := DECLARATION_NAME.match(rest)):
        return None
    return m.group("name"), rest[m.end():]


def binder_names(binders: str) -> list[str]:
    """The names bound by a binder list, without the types: ``x (y z : T) ⟨a, b⟩ : U``."""
    kept: list[str] = []
    stack: list[bool] = []  # per open bracket: whether the enclosing text was being skipped
    skipping = False
    for i, ch in enumerate(binders):
        if not stack and _BINDER_STOP.match(binders, i):
            break
        if ch in _PAIRS:
            stack.append(skipping)
        elif ch in _CLOSERS and stack:
            skipping = stack.pop()
        elif ch == ":":
            skipping = True  # a type ascription, to the end of the enclosing bracket
        elif not skipping:
            kept.append(ch)
            continue
        kept.append(" ")
    return TOKENIZER.findall("".join(kept))


@dataclass
class BracketGroup:
    """A top-level bracketed group of a string."""

    opener: str  # one of '(', '[', '{'
    text: str  # including the brackets
    start: int
    end: int  # exclusive

    @property
    def inner(self) -> str:
        """The text between the brackets."""
        return self.text[1:-1]


def bracket_groups(text: str) -> list[BracketGroup]:
    """The top-level groups enclosed in (), [] or {}; unmatched brackets are ignored."""
    groups = []
    stack: list[tuple[str, int]] = []
    for i, ch in enumerate(text):
        if ch in _PAIRS:
            stack.append((ch, i))
        elif ch in _CLOSERS and stack and stack[-1][0] == _CLOSERS[ch]:
            opener, start = stack.pop()
            if not stack:
                groups.append(BracketGroup(opener, text[start:i + 1], start, i + 1))
    return groups


def _pop_scope(stack: list[tuple], name: str | None) -> None:
    """Close the scope(s) named by an `end`, leaving the stack alone if nothing matches.

    Stack entries start with (is_namespace, name); anonymous sections have name None.
    """
    if name is None:
        # A bare `end` closes the innermost anonymous section.
        if stack and not stack[-1][0] and stack[-1][1] is None:
            stack.pop()
        return
    parts = name.split(".")
    if len(stack) >= len(parts) and [e[1] for e in stack[-len(parts):]] == parts:
        del stack[-len(parts):]
    elif stack and stack[-1][1] == parts[-1]:
        # Tolerate a partial match rather than leaving the stack permanently skewed.
        stack.pop()


def namespace_ranges(src: str) -> list[tuple[str | None, int, int]]:
    """Contiguous character ranges of `src`, each with the namespace it lies in.

    Namespaces are dotted strings like ``"A.B"``, or None at the top level. ``namespace A.B``
    opens one scope per dotted component, exactly as Lean does, so that ``end B`` closes only
    ``B`` and ``end A.B`` closes both. Sections share the same stack, since ``end Foo`` is
    ambiguous between the two and only a shared stack can tell which one it closes.
    """
    # Entries are (is_namespace, name); anonymous sections have name None.
    stack: list[tuple[bool, str | None]] = []

    def current() -> str | None:
        parts = [name for is_ns, name in stack if is_ns and name]
        return ".".join(parts) if parts else None

    ranges: list[tuple[str | None, int, int]] = []
    ns: str | None = None
    range_start = offset = 0
    for line in src.splitlines(keepends=True):
        line_start, offset = offset, offset + len(line)
        if m := NAMESPACE.match(line):
            stack.extend((True, part) for part in m.group(1).split("."))
        elif m := SECTION.match(line):
            stack.append((False, m.group(1)))
            continue  # sections never change the namespace
        elif m := END.match(line):
            _pop_scope(stack, m.group(1))
        else:
            continue
        if line_start > range_start:
            ranges.append((ns, range_start, line_start))
        ns, range_start = current(), line_start
    if offset > range_start:
        ranges.append((ns, range_start, offset))
    return ranges


def namespace_at(pos: int, ranges: list[tuple[str | None, int, int]]) -> str | None:
    """The namespace containing character offset `pos`."""
    return next((ns for ns, start, end in ranges if start <= pos < end), None)


def variable_names(binders: str) -> set[str]:
    """The names bound by the binders of a `variable` command: ``{x y : α} [Foo α] (z)``."""
    names: set[str] = set()
    for group in bracket_groups(binders):
        inner = group.inner
        if (ix := first_top_level_colon(inner)) is not None:
            names.update(TOKENIZER.findall(inner[:ix]))
        elif group.opener != "[":  # `(x)` updates the binder `x`; `[Foo α]` is anonymous
            names.update(TOKENIZER.findall(inner))
    return names


def opened_namespaces(command: str) -> set[str]:
    """The namespaces an `open` command opens: ``open Foo Bar.Baz``; not ``open scoped Foo``."""
    if command.split(None, 1)[:1] == ["scoped"]:
        return set()  # opens notation and instances only, not names
    if m := _OPEN_END.search(command):
        command = command[:m.start()]
    return set(TOKENIZER.findall(command))


def scoped_namespaces(command: str) -> set[str]:
    """The namespaces an `open scoped Foo Bar` command opens; none for a plain `open`."""
    keyword, _, rest = command.strip().partition(" ")
    return opened_namespaces(rest) if keyword == "scoped" else set()


def scoped_ranges(src: str, command: re.Pattern, extract: Callable[[str], set[str]],
                  ) -> list[tuple[frozenset[str], int, int]]:
    """Contiguous character ranges of `src`, each with the names `command`s put in scope there.

    Each line matching `command` (`variable`, `open`), with any indented lines that continue
    it, contributes `extract(text after the keyword)` until the end of the enclosing section
    or namespace; with a trailing `in`, for the next command only.
    """
    lines = src.splitlines(keepends=True)
    # Entries are (is_namespace, name, names added in that scope).
    stack: list[tuple[bool, str | None, set[str]]] = []
    top: set[str] = set()
    pending: set[str] = set()  # added by `... in`
    pending_lines = 0  # unindented lines left before `pending` expires

    def current() -> frozenset[str]:
        return frozenset(top.union(pending, *(names for _, _, names in stack)))

    ranges: list[tuple[frozenset[str], int, int]] = []
    names = current()
    range_start = offset = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        line_start, offset = offset, offset + len(line)
        i += 1
        if pending and line[:1].strip():
            pending_lines -= 1
            if not pending_lines:
                pending = set()
        if m := command.match(line):
            # The command runs on over indented and blank lines.
            end = next((j for j in range(i, len(lines)) if lines[j][:1].strip()), len(lines))
            text = line[m.end():] + "".join(lines[i:end])
            offset += sum(map(len, lines[i:end]))
            i = end
            added = extract(text)
            if _COMMAND_IN.search(text):
                # Expires at the second unindented line from here: the one after the command.
                pending, pending_lines = pending | added, 2
            else:
                (stack[-1][2] if stack else top).update(added)
        elif m := NAMESPACE.match(line):
            stack.extend((True, part, set()) for part in m.group(1).split("."))
        elif m := SECTION.match(line):
            stack.append((False, m.group(1), set()))
        elif m := END.match(line):
            _pop_scope(stack, m.group(1))
        if (new := current()) != names:
            if line_start > range_start:
                ranges.append((names, range_start, line_start))
            names, range_start = new, line_start
    if offset > range_start:
        ranges.append((names, range_start, offset))
    return ranges


def variable_types(binders: str) -> set[str]:
    """`name:Head` for each binder of a `variable` command whose type is a capitalised name.

    ``{l : List α} (h : a ≤ b)`` gives ``{"l:List"}``; see `Declaration.variable_types`.
    """
    typed: set[str] = set()
    for group in bracket_groups(binders):
        inner = group.inner
        if (ix := first_top_level_colon(inner)) is None:
            continue
        if (m := TOKENIZER.match(inner[ix + 1:].strip())) and m.group()[0].isupper():
            typed.update(f"{name}:{m.group()}" for name in TOKENIZER.findall(inner[:ix]))
    return typed


def variable_type_ranges(src: str) -> list[tuple[frozenset[str], int, int]]:
    """`scoped_ranges` for `variable_types`."""
    return scoped_ranges(src, VARIABLE, variable_types)


def variable_ranges(src: str) -> list[tuple[frozenset[str], int, int]]:
    """`scoped_ranges` for `variable` names, which are local and shadow global constants."""
    return scoped_ranges(src, VARIABLE, variable_names)


def open_ranges(src: str) -> list[tuple[frozenset[str], int, int]]:
    """`scoped_ranges` for the namespaces opened by `open`."""
    return scoped_ranges(src, OPEN, opened_namespaces)


def scoped_open_ranges(src: str) -> list[tuple[frozenset[str], int, int]]:
    """`scoped_ranges` for the namespaces opened by `open scoped`, for their notation only."""
    return scoped_ranges(src, OPEN, scoped_namespaces)


def names_at(pos: int, ranges: list[tuple[frozenset[str], int, int]]) -> frozenset[str]:
    """The names in scope at character offset `pos`, per `scoped_ranges`."""
    return next((names for names, start, end in ranges if start <= pos < end), frozenset())
