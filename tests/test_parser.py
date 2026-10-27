from __future__ import annotations

import textwrap

from lexical_lean_parser import (
    Declaration,
    find_lean_files,
    parse_dependencies,
    parse_file,
    parse_text,
)
from lexical_lean_parser.parser import local_binder_names


def decls(src: str) -> dict[str, Declaration]:
    return {d.full_name: d for d in parse_text(textwrap.dedent(src)).declarations}


def deps_of(project, name: str) -> set[str]:
    by_name = {d.full_name: d for items in parse_dependencies(project).values()
               for d in items if isinstance(d, Declaration)}
    return {d.full_name for d in by_name[name].depends_on}


def test_declaration_fields_and_lines():
    src = """
    import Mathlib.Data.Nat.Basic

    /-- The double. -/
    def double (n : Nat) : Nat := n + n

    theorem double_eq (n : Nat) : double n = 2 * n := by
      unfold double
      omega
    """
    parsed = parse_text(textwrap.dedent(src))
    assert [i.name for i in parsed.imports] == ["Mathlib.Data.Nat.Basic"]
    d = {x.name: x for x in parsed.declarations}
    assert d["double"].kind == "def"
    assert d["double"].definition == "(n : Nat) : Nat"
    assert d["double"].body == "n + n"
    assert (d["double"].start_line, d["double"].end_line) == (5, 5)
    assert d["double_eq"].definition == "(n : Nat) : double n = 2 * n"
    assert (d["double_eq"].start_line, d["double_eq"].end_line) == (7, 9)
    assert d["double"].arguments == {"n": "Nat"}


def test_namespaces_sections_and_root():
    src = """
    namespace A.B

    section foo

    lemma inner : True := trivial

    end foo

    end B

    def _root_.Top.escaped : Nat := 0

    lemma outer : True := trivial

    end A

    theorem top : True := trivial
    """
    assert set(decls(src)) == {"A.B.inner", "Top.escaped", "A.outer", "top"}


def test_anonymous_instance_is_skipped_but_named_one_kept():
    src = """
    instance : Inhabited Nat := ⟨0⟩

    instance instFoo : Inhabited Bool := ⟨true⟩
    """
    assert set(decls(src)) == {"instFoo"}


def test_aliases():
    src = """
    namespace Foo

    theorem bar_iff : True ↔ True := Iff.rfl

    alias baz := bar_iff
    alias ⟨_, qux⟩ := bar_iff

    end Foo
    """
    d = decls(src)
    assert {"Foo.baz", "Foo.qux"} <= set(d)
    assert d["Foo.baz"].kind == "alias"
    assert d["Foo.baz"].body == "bar_iff"


def test_todo_comments_are_counted():
    src = """
    -- TODO: generalise
    lemma a : True := trivial

    lemma b : True := by
      -- todo golf this
      trivial

    lemma c : True := trivial
    """
    d = decls(src)
    assert (d["a"].n_todos, d["b"].n_todos, d["c"].n_todos) == (1, 1, 0)


def test_dependencies_resolve_across_files_and_namespaces(make_project):
    project = make_project({
        "Lib/Defs.lean": """
            namespace Lib

            def size (n : Nat) : Nat := n

            end Lib
            """,
        "Lib/Main.lean": """
            import Lib.Defs

            namespace Lib

            theorem size_eq (n : Nat) : size n = n := rfl

            end Lib

            theorem uses_qualified : Lib.size 0 = 0 := Lib.size_eq 0
            """,
    })
    assert deps_of(project, "Lib.size_eq") == {"Lib.size"}
    assert deps_of(project, "uses_qualified") == {"Lib.size", "Lib.size_eq"}


def test_signature_and_body_dependencies_are_split(make_project):
    project = make_project({"A.lean": """
        def P : Prop := True

        lemma p_holds : True := trivial

        theorem t : P := p_holds
        """})
    t = next(d for d in parse_dependencies(project)[project / "A.lean"]
             if getattr(d, "name", None) == "t")
    assert [d.name for d in t.depends_on_def] == ["P"]
    assert [d.name for d in t.depends_on_body] == ["p_holds"]
    assert {d.name for d in t.depends_on} == {"P", "p_holds"}


def test_local_binders_do_not_resolve_to_globals(make_project):
    project = make_project({"A.lean": """
        lemma h : True := trivial

        theorem t (x : Nat) : True := by
          have h : True := trivial
          intro y
          exact h
        """})
    assert deps_of(project, "t") == set()


def test_ambiguous_references_prefer_the_same_file(make_project):
    project = make_project({
        "A.lean": """
            namespace A

            def f : Nat := 0

            end A
            """,
        "B.lean": """
            namespace B

            def f : Nat := 1

            end B

            open A B in
            def g : Nat := f
            """,
    })
    assert deps_of(project, "g") == {"B.f"}


def test_notation_is_expanded(make_project):
    project = make_project({"A.lean": """
        def rho (x : Nat) : Nat := x

        def sigma (x : Nat) : Nat := rho x

        notation3:max "ρ[" X "]" => rho X

        local notation "σ[" X "]" => sigma X

        theorem t : ρ[0] = σ[0] := rfl
        """})
    assert deps_of(project, "t") == {"rho", "sigma"}


def test_find_lean_files_matches_relative_paths(make_project):
    project = make_project({
        "Lib/A.lean": "",
        "Lib/Greatest.lean": "",
        "Lib/Description.lean": "",
        "Lib/Tests/T.lean": "",
        "docs/D.lean": "",
        ".lake/packages/X.lean": "",
        "lakefile.lean": "",
    })
    # Excluded folder names match whole path components, not substrings ("Greatest" has
    # "test" in it, "Description" has "script").
    assert [p.relative_to(project).as_posix() for p in find_lean_files(project)] == [
        "Lib/A.lean", "Lib/Description.lean", "Lib/Greatest.lean"]
    # Matching is relative to the project, so an excluded word in the parent path is harmless.
    nested = project / "Lib"
    assert [p.name for p in find_lean_files(nested)] == ["A.lean", "Description.lean",
                                                         "Greatest.lean"]


# ---------------------------------------------------------------------------
# Regression tests for parser bugs
# ---------------------------------------------------------------------------


def test_namespace_is_right_after_a_long_header():
    # Offsets into the stripped text were looked up in a namespace map of the unstripped text,
    # so declarations near a namespace boundary landed in the wrong namespace.
    header = "/-\n" + "Copyright line\n" * 30 + "-/\n"
    src = header + textwrap.dedent("""
        namespace Foo

        theorem a : True := trivial

        end Foo

        theorem b : True := trivial
        """)
    assert set(decls(src)) == {"Foo.a", "b"}


def test_nested_block_comments():
    src = """
    theorem first : True := trivial

    /-
    /-- An old docstring. -/
    theorem old : True := trivial
    -/

    theorem new : True := trivial
    """
    assert set(decls(src)) == {"first", "new"}


def test_comment_markers_inside_strings_are_not_comments():
    src = """
    def s : String := "a -- b /- c"

    theorem t : True := trivial
    """
    d = decls(src)
    assert d["s"].body == '"a -- b /- c"'
    assert set(d) == {"s", "t"}


def test_consecutive_declarations_with_modifiers():
    src = """
    noncomputable def a : Nat := 0
    noncomputable def b : Nat := 1
    private theorem c : True := trivial
    protected lemma d : True := trivial
    """
    assert set(decls(src)) == {"a", "b", "c", "d"}


def test_commands_after_a_declaration_are_not_part_of_it(make_project):
    project = make_project({"A.lean": """
        theorem x : True := trivial

        theorem y : True := trivial
        attribute [simp] x
        open Nat in
        theorem z : True := trivial

        #check y
        """})
    assert deps_of(project, "y") == set()
    assert deps_of(project, "z") == set()


def test_declaration_header_variants():
    src = """
    theorem glued: True := trivial

    def withUniverse.{u} (α : Sort u) : Sort u := α

    instance (priority := 100) instWithPriority : Inhabited Nat := ⟨0⟩

    instance (priority := 100) : Inhabited Bool := ⟨true⟩

    class inductive Marker : Prop
      | mk

    def X := 0

    attribute [local instance 100] instWithPriority
    """
    assert set(decls(src)) == {"glued", "withUniverse", "instWithPriority", "Marker", "X"}


def test_default_arguments_do_not_split_the_signature():
    d = decls("theorem t (n : Nat) (h : 0 ≤ n := by omega) : n + 0 = n := by simp\n")["t"]
    assert d.definition == "(n : Nat) (h : 0 ≤ n := by omega) : n + 0 = n"
    assert d.body == "by simp"


def test_references_inside_anonymous_constructors(make_project):
    project = make_project({"A.lean": """
        lemma p : True := trivial

        lemma q : True := trivial

        theorem t : True ∧ True := ⟨p, q⟩
        """})
    assert deps_of(project, "t") == {"p", "q"}


def test_field_notation_on_a_declaration(make_project):
    project = make_project({"A.lean": """
        theorem foo : True ↔ True := Iff.rfl

        theorem h : True := trivial

        theorem t : True := foo.mp trivial

        theorem u (h : True ↔ True) : True := h.mp trivial
        """})
    assert deps_of(project, "t") == {"foo"}
    # `h.mp` is field notation on the local `h`, not on the global `h`.
    assert deps_of(project, "u") == set()


def test_binder_types_are_not_bound_names(make_project):
    project = make_project({"A.lean": """
        structure Point where
          x : Nat

        def S : Set Nat := ∅

        theorem helper : True := trivial

        def f : Point → Nat := fun (p : Point) => p.x

        theorem g : ∀ n : Nat, ∀ m ∈ S, True := by
          intro n m hm; exact helper
        """})
    assert deps_of(project, "f") == {"Point"}
    assert deps_of(project, "g") == {"S", "helper"}


def test_pattern_bound_names_do_not_resolve_to_globals(make_project):
    project = make_project({"A.lean": """
        theorem hx : True := trivial

        theorem t (h : ∃ x : Nat, x = x) : True := by
          obtain ⟨x, hx⟩ := h
          exact trivial
        """})
    assert deps_of(project, "t") == set()


def test_dotted_declaration_name_opens_its_namespace(make_project):
    project = make_project({"A.lean": """
        def Point.zero : Nat := 0

        def Point.one : Nat := zero + 1
        """})
    assert deps_of(project, "Point.one") == {"Point.zero"}


def test_declarations_in_different_namespaces_are_distinct(make_project):
    project = make_project({"A.lean": """
        namespace A

        theorem h : True := trivial

        end A

        namespace B

        theorem h : True := trivial

        end B

        theorem t : True ∧ True := And.intro A.h B.h
        """})
    assert deps_of(project, "t") == {"A.h", "B.h"}


def test_tactic_invocations_are_not_references(make_project):
    project = make_project({"A.lean": """
        structure P where
          x : Nat

        namespace P

        theorem ext {a b : P} (h : a.x = b.x) : a = b := by
          cases a; cases b; simp_all

        theorem uses_tactic (a : P) : a = a := by
          ext
          rfl

        theorem uses_lemma (a b : P) (h : a.x = b.x) : a = b := by
          exact ext h

        end P
        """})
    assert deps_of(project, "P.uses_tactic") == {"P"}
    assert deps_of(project, "P.uses_lemma") == {"P", "P.ext"}


def test_import_names():
    src = "public import Mathlib.Tactic -- everything\nimport Lib.Basic   \n"
    assert [i.name for i in parse_text(src).imports] == ["Mathlib.Tactic", "Lib.Basic"]


def test_notation_resolves_where_it_is_declared(make_project):
    project = make_project({
        "Lib/Defs.lean": """
            namespace Prob

            def entropy (n : Nat) : Nat := n

            namespace Kernel

            def entropy (n : Nat) : Nat := n

            end Kernel

            notation "H[" X "]" => entropy X

            end Prob
            """,
        "Lib/Use.lean": """
            import Lib.Defs

            theorem t : H[0] = 0 := rfl
            """,
    })
    assert deps_of(project, "t") == {"Prob.entropy"}


def test_overlapping_notations(make_project):
    project = make_project({"A.lean": """
        def mi (a b : Nat) : Nat := a + b

        def cmi (a b c : Nat) : Nat := a + b + c

        notation "I[" X " : " Y "]" => mi X Y

        notation "I[" X " : " Y " | " Z "]" => cmi X Y Z

        theorem uses_cmi : I[1 : 2 | 3] = 6 := rfl

        theorem uses_mi : I[1 : 2] = 3 := rfl

        theorem no_overrun (h : I[1 : 2] = 3) : 1 ∣ 3 ∧ True := by exact ⟨by decide, trivial⟩
        """})
    assert deps_of(project, "uses_cmi") == {"cmi"}
    assert deps_of(project, "uses_mi") == {"mi"}
    # `I[1 : 2]` followed later on the line by `∣ ... ]` is not a use of `I[_ : _ | _]`.
    assert deps_of(project, "no_overrun") == {"mi"}


def test_notation_tokens_are_read_longest_first(make_project):
    project = make_project({"A.lean": """
        def conv (a b : Nat) : Nat := a + b

        def cconv (a b : Nat) : Nat := a * b

        infixl:71 " ∗ " => conv

        infixl:71 " ∗ₙ " => cconv

        theorem uses_cconv : 2 ∗ₙ 3 = 6 := rfl

        theorem uses_both : 2 ∗ₙ 3 ∗ 1 = 7 := rfl
        """})
    # Lean's tokenizer reads `∗ₙ` as one token, so it is not also a use of `∗`.
    assert deps_of(project, "uses_cconv") == {"cconv"}
    assert deps_of(project, "uses_both") == {"cconv", "conv"}


def test_bracket_only_notation_is_ignored(make_project):
    # Indistinguishable from Lean's anonymous constructor syntax.
    project = make_project({"A.lean": """
        def pair (a b : Nat) : Nat × Nat := (a, b)

        notation3 "⟨" X ", " Y "⟩" => pair X Y

        theorem t : ∃ n : Nat, n = n := ⟨0, rfl⟩
        """})
    assert deps_of(project, "t") == set()


def test_indented_declarations():
    src = """
    namespace Foo

      theorem a : True := by
        trivial

      theorem b : True := trivial

    end Foo

    mutual
      def even : Nat → Bool
        | 0 => true
        | n + 1 => odd n
      def odd : Nat → Bool
        | 0 => false
        | n + 1 => even n
    end
    """
    assert set(decls(src)) == {"Foo.a", "Foo.b", "even", "odd"}


def test_deriving_instance_is_not_a_declaration():
    assert decls("inductive T\n  | a\n\nderiving instance Repr for T\n") == {}


def test_notation_variants():
    src = """
    scoped[Prob] notation "H[" X "]" => entropy X

    notation (name := dNotation) "d[" X "]" => dist X
    """
    a, b = parse_text(textwrap.dedent(src)).notations
    assert a.literals == ["H[", "]"]
    assert b.params == ("X",)


def test_unbalanced_brackets_before_the_body():
    d = decls('theorem t (s : String := "(") : True := trivial\n')["t"]
    assert d.body == "trivial"


def test_binder_predicates_inside_brackets():
    assert local_binder_names("∀ (hx : x ∈ s) (y : Nat), True") == {"hx", "y"}
    assert local_binder_names("∀ x ∈ S, ∃ ε > 0, True") == {"x", "ε"}


def test_equation_style_declarations():
    d = decls("theorem foo : ∀ n : Nat, n = n\n  | 0 => rfl\n  | n+1 => rfl\n")["foo"]
    assert d.definition == ": ∀ n : Nat, n = n"
    assert d.body.startswith("| 0 => rfl")


def test_byte_order_mark_and_crlf(tmp_path):
    path = tmp_path / "A.lean"
    path.write_bytes("﻿import Foo\n\ntheorem a : True := trivial\n".encode())
    assert [i.name for i in parse_file(path).imports] == ["Foo"]
    parsed = parse_text("import Foo\r\nimport Bar\r\n\r\ntheorem a : True := trivial\r\n")
    assert [i.name for i in parsed.imports] == ["Foo", "Bar"]
    assert [d.name for d in parsed.declarations] == ["a"]


def test_attribute_syntax_inside_a_string_is_not_an_attribute():
    # `@[...]` followed by a backtick, not whitespace, once swallowed the rest of the file.
    found = decls('''
        def msg : String := s!"disable with `@[nolint {name}]` here"

        def after : Nat := 1

        @[simp, aesop safe (rule_sets := [Foo])] theorem last : True := trivial
        ''')
    assert set(found) == {"msg", "after", "last"}
    assert found["last"].definition == ": True"


def test_keywords_inside_strings_are_not_declarations():
    found = decls('''
        def a : String := "the definition of a constant to an entry"
        def b (n : Nat) : String := s!"trying lemma {n}
          theorem in a multi-line string"
        def c : Char := '\\"'
        def d : String := r#"raw " string def fake : Nat"#
        def e : Nat := 2
        ''')
    assert set(found) == {"a", "b", "c", "d", "e"}


def test_declaration_names_cannot_start_with_punctuation():
    found = decls('''
        macro "gen" name:ident : command => `(def $name : Nat := 1)

        A tidy structure - like this one.

        def «weird name» : Nat := 1
        ''')
    assert set(found) == {"«weird name»"}


def test_verso_document_is_not_lean_code():
    found = decls('''
        import VersoManual

        def real : Nat := 1

        #doc (Manual) "Title" =>

        Every theorem stated here has a structure given by prose.

        ```anchor Real
        def quoted : Nat := 1
        ```
        ''')
    assert set(found) == {"real"}


def test_section_variables_are_local_names(make_project):
    project = make_project({"A.lean": """
        def B : Nat := 0
        def f : Nat := 0

        section
        variable {α : Type} (B : Nat)
          (f : α → α) [Inhabited α]

        theorem uses_vars : B = B ∧ f = f := ⟨rfl, rfl⟩
        end

        theorem uses_global : B = 0 := rfl

        variable (f : Nat) in
        theorem scoped_in : f = f := rfl

        theorem after_in : f = 0 := rfl
        """})
    assert deps_of(project, "uses_vars") == set()
    assert deps_of(project, "uses_global") == {"B"}
    assert deps_of(project, "scoped_in") == set()
    assert deps_of(project, "after_in") == {"f"}


def test_only_imported_files_are_in_scope(make_project):
    project = make_project({
        "src/Lib/Core.lean": """
            def helper : Nat := 0
            """,
        "src/Lib/Mid.lean": """
            import Lib.Core
            """,
        "src/Lib/Other.lean": """
            def helper : Nat := 1
            def unrelated : Nat := 2
            """,
        "src/Lib/Use.lean": """
            import Mathlib.Tactic
            import Lib.Mid

            theorem t : helper = unrelated := rfl
            """,
    })
    # `helper` is ambiguous project-wide but only one is imported (through `Lib.Mid`, a
    # file with no declarations); `unrelated` is never imported, so cannot be meant.
    assert deps_of(project, "t") == {"helper"}
    by_file = {d.file.parent.name + "/" + d.file.name: d
               for items in parse_dependencies(project).values() for d in items
               if isinstance(d, Declaration) and d.name == "t"}
    assert by_file["Lib/Use.lean"].depends_on[0].file.name == "Core.lean"


def test_identifiers_with_lean_characters(make_project):
    # `?`, `!`, subscripts, letterlike and mathematical alphanumeric characters are all part
    # of Lean identifiers; the tokenizer once split or dropped them.
    project = make_project({"A.lean": """
        def find? (n : Nat) : Option Nat := some n
        def get! (n : Nat) : Nat := n
        def 𝒥₂ : Nat := 0
        def ℭ₁ : Nat := 0
        theorem find?_some : find? 0 = some 0 := rfl

        theorem uses : (find? 1).isSome ∧ get! 𝒥₂ = ℭ₁ := by
          exact ⟨rfl, find?_some ▸ rfl⟩
        """})
    assert deps_of(project, "uses") == {"find?", "find?_some", "get!", "𝒥₂", "ℭ₁"}


def test_names_after_a_dot_are_not_global_references(make_project):
    project = make_project({"A.lean": """
        def ok : Nat := 0
        def symm : Nat := 0

        theorem t (h : 1 = 1) : (Except.ok 1 : Except String Nat) = .ok 1 ∧ 1 = 1 :=
          ⟨rfl, (h.trans rfl).symm⟩
        """})
    assert deps_of(project, "t") == set()


def test_field_notation_resolves_in_the_enclosing_namespace(make_project):
    project = make_project({"A.lean": """
        namespace Series
        def sum (n : Nat) : Nat := n
        def reverse (n : Nat) : Nat := n
        theorem t (n : Nat) : (id n).sum = n ∧ Nat.succ n = .reverse n := ⟨rfl, rfl⟩
        end Series

        theorem u (n : Nat) : (id n).sum = n := rfl
        """})
    assert deps_of(project, "Series.t") == {"Series.sum"}
    assert deps_of(project, "u") == set()


def test_field_names_and_strings_are_not_references(make_project):
    project = make_project({"A.lean": """
        def goals : Nat := 0
        def empty : Nat := 0
        def size : Nat := 0

        structure Cluster where
          goals : Nat
          size : Nat := 0

        def mk (n : Nat) : Cluster := { goals := n, size := n }

        def describe (c : Cluster) : String := s!"empty cluster of size {c.size + size}"
        """})
    assert deps_of(project, "Cluster") == set()
    assert deps_of(project, "mk") == {"Cluster"}
    assert deps_of(project, "describe") == {"Cluster", "size"}


def test_root_declarations_resolve_in_their_enclosing_namespace(make_project):
    project = make_project({"A.lean": """
        namespace Prob
        def debut : Nat := 0
        theorem _root_.Set.debut_eq : debut = 0 := rfl
        end Prob
        """})
    assert deps_of(project, "Set.debut_eq") == {"Prob.debut"}


def test_open_resolves_relative_to_other_opens(make_project):
    project = make_project({
        "Lib/Factory.lean": """
            namespace Lib.SymCC.Factory
            def noneOf : Nat := 0
            end Lib.SymCC.Factory
            """,
        "Lib/Use.lean": """
            import Lib.Factory

            namespace Lib.Thm
            open SymCC Factory

            theorem t : noneOf = 0 := rfl
            end Lib.Thm

            def none : Nat := 1

            theorem u : Option.none = (none : Option Nat) := rfl
            """,
    })
    assert deps_of(project, "Lib.Thm.t") == {"Lib.SymCC.Factory.noneOf"}


def test_scoped_notation_applies_where_its_namespace_is_open(make_project):
    project = make_project({
        "Lib/Defs.lean": """
            def defaultD (a : Nat) : Nat := a

            namespace ShortVariables
            scoped notation "D" => defaultD 4
            end ShortVariables
            """,
        "Lib/Open.lean": """
            import Lib.Defs
            open scoped ShortVariables

            theorem t : D = 4 := rfl
            """,
        "Lib/Closed.lean": """
            import Lib.Defs

            theorem u (D : Nat) : D = D := rfl
            """,
    })
    assert deps_of(project, "t") == {"defaultD"}
    assert deps_of(project, "u") == set()


def test_name_literals_are_not_references(make_project):
    project = make_project({"A.lean": """
        def foo : Nat := 0
        def names : List String := [toString `foo, toString ``foo, toString (decl_name% foo)]
        """})
    assert deps_of(project, "names") == set()


def test_monadic_let_binds_only_its_pattern():
    assert local_binder_names("let (goal, steps) ← destructCore input md") == {"goal", "steps"}
    assert local_binder_names("let opts <- elabOptions t") == {"opts"}


def test_field_notation_on_a_typed_argument(make_project):
    project = make_project({"A.lean": """
        structure Goal where
          id : Nat

        def Goal.priority (g : Goal) : Nat := g.id

        def score (g : Goal) (h : g.id ≤ 3) : Nat := g.priority + 1
        """})
    assert deps_of(project, "score") == {"Goal", "Goal.priority"}


def test_field_notation_on_a_typed_variable(make_project):
    project = make_project({"A.lean": """
        def List.sum' (l : List Nat) : Nat := l.foldl (· + ·) 0

        variable {l : List Nat} (h : 1 ≤ 2)

        theorem t : l.sum' = l.sum' := rfl
        """})
    assert deps_of(project, "t") == {"List.sum'"}
