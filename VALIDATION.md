# Validation

How closely the parser's output matches the ground truth held by the Lean 4 kernel, on nineteen
public Lean projects. Every number here comes from
[`validation/verify.py`](validation/verify.py) and can be reproduced with it
([see below](#reproducing)).

## Method

Each project is built with `lake build`. A Lean script
([`validation/lean_kernel_deps.lean`](validation/lean_kernel_deps.lean)) then dumps every
constant in the project's own modules, with its source range and the constants its type and
value use. Each kernel constant is sorted by the source text its range points at:

- **Supported:** written with a command the parser handles (`theorem`, `lemma`, `def`,
  `abbrev`, `structure`, `class`, `axiom`, named `instance` and `alias`). These are the
  ground truth.
- **Unsupported:** written with a command the parser does not handle (anonymous
  `instance`, `inductive`, `notation`, `macro`, ...). These are excluded.
- **Generated:** never written in the source: constructors, recursors, projections,
  auxiliary and equation lemmas, `to_additive` siblings. These are excluded and
  *contracted*: their dependencies are inlined into whatever refers to them. A structure is
  credited with its constructor's dependencies (its fields and parents), and a `partial def`
  with those of its `_unsafe_rec` body.

The parser runs on the same source, and its output is compared with the ground truth in two
ways:

- **Declarations:** does it find the same declarations, by fully qualified name?
- **Edges:** among the declarations both sides agree on, does it report the same
  dependencies? Only dependencies within the project count, since the parser cannot see into
  Mathlib or core by construction.

Only modules the project's default build target compiles are analysed.

## Results

The first eleven projects were measured in October 2026 on their main branch, and the other
eight at commits from December 2025 to March 2026:

| project | commit | modules | ground-truth declarations |
|---|---|---|---|
| [PFR](https://github.com/teorth/pfr) | `d91e4678` | 71 / 71 | 1007 |
| [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | `127b50e` | 104 / 235 | 2810 |
| [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | `0921599` | 1952 / 1963 | 11876 |
| [Carleson](https://github.com/fpvandoorn/carleson) | `c9fba45` | 121 / 123 | 3040 |
| [Analysis I](https://github.com/teorth/analysis) | `a19a5bf` | 107 / 108 | 3817 |
| [brownian-motion](https://github.com/RemyDegenne/brownian-motion) | `546d772` | 89 / 95 | 1848 |
| [LeanCamCombi](https://github.com/YaelDillies/LeanCamCombi) | `963dc05` | 21 / 21 | 118 |
| [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean) | `cb338f2` | 45 / 89 | 334 |
| [Batteries](https://github.com/leanprover-community/batteries) | `a18b051` | 197 / 273 | 3436 |
| [Aesop](https://github.com/leanprover-community/aesop) | `29c64c5` | 132 / 250 | 1351 |
| [Cedar](https://github.com/cedar-policy/cedar-spec) (`cedar-lean`) | `301bdd2` | 304 / 386 | 5290 |
| [APAP](https://github.com/YaelDillies/apap) | `eba2c2b` | 40 / 40 | 832 |
| [Duality](https://github.com/madvorak/duality) | `99e264c` | 7 / 7 | 184 |
| [FinLin](https://github.com/roman3017/FinLin) | `613ce9e` | 2 / 2 | 15 |
| [FLT](https://github.com/ImperialCollegeLondon/FLT) | `002a19b` | 174 / 174 | 1851 |
| [OrderedSemigroups](https://github.com/ericluap/OrderedSemigroups) | `d63c01e` | 16 / 16 | 228 |
| [PDL](https://github.com/m4lvin/lean4-pdl) | `87803fe` | 34 / 59 | 1004 |
| [Sphere Packing](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | `a41e5e7` | 88 / 88 | 1611 |
| [ζ(3) irrational](https://github.com/ahhwuhu/zeta_3_irrational) | `e878531` | 8 / 8 | 131 |

Batteries and Aesop are Lean libraries for tactics and data structures, Cedar is a verified
software specification, and PDL formalises propositional dynamic logic. Mathematics in Lean
is a textbook of exercises. The rest are mathematics formalisations built on Mathlib. Between
them they span Lean releases from v4.18 (Duality and ζ(3) irrational) to v4.36.

### Declarations

| project | precision | recall | F1 |
|---|---|---|---|
| PFR | 0.994 | 1.000 | 0.997 |
| PrimeNumberTheoremAnd | 1.000 | 1.000 | 1.000 |
| formal-conjectures | 0.999 | 0.991 | 0.995 |
| Carleson | 0.999 | 1.000 | 1.000 |
| Analysis I | 1.000 | 1.000 | 1.000 |
| brownian-motion | 0.999 | 1.000 | 1.000 |
| LeanCamCombi | 1.000 | 1.000 | 1.000 |
| Mathematics in Lean | 1.000 | 0.997 | 0.999 |
| Batteries | 0.999 | 0.974 | 0.986 |
| Aesop | 0.990 | 0.976 | 0.983 |
| Cedar | 1.000 | 0.990 | 0.995 |
| APAP | 0.995 | 1.000 | 0.998 |
| Duality | 1.000 | 1.000 | 1.000 |
| FinLin | 1.000 | 1.000 | 1.000 |
| FLT | 1.000 | 1.000 | 1.000 |
| OrderedSemigroups | 1.000 | 1.000 | 1.000 |
| PDL | 1.000 | 1.000 | 1.000 |
| Sphere Packing | 0.999 | 1.000 | 0.999 |
| ζ(3) irrational | 1.000 | 1.000 | 1.000 |

### Dependency edges

*Achievable recall* is the recall over the edges whose target's name occurs in the
declaration's source text at all. It is the ceiling for any parser that reads the source
without elaborating it.

| project | kernel edges | precision | recall | F1 | achievable recall | exact dependency sets |
|---|---|---|---|---|---|---|
| PFR | 4,385 | 0.979 | 0.758 | 0.855 | 0.991 | 373 / 839 |
| PrimeNumberTheoremAnd | 5,471 | 0.988 | 0.921 | 0.953 | 0.989 | 1689 / 2030 |
| formal-conjectures | 15,579 | 0.986 | 0.817 | 0.894 | 0.976 | 7263 / 8828 |
| Carleson | 24,361 | 0.991 | 0.443 | 0.613 | 0.970 | 960 / 2607 |
| Analysis I | 15,541 | 0.969 | 0.585 | 0.730 | 0.903 | 980 / 3343 |
| brownian-motion | 5,454 | 0.979 | 0.732 | 0.837 | 0.965 | 762 / 1490 |
| LeanCamCombi | 109 | 1.000 | 0.899 | 0.947 | 0.951 | 52 / 61 |
| Mathematics in Lean | 331 | 0.940 | 0.810 | 0.870 | 1.000 | 141 / 174 |
| Batteries | 7,973 | 0.970 | 0.668 | 0.791 | 0.954 | 1276 / 2630 |
| Aesop | 6,521 | 0.972 | 0.476 | 0.639 | 0.955 | 441 / 1148 |
| Cedar | 75,834 | 0.964 | 0.420 | 0.585 | 0.959 | 1110 / 4898 |
| APAP | 2,176 | 0.924 | 0.845 | 0.882 | 0.999 | 475 / 764 |
| Duality | 954 | 0.982 | 0.522 | 0.682 | 0.988 | 31 / 165 |
| FinLin | 25 | 1.000 | 1.000 | 1.000 | 1.000 | 10 / 10 |
| FLT | 5,197 | 0.935 | 0.629 | 0.752 | 0.944 | 615 / 1450 |
| OrderedSemigroups | 1,128 | 0.994 | 0.618 | 0.762 | 0.994 | 52 / 208 |
| PDL | 6,172 | 0.951 | 0.499 | 0.655 | 0.922 | 181 / 919 |
| Sphere Packing | 4,694 | 0.973 | 0.847 | 0.905 | 0.984 | 918 / 1305 |
| ζ(3) irrational | 287 | 0.996 | 0.944 | 0.970 | 0.989 | 81 / 92 |
| **all, pooled** | **182,192** | **0.972** | **0.545** | **0.698** | **0.960** | |

Most edges the parser reports are real ones (precision 0.92–1.00). Of the edges a
source-level parser could recover at all, it finds 90–100%. Overall recall is lower where
much of what the kernel records never appears in the source text. That share is 42% of all
kernel edges in Carleson, 45% in PDL and 56% in Cedar, but only 7% in PrimeNumberTheoremAnd.

FinLin is very small (two modules, 15 declarations), so its perfect scores say little on
their own.

## Where the errors come from

`verify.py` attributes every wrong edge to a cause. Pooled over the nineteen projects:

**Missed edges (82,882):**

| cause | edges | share |
|---|---|---|
| target never written in the source: instance arguments, coercions, `variable` binders, definitions unfolded by `simp`, terms built by tactics | 74,630 | 90% |
| target reachable only through a notation declared in the project | 4,088 | 5% |
| name present and indexed, but dropped during resolution (ambiguous, or the namespace could not be determined) | 2,194 | 3% |
| target written only outside the text the parser reads (attributes, multi-line notation) | 1,206 | 1% |
| written qualified, but indexed unqualified (or vice versa) | 764 | 1% |

**Invented edges (2,902):**

| cause | edges | share |
|---|---|---|
| name occurs in the text but is not a dependency in the kernel | 2,553 | 88% |
| name does not occur in the text the parser reads | 279 | 10% |
| the declaration has no body in the kernel (an `opaque` definition) | 70 | 2% |

Not every invented edge is a parser error: a lemma passed to `simp [foo]` or `unfold foo`
uses `foo` in the source even when the proof term the kernel stores does not mention it.
The rest are mostly constructor patterns (`| .record r =>`) and field accesses that only
type information could resolve.

## Reproducing

`verify.py` needs a Lean toolchain (installed with [elan](https://github.com/leanprover/elan))
and works from a source checkout of this repository:

```bash
git clone https://github.com/teorth/pfr
uv run python validation/verify.py --build pfr -o results/
```

`--build` fetches the Mathlib build cache if the project uses Mathlib and runs `lake build`.
The script then dumps the kernel's constants and writes `SUMMARY.md` (the numbers above)
and `comparison.json` (everything, including examples of each kind of error) under
`results/<project>_<commit>/`. Several projects can be given at once, and their results are
pooled in `results/POOLED.md`.

Notes:

- **Memory.** Lake builds as many modules in parallel as there are cores, and each loads its
  imports. With many cores and little memory, cap it: `LEAN_NUM_THREADS=6` kept the largest
  project here (formal-conjectures, 1,963 modules) under 6 GB.
- **Disk.** The builds take 127 GB for the nineteen projects, mostly Mathlib build caches.
- **Re-scoring.** After the parser changes, `--skip-extract` re-scores the saved kernel
  dump in seconds, without rebuilding the project.
