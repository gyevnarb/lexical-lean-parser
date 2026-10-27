/-
Dump every constant the Lean kernel holds for a repository's own modules, together with
the constants each one depends on.

This file is a template: `verify.py` substitutes the import list, the
library root names and the output path before running it with `lake env lean`. The dump is
deliberately faithful and unopinionated - every constant, every flag, every dependency -
so that the classification of what counts as a "source declaration" happens in Python,
where it can be revised without rebuilding.
-/
import Lean
-- @IMPORTS@

open Lean Elab Command Meta

/-- Where the JSONL dump is written (one JSON object per constant). -/
def outPath : String := "@OUTPUT@"

/-- Root module names belonging to the repository under analysis. -/
def libRoots : List Name := [@ROOTS@]

def isLibModule (n : Name) : Bool := libRoots.any fun r => n == r || r.isPrefixOf n

def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"
  | .inductInfo _ =>
      if isClass env ci.name then "class"
      else if isStructure env ci.name then "structure"
      else "inductive"

/-- Split the constants used by an expression into (repository-internal, external). -/
def splitDeps (lib : Std.HashSet Name) (e : Option Expr) : Array Name × Array Name := Id.run do
  match e with
  | none => (#[], #[])
  | some e =>
    let mut int : Array Name := #[]
    let mut ext : Array Name := #[]
    let mut seen : Std.HashSet Name := {}
    for c in e.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      if lib.contains c then int := int.push c else ext := ext.push c
    return (int, ext)

/-- The body of a definition or theorem. Not `ConstantInfo.value?`, which from Lean v4.33 (at
the latest; v4.29 still had them) omits theorem proofs unless `allowOpaque` is set, and that
would admit `opaque` bodies too. -/
def valueOf? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | _ => none

def jarr (a : Array Name) : Json := Json.arr (a.map fun n => Json.str (toString n))

run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let datas := env.header.moduleData

  -- Pass 1: every constant name declared in one of the repository's own modules.
  let mut libConsts : Std.HashSet Name := {}
  for i in [0:mods.size] do
    if isLibModule mods[i]! then
      for n in datas[i]!.constNames do
        libConsts := libConsts.insert n
  IO.println s!"Repository module constants: {libConsts.size}"

  -- Pass 2: dump each of them with its flags, source range and dependencies.
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  let mut nDumped := 0
  for i in [0:mods.size] do
    let m := mods[i]!
    if !isLibModule m then continue
    for ci in datas[i]!.constants do
      let n := ci.name
      let (tInt, tExt) := splitDeps libConsts (some ci.type)
      let (vInt, vExt) := splitDeps libConsts (valueOf? ci)
      let ranges ← findDeclarationRanges? n
      let rangeJson : Json := match ranges with
        | none => Json.null
        | some r => Json.mkObj [
            ("startLine", Json.num r.range.pos.line),
            ("endLine",   Json.num r.range.endPos.line),
            ("selLine",   Json.num r.selectionRange.pos.line),
            ("selCol",    Json.num r.selectionRange.pos.column)]
      let isInst ← Meta.isInstance n
      let j := Json.mkObj [
        ("module", Json.str (toString m)),
        ("name", Json.str (toString n)),
        ("userName", match privateToUserName? n with
            | some u => Json.str (toString u) | none => Json.null),
        ("kind", Json.str (kindOf env ci)),
        ("isCtor", Json.bool (ci matches .ctorInfo _)),
        ("isRec", Json.bool (ci matches .recInfo _)),
        ("isAuxRec", Json.bool (isAuxRecursor env n)),
        ("isNoConfusion", Json.bool (isNoConfusion env n)),
        ("isProj", Json.bool (env.getProjectionFnInfo? n).isSome),
        ("isInstance", Json.bool isInst),
        ("isStructure", Json.bool (isStructure env n)),
        ("isClass", Json.bool (isClass env n)),
        ("isInternalDetail", Json.bool n.isInternalDetail),
        ("isPrivate", Json.bool (privateToUserName? n).isSome),
        ("hasSorry", Json.bool (ci.type.hasSorry ||
            (match valueOf? ci with | some v => v.hasSorry | none => false))),
        ("hasValue", Json.bool (valueOf? ci).isSome),
        ("range", rangeJson),
        ("typeDepsInternal", jarr tInt),
        ("valueDepsInternal", jarr vInt),
        ("typeDepsExternal", jarr tExt),
        ("valueDepsExternal", jarr vExt)]
      h.putStrLn j.compress
      nDumped := nDumped + 1
  h.flush
  IO.println s!"Dumped {nDumped} constants"
