import Lean
open Lean

/-!
# Fast-gate check: no forbidden declaration in the library

Every declaration of a `ZlibF` module is rejected when the compiled environment says it is

- unsafe or partial, except the reviewed compiler auxiliaries of `tests/audit/compiler-helpers.txt`.
  A recursive `def` whose compiled code needs an `_unsafe_rec` helper is caught here, on every
  push; marking the definition `noncomputable` removes the helper
  and leaves kernel reduction unchanged;
- an axiom or an opaque constant;
- marked `@[implemented_by]` or `@[extern]`;
- a direct user of an axiom other than `propext`, `Classical.choice` and `Quot.sound`: its type or
  its value names the axiom. A `sorry` names `sorryAx` and `native_decide` names
  `Lean.ofReduceBool` in the declaration that holds it, and that declaration is in the library, so
  both are found here. The reviewed compiler auxiliaries are not exempt from the last three rules.

Not checked here: an axiom reached only through a declaration of another package. The check of
`ZlibF/Results.lean` computes the full axiom closure (`Lean.collectAxioms`) of every theorem that
proves a goal; this check reads each declaration of the library once.

Run after the library build: `lake env lean --run tests/audit/PartialCheck.lean`.
-/

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The constants a declaration names: the same edges as `Lean.CollectAxioms`. -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants

def readNames (path : System.FilePath) : IO NameSet := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := {}) fun s line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then s else s.insert line.toName

def main : IO UInt32 := do
  let helpers ← readNames "tests/audit/compiler-helpers.txt"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
  -- Read the checked constants, with the bodies that an exporting view hides.
  let env := env.setExporting false
  let kernel := env.checked.get
  let mut problems : Array String := #[]
  let mut recursive := false
  let mut count := 0
  for (n, ci) in kernel.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i]!).getRoot == `ZlibF
      | none => false
    unless ours do continue
    count := count + 1
    if !helpers.contains n then
      if ci.isUnsafe then problems := problems.push s!"unsafe declaration {n}"; recursive := true
      if ci.isPartial then problems := problems.push s!"partial declaration {n}"; recursive := true
    match ci with
    | .axiomInfo _ => problems := problems.push s!"axiom {n}"
    | .opaqueInfo _ => problems := problems.push s!"opaque constant {n}"
    | _ => pure ()
    if (Compiler.getImplementedBy? env n).isSome then problems := problems.push s!"implemented_by on {n}"
    if isExtern env n then problems := problems.push s!"extern on {n}"
    let mut seen : NameSet := {}
    for used in usedConstants ci do
      if seen.contains used || allowedAxioms.contains used then continue
      seen := seen.insert used
      if let some (.axiomInfo _) := kernel.find? used then
        problems := problems.push s!"{n} uses the axiom {used}"
  if count == 0 then problems := problems.push "no declaration of ZlibF was read"
  for p in problems.qsort (· < ·) do IO.println s!"PROBLEM: {p}"
  if problems.isEmpty then
    IO.println s!"{count} declarations of ZlibF: no unsafe or partial declaration outside the reviewed compiler auxiliaries, no axiom, opaque constant, implemented_by or extern, and no use of an axiom outside the allowed three"
    return 0
  if recursive then
    IO.println "mark the recursive definition noncomputable (or review it into tests/audit/compiler-helpers.txt)"
  return 1
