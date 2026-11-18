import Lean
open Lean

/-!
# Compiled-environment audit: no forbidden declaration in `<Package>`

Usage (from `projects/<id>/` after `lake build`):
  `lake env lean --run ../../framework/lean/PartialCheck.lean <Package> [compiler-helpers.txt]`

Every declaration of a `<Package>` module is rejected when the compiled kernel environment says it is:
- `unsafe` or `partial`, except reviewed compiler auxiliaries listed in `compiler-helpers.txt`;
- an `axiom` or `opaque` constant;
- marked `@[implemented_by]` or `@[extern]`;
- a direct user of an axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
-/

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

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
  if !(← path.pathExists) then return {}
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := {}) fun s line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then s else s.insert line.toName

def main (args : List String) : IO UInt32 := do
  let pkgStr :: rest := args | do
    IO.eprintln "usage: PartialCheck.lean <Package> [compiler-helpers.txt]"
    return 2
  let pkg := pkgStr.toName
  let helpers ← match rest with
    | h :: _ => readNames h
    | [] => pure {}
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := pkg }] {} 0
  let env := env.setExporting false
  let kernel := env.checked.get
  let mut problems : Array String := #[]
  let mut recursive := false
  let mut count := 0
  for (n, ci) in kernel.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i]!).getRoot == pkg
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
  if count == 0 then problems := problems.push s!"no declaration of {pkg} was read"
  for p in problems.qsort (· < ·) do IO.println s!"PROBLEM: {p}"
  if problems.isEmpty then
    IO.println s!"{count} declarations of {pkg}: no unsafe or partial declaration outside the reviewed compiler auxiliaries, no axiom, opaque constant, implemented_by or extern, and no use of an axiom outside the allowed three"
    return 0
  if recursive then
    IO.println "mark the recursive definition noncomputable (or review it into compiler-helpers.txt)"
  return 1
