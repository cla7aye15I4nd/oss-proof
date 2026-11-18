import Lean
open Lean

/-!
# Fast-gate check: no forbidden declaration in the library

Run after the library build: `lake env lean --run tests/audit/PartialCheck.lean`.
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

def isInductiveCtorIdx (kernel : Kernel.Environment) (n target : Name) : Bool :=
  match n with
  | .str ind "ctorIdx" =>
    target == .str n "_impl" && match kernel.find? ind with | some (.inductInfo _) => true | _ => false
  | _ => false

def isInductiveCtorIdxImpl (kernel : Kernel.Environment) (n : Name) : Bool :=
  match n with
  | .str (.str ind "ctorIdx") "_impl" =>
    match kernel.find? ind with | some (.inductInfo _) => true | _ => false
  | _ => false

def readNames (path : System.FilePath) : IO NameSet := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := {}) fun s line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then s else s.insert line.toName

def main : IO UInt32 := do
  let helpers ← readNames "tests/audit/compiler-helpers.txt"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ZlibF }] {} 0
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
    if !helpers.contains n && !isInductiveCtorIdxImpl kernel n then
      if ci.isUnsafe then problems := problems.push s!"unsafe declaration {n}"; recursive := true
      if ci.isPartial then problems := problems.push s!"partial declaration {n}"; recursive := true
    match ci with
    | .axiomInfo _ => problems := problems.push s!"axiom {n}"
    | .opaqueInfo _ => problems := problems.push s!"opaque constant {n}"
    | _ => pure ()
    if let some target := Compiler.getImplementedBy? env n then
      if !isInductiveCtorIdx kernel n target then
        problems := problems.push s!"implemented_by on {n}"
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
