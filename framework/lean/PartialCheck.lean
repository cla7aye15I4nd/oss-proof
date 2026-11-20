import Lean
open Lean

/-!
# Compiled-environment audit: no forbidden declaration in `<Package>`

Usage (from `projects/<id>/` after `lake build`):
  `lake env lean --run ../../framework/lean/PartialCheck.lean <Package> [compiler-helpers.txt]`

Every declaration of a `<Package>` module is rejected when the compiled kernel environment says it is:
- `unsafe` or `partial`, except reviewed compiler auxiliaries listed in `compiler-helpers.txt` and
  Lean 4.36+'s compiler-synthesized `Ind.ctorIdx._impl` on genuine kernel inductives;
- an `axiom` or `opaque` constant;
- marked `@[implemented_by]` (other than `Ind.ctorIdx -> Ind.ctorIdx._impl` on a kernel inductive)
  or `@[extern]`;
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

def isResultsCheckHelper (pkg : Name) (n : Name) : Bool :=
  n == pkg ++ `Results ++ `expectedType ++ `go ++ `_unsafe_rec ||
  n == pkg ++ `Results ++ `isGoalType ++ `_unsafe_rec

def readNames (path : System.FilePath) : IO NameSet := do
  if !(← path.pathExists) then return {}
  let lines := (← IO.FS.readFile path).splitOn "\n"
  return lines.foldl (init := {}) fun s line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then s else s.insert line.toName

def parseArgs (args : List String) : Except String (String × Option String × Option String) :=
  go args none none none
where
  go : List String → Option String → Option String → Option String →
      Except String (String × Option String × Option String)
    | [], some pkg, helpers, res => .ok (pkg, helpers, res)
    | [], none, _, _ => .error "usage: PartialCheck.lean <Package> [compiler-helpers.txt] [--results <ResultsMod>]"
    | "--results" :: r :: rest, pkg, helpers, _ => go rest pkg helpers (some r)
    | "--results" :: [], _, _, _ => .error "missing module name after --results"
    | a :: rest, none, helpers, res => go rest (some a) helpers res
    | a :: rest, some pkg, none, res => go rest (some pkg) (some a) res
    | a :: _, some _, some _, _ => .error s!"unexpected extra argument: {a}"

def main (args : List String) : IO UInt32 := do
  let (pkgStr, helpersOpt, resultsOpt) ← match parseArgs args with
    | .ok v => pure v
    | .error msg =>
      IO.eprintln msg
      return 2
  let pkg := pkgStr.toName
  let helpers ← match helpersOpt with
    | some h => readNames h
    | none => pure {}
  initSearchPath (← findSysroot)
  let imports : Array Import :=
    match resultsOpt with
    | some r => #[{ module := pkg }, { module := r.toName }]
    | none => #[{ module := pkg }]
  let env ← importModules imports {} 0
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
    if !helpers.contains n && !isInductiveCtorIdxImpl kernel n && !isResultsCheckHelper pkg n then
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
  if count == 0 then problems := problems.push s!"no declaration of {pkg} was read"
  for p in problems.qsort (· < ·) do IO.println s!"PROBLEM: {p}"
  if problems.isEmpty then
    IO.println s!"{count} declarations of {pkg}: no unsafe or partial declaration outside the reviewed compiler auxiliaries, no axiom, opaque constant, implemented_by or extern, and no use of an axiom outside the allowed three"
    return 0
  if recursive then
    IO.println "mark the recursive definition noncomputable (or review it into compiler-helpers.txt)"
  return 1
