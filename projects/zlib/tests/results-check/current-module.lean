import ZlibF.ResultsCheck
/-! Fails: an unlisted goal defined in the module being checked is seen (the scope of ZlibF/Results.lean). -/
open Lean ZlibF.Results

namespace ZlibF.FixtureLocal
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.hidden : Prop := False
end ZlibF.FixtureLocal

#eval checkWith [(``ZlibF.FixtureLocal.Goal.a, ``ZlibF.FixtureLocal.a_proof)] [] [] inLibrary
