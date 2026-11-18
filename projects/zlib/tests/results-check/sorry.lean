import ZlibF.ResultsCheck
/-! Fails: the theorem is proved by sorry. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := sorry
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [] [] (fun _ n => n.getRoot == `Fixture)
