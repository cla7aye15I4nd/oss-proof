import ZlibF.ResultsCheck
/-! Fails: a goal is listed twice (once proved, once not done). -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [``Fixture.Goal.a] [] (fun _ n => n.getRoot == `Fixture)
