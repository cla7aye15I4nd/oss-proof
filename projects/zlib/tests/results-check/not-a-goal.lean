import ZlibF.ResultsCheck
/-! Fails: a listed name is a definition that is not a goal. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
def notGoal : Nat := 0
end Fixture

#eval checkWith [] [``Fixture.Goal.a, ``Fixture.notGoal] [] (fun _ n => n.getRoot == `Fixture)
