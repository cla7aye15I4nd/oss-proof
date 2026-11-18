import ZlibF.ResultsCheck
/-! Fails: the name paired with a goal is a definition, not a theorem. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
def a_def : Goal.a := trivial
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_def)] [] [] (fun _ n => n.getRoot == `Fixture)
