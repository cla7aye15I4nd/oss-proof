import ZlibF.ResultsCheck
/-! Fails: a listed goal is outside the scope searched, so fewer goals are defined than listed. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
end Fixture
namespace Outside
def Goal.c : Prop := False
end Outside

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [``Outside.Goal.c] [] (fun _ n => n.getRoot == `Fixture)
