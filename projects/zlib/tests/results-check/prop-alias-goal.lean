import ZlibF.ResultsCheck
/-! Fails: a goal whose type is Prop only after unfolding an alias would escape the count. -/
open Lean ZlibF.Results

namespace Fixture
abbrev P := Prop
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.d : P := False
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [] [] (fun _ n => n.getRoot == `Fixture)
