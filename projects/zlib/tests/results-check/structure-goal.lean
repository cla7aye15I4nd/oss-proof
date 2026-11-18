import ZlibF.ResultsCheck
/-! Fails: a proposition declared as a structure under a goal name would escape the count. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
structure Goal.e : Prop where
  impossible : False
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [] [] (fun _ n => n.getRoot == `Fixture)
