import ZlibF.ResultsCheck
/-! Fails: the theorem reaches an axiom only through a lemma. -/
open Lean ZlibF.Results

namespace Fixture
axiom extra : False
theorem helper : True := extra.elim
def Goal.a : Prop := True
theorem a_proof : Goal.a := helper
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof)] [] [] (fun _ n => n.getRoot == `Fixture)
