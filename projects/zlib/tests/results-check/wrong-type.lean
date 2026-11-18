import ZlibF.ResultsCheck
/-! Fails: the theorem paired with `Goal.a` has the type `True`, not exactly `Goal.a`. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.b (n : Nat) : Prop := n = n
theorem b_proof : ∀ n, Goal.b n := fun _ => rfl
def Goal.c : Prop := False
theorem a_true : True := trivial
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_true), (``Fixture.Goal.b, ``Fixture.b_proof)]
  [``Fixture.Goal.c] [] (fun _ n => n.getRoot == `Fixture)
