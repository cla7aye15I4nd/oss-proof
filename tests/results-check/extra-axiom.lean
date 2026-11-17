import ZlibF.ResultsCheck
/-! Fails: the theorem paired with `Goal.a` depends on an axiom other than the three allowed. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.b (n : Nat) : Prop := n = n
theorem b_proof : ∀ n, Goal.b n := fun _ => rfl
def Goal.c : Prop := False
axiom extra : Goal.a
theorem a_axiom : Goal.a := extra
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_axiom), (``Fixture.Goal.b, ``Fixture.b_proof)]
  [``Fixture.Goal.c] [] (fun _ n => n.getRoot == `Fixture)
