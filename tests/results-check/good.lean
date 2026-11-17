import ZlibF.ResultsCheck
/-! Passes: two goals proved (one with a binder), one not done, one required. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.b (n : Nat) : Prop := n = n
theorem b_proof : ∀ n, Goal.b n := fun _ => rfl
def Goal.c : Prop := False
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof), (``Fixture.Goal.b, ``Fixture.b_proof)]
  [``Fixture.Goal.c] [``Fixture.Goal.a] (fun _ n => n.getRoot == `Fixture)
