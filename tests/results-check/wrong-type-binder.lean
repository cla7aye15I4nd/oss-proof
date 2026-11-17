import ZlibF.ResultsCheck
/-! Fails: the theorem paired with a goal with a binder states something else. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.b (n : Nat) : Prop := n = n
theorem b_other : ∀ n : Nat, n + 0 = n := fun _ => rfl
end Fixture

#eval checkWith [(``Fixture.Goal.b, ``Fixture.b_other)] [] [] (fun _ n => n.getRoot == `Fixture)
