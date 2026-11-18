import ZlibF.ResultsCheck
/-! Fails: `Goal.c` is in neither list. -/
open Lean ZlibF.Results

namespace Fixture
def Goal.a : Prop := True
theorem a_proof : Goal.a := trivial
def Goal.b (n : Nat) : Prop := n = n
theorem b_proof : ∀ n, Goal.b n := fun _ => rfl
def Goal.c : Prop := False
end Fixture

#eval checkWith [(``Fixture.Goal.a, ``Fixture.a_proof), (``Fixture.Goal.b, ``Fixture.b_proof)]
  [] [] (fun _ n => n.getRoot == `Fixture)
