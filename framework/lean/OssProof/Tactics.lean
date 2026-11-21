import OssProof.Frame

/-!
# Shared Kernel-Checked Proof Helpers & Tactics (`OssProof.Tactics`)

Pure kernel-checked helpers (zero `bv_decide`, zero `native_decide`, zero extra axioms):
- standard fixed-width integer injectivity lemmas (eliminating per-file private duplicates),
- `c_arith`: thin wrapper around Lean 4.36's built-in `grind` + `omega` for bounded C integer and
  shift arithmetic,
- `freeze h := e`: clean WHNF-barrier replacement for manual
  `obtain ⟨h, hdef⟩ : ∃ x, x = e := ⟨_, rfl⟩`.
-/

namespace OssProof

theorem u8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b := by grind
theorem u16_eq_of_toNat {a b : UInt16} (h : a.toNat = b.toNat) : a = b := by grind
theorem u32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := by grind
theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by grind
theorem i32_eq_of_toInt {a b : Int32} (h : a.toInt = b.toInt) : a = b := by grind
theorem i64_eq_of_toInt {a b : Int64} (h : a.toInt = b.toInt) : a = b := by grind

/-- Freeze an expression behind a fresh existential variable + equality to prevent zeta-reduction
from triggering WHNF blowups on large struct update chains. -/
macro "freeze " x:ident " , " hx:ident " := " e:term : tactic =>
  `(tactic| have ⟨$x, $hx⟩ : ∃ v, v = $e := ⟨_, rfl⟩)

/-- Pure kernel-checked C integer/bounds arithmetic solver backed by Lean 4.36's `grind`/`omega`. -/
macro "c_arith" : tactic =>
  `(tactic| first | grind | omega)

end OssProof
