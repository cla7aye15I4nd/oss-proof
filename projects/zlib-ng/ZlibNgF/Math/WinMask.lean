/-!
# Rounding down to a multiple of a power of two (`ZlibNgF`)

`x & ~(w - 1)` on `uint32_t`, with `w = 2^k`, is `x` rounded down to a multiple of `w` (`fill_window`'s
`slide_len`).
-/

set_option autoImplicit false

namespace ZlibNgF.Math.WinMask

theorem nat_and_high (x k : Nat) (hk : k ≤ 32) (hx : x < 2 ^ 32) :
    x &&& (2 ^ (32 - k) - 1) * 2 ^ k = x / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : k ≤ j
  · by_cases h2 : j < 32
    · have e : j - k + k = j := by omega
      simp [h1, show j - k < 32 - k by omega, e]
    · have : x.testBit j = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right
        (by decide) (by omega)))
      have e : j - k + k = j := by omega
      simp [this, e]
  · simp [h1]

theorem round_down (x w : UInt32) (k : Nat) (hw : w.toNat = 2 ^ k) (hk : k ≤ 31) :
    (x &&& ~~~(w - 1)).toNat = x.toNat - x.toNat % 2 ^ k := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp2 : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hk
  have e1 : (w - 1).toNat = 2 ^ k - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hw]; simp; omega), hw]; rfl
  have e2 : (2 : Nat) ^ 32 - 1 - (2 ^ k - 1) = (2 ^ (32 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, ← Nat.pow_add, show 32 - k + k = 32 by omega, Nat.one_mul]; omega
  rw [UInt32.toNat_and, UInt32.toNat_not, e1, show UInt32.size = 2 ^ 32 from rfl, e2,
    nat_and_high _ _ (by omega) x.toNat_lt]
  have := Nat.div_add_mod x.toNat (2 ^ k)
  rw [Nat.mul_comm] at this
  omega

/-- The slide of `fill_window`: with `w = 2^k` (`k` in 9..15), the window size `ws = max(2 w, 32768)`, the data end
`fe` a multiple of `w` minus `MIN_LOOKAHEAD` (262) past `ws - 262`, reached from a value `fe0` within the window by
steps of `w` (`fe ≤ ss + w`), `ss < fe` and `ss + la ≤ ws`, the slide `sl = x - x % w` with
`x = ss - (w - 262)` is a multiple of `w` at most `ss`, at least half the data, and leaves `fe - sl` within the
window. -/
theorem slide_math (k w ws fe0 fe ss la : Nat) (hk1 : 9 ≤ k) (hk2 : k ≤ 15) (hw : w = 2 ^ k)
    (hws : ws = if 2 * w > 32768 then 2 * w else 32768) (hm : (fe + 262) % w = 0) (h0 : fe0 + 262 ≤ ws)
    (hfe : fe = fe0 ∨ fe ≤ ss + w) (hs : ss < fe) (hl : ss + la ≤ ws) (hgt : ws < fe + 262) :
    w - 262 ≤ ss ∧ (ss - (w - 262)) - (ss - (w - 262)) % w ≤ ss ∧
      ss + la ≤ 2 * ((ss - (w - 262)) - (ss - (w - 262)) % w) ∧ (ss - (w - 262)) - (ss - (w - 262)) % w ≤ fe ∧
      (fe - ((ss - (w - 262)) - (ss - (w - 262)) % w) + 262) % w = 0 ∧
      fe - ((ss - (w - 262)) - (ss - (w - 262)) % w) + 262 ≤ ws ∧
      (ss - (w - 262)) - (ss - (w - 262)) % w ≤ 65536 := by
  have hfe' : fe ≤ ss + w := by rcases hfe with rfl | h <;> omega
  have : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> subst hw <;> simp at hws <;> subst hws <;> omega

/-- `fill_end += w_size` keeps `fill_end + MIN_LOOKAHEAD` a multiple of `w_size`. -/
theorem fe_step (fe w : Nat) (hm : (fe + 262) % w = 0) : (fe + w + 262) % w = 0 := by
  rw [show fe + w + 262 = fe + 262 + w by omega, Nat.add_mod_right]; exact hm

end ZlibNgF.Math.WinMask
