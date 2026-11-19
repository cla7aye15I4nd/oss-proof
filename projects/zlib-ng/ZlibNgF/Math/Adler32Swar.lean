import ZlibNgF.Math.Adler32

/-!
# Lane arithmetic of the SWAR Adler-32 kernel (`ZlibNgF`)

Heap-free facts behind `adler32_swar` (`adler32_p.h`): the unreduced Adler-32 sums of whole 8-byte groups in
terms of per-position byte sums `gsD` and their prefix sums `psD`, bounds on those sums, the 16-bit lane
layout of 64-bit words, and the fixed-point multiplications of the kernel's final reduction.
-/

set_option autoImplicit false

namespace ZlibNgF.Math.Adler32Swar
open ZlibNgF.Math.Adler32

/-- Sum of byte `j` of each of the first `t` 8-byte groups of `xs`. -/
noncomputable def gs (xs : List UInt8) : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, j => gs xs t j + (xs.getD (8 * t + j) 0).toNat

/-- Prefix sums of `gs`: `ps t j = Σ_{u < t} gs u j`. -/
noncomputable def ps (xs : List UInt8) : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, j => ps xs t j + gs xs t j

/-- `tri t = 0 + 1 + ... + (t - 1)`. -/
noncomputable def tri : Nat → Nat
  | 0 => 0
  | t + 1 => tri t + t

theorem tri_le : ∀ t, t ≤ 23 → tri t ≤ 253 := by decide

theorem gs_le (xs : List UInt8) : ∀ t j, gs xs t j ≤ 255 * t := by
  intro t j
  induction t with
  | zero => simp [gs]
  | succ t ih =>
    simp only [gs]
    have : (xs.getD (8 * t + j) 0).toNat < 256 := (xs.getD (8 * t + j) 0).toNat_lt
    omega

theorem ps_le (xs : List UInt8) : ∀ t j, ps xs t j ≤ 255 * tri t := by
  intro t j
  induction t with
  | zero => simp [ps, tri]
  | succ t ih =>
    simp only [ps, tri]
    have := gs_le xs t j
    omega

theorem take8 : ∀ (ys : List UInt8), 8 ≤ ys.length →
    ys.take 8 = [ys.getD 0 0, ys.getD 1 0, ys.getD 2 0, ys.getD 3 0, ys.getD 4 0, ys.getD 5 0, ys.getD 6 0,
      ys.getD 7 0]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ => rfl
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | [_, _, _, _], h => by simp at h
  | [_, _, _, _, _], h => by simp at h
  | [_, _, _, _, _, _], h => by simp at h
  | [_, _, _, _, _, _, _], h => by simp at h

theorem getD_drop (xs : List UInt8) (n j : Nat) : (xs.drop n).getD j 0 = xs.getD (n + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The unreduced sums of `8 t` bytes, group by group. -/
theorem rawSums_groups (xs : List UInt8) (a s : Nat) : ∀ t, 8 * t ≤ xs.length →
    rawSums (a, s) (xs.take (8 * t)) =
      (a + (gs xs t 0 + gs xs t 1 + gs xs t 2 + gs xs t 3 + gs xs t 4 + gs xs t 5 + gs xs t 6 + gs xs t 7),
       s + 8 * t * a +
         8 * (ps xs t 0 + ps xs t 1 + ps xs t 2 + ps xs t 3 + ps xs t 4 + ps xs t 5 + ps xs t 6 + ps xs t 7) +
         (8 * gs xs t 0 + 7 * gs xs t 1 + 6 * gs xs t 2 + 5 * gs xs t 3 +
          4 * gs xs t 4 + 3 * gs xs t 5 + 2 * gs xs t 6 + gs xs t 7)) := by
  intro t
  induction t with
  | zero => intro _; simp [gs, ps]
  | succ t ih =>
    intro hle
    have ih' := ih (by omega)
    have hsplit : xs.take (8 * (t + 1)) =
        xs.take (8 * t) ++
          [xs.getD (8 * t + 0) 0, xs.getD (8 * t + 1) 0, xs.getD (8 * t + 2) 0, xs.getD (8 * t + 3) 0,
           xs.getD (8 * t + 4) 0, xs.getD (8 * t + 5) 0, xs.getD (8 * t + 6) 0, xs.getD (8 * t + 7) 0] := by
      rw [show 8 * (t + 1) = 8 * t + 8 by omega, List.take_add, take8 _ (by simp; omega)]
      simp only [getD_drop]
    rw [hsplit, rawSums_append, ih']
    simp only [rawSums_cons, rawSums_nil, rawStep, gs, ps, Nat.add_zero]
    have e1 : 8 * (t + 1) * a = 8 * t * a + 8 * a := by rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    apply Prod.ext <;> dsimp only <;> omega

/-! ## 16-bit lanes of 64-bit words -/

/-- `x &&& m` from the 16-bit low part and the rest. -/
theorem land_split16 (x m : Nat) :
    x &&& m = ((x % 2 ^ 16) &&& (m % 2 ^ 16)) + 2 ^ 16 * ((x / 2 ^ 16) &&& (m / 2 ^ 16)) := by
  have h1 := Nat.mod_add_div (x &&& m) (2 ^ 16)
  rw [Nat.and_mod_two_pow, Nat.and_div_two_pow] at h1
  omega

/-- `x &&& 0x00FF00FF00FF00FF` keeps byte `2k` of `x` in lane `k`. -/
theorem land_even_mask (x : Nat) :
    x &&& 0x00FF00FF00FF00FF =
      x % 256 + 2 ^ 16 * (x / 2 ^ 16 % 256) + 2 ^ 32 * (x / 2 ^ 32 % 256) + 2 ^ 48 * (x / 2 ^ 48 % 256) := by
  have k255 : ∀ y, y % 2 ^ 16 &&& 255 = y % 256 := by
    intro y
    rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [land_split16]
  rw [show (0x00FF00FF00FF00FF : Nat) % 2 ^ 16 = 255 from rfl, k255,
    show (0x00FF00FF00FF00FF : Nat) / 2 ^ 16 = 0x00FF00FF00FF from rfl, land_split16,
    show (0x00FF00FF00FF : Nat) % 2 ^ 16 = 255 from rfl, k255,
    show (0x00FF00FF00FF : Nat) / 2 ^ 16 = 0x00FF00FF from rfl, land_split16,
    show (0x00FF00FF : Nat) % 2 ^ 16 = 255 from rfl, k255,
    show (0x00FF00FF : Nat) / 2 ^ 16 = 0x00FF from rfl]
  have hlast : x / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 &&& 0x00FF = x / 2 ^ 48 % 256 := by
    rw [show (0x00FF : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hlast]
  omega

/-- `x &&& 0xFFFF0000FFFF` keeps lanes 0 and 2 of `x`. -/
theorem land_lane02 (x : Nat) :
    x &&& 0xFFFF0000FFFF = x % 2 ^ 16 + 2 ^ 32 * (x / 2 ^ 32 % 2 ^ 16) := by
  have k : ∀ y, y % 2 ^ 16 &&& 0xFFFF = y % 2 ^ 16 := by
    intro y
    rw [show (0xFFFF : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have k0 : ∀ y, y % 2 ^ 16 &&& 0 = 0 := fun y => Nat.and_zero _
  rw [land_split16]
  rw [show (0xFFFF0000FFFF : Nat) % 2 ^ 16 = 0xFFFF from rfl, k,
    show (0xFFFF0000FFFF : Nat) / 2 ^ 16 = 0xFFFF0000 from rfl, land_split16,
    show (0xFFFF0000 : Nat) % 2 ^ 16 = 0 from rfl, k0,
    show (0xFFFF0000 : Nat) / 2 ^ 16 = 0xFFFF from rfl]
  have hlast : x / 2 ^ 16 / 2 ^ 16 &&& 0xFFFF = x / 2 ^ 32 % 2 ^ 16 := by
    rw [show (0xFFFF : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hlast]
  omega

/-! ## The fixed-point multiplications of the final reduction -/

/-- `((l0 + 2^16 l1 + 2^32 l2 + 2^48 l3) * 0x1000100010001 mod 2^64) >> 48 = l0 + l1 + l2 + l3`. -/
theorem hsum_lanes (l0 l1 l2 l3 : Nat) (h : l0 + l1 + l2 + l3 < 2 ^ 16) :
    (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x1000100010001 % 2 ^ 64 / 2 ^ 48 = l0 + l1 + l2 + l3 := by
  have e : (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x1000100010001 =
      (l0 + 2 ^ 16 * (l0 + l1) + 2 ^ 32 * (l0 + l1 + l2) + 2 ^ 48 * (l0 + l1 + l2 + l3)) +
        2 ^ 64 * (l1 + l2 + l3 + 2 ^ 16 * (l2 + l3) + 2 ^ 32 * l3) := by
    simp only [Nat.reducePow]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
  simp only [Nat.reducePow]
  omega

/-- `((l0 + 2^16 l1 + 2^32 l2 + 2^48 l3) * 0x4000300020001 mod 2^64) >> 48 = 4 l0 + 3 l1 + 2 l2 + l3`. -/
theorem w4_lanes (l0 l1 l2 l3 : Nat) (h0 : l0 < 5866) (h1 : l1 < 5866) (h2 : l2 < 5866) (h3 : l3 < 5866) :
    (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x4000300020001 % 2 ^ 64 / 2 ^ 48 =
      4 * l0 + 3 * l1 + 2 * l2 + l3 := by
  have e : (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x4000300020001 =
      (l0 + 2 ^ 16 * (2 * l0 + l1) + 2 ^ 32 * (3 * l0 + 2 * l1 + l2) + 2 ^ 48 * (4 * l0 + 3 * l1 + 2 * l2 + l3)) +
        2 ^ 64 * (4 * l1 + 3 * l2 + 2 * l3 + 2 ^ 16 * (4 * l2 + 3 * l3) + 2 ^ 32 * (4 * l3)) := by
    simp only [Nat.reducePow]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
  simp only [Nat.reducePow]
  omega

/-- `((l0 + 2^16 l1 + 2^32 l2 + 2^48 l3) * 0x3000200010000 mod 2^64) >> 48 = 3 l0 + 2 l1 + l2`. -/
theorem w3_lanes (l0 l1 l2 l3 : Nat) (h0 : l0 < 5866) (h1 : l1 < 5866) (h2 : l2 < 5866) :
    (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x3000200010000 % 2 ^ 64 / 2 ^ 48 =
      3 * l0 + 2 * l1 + l2 := by
  have e : (l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3) * 0x3000200010000 =
      (2 ^ 16 * l0 + 2 ^ 32 * (2 * l0 + l1) + 2 ^ 48 * (3 * l0 + 2 * l1 + l2)) +
        2 ^ 64 * (3 * l1 + 2 * l2 + l3 + 2 ^ 16 * (3 * l2 + 2 * l3) + 2 ^ 32 * (3 * l3)) := by
    simp only [Nat.reducePow]; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simp only [Nat.reducePow]; omega)]
  simp only [Nat.reducePow]
  omega

/-- `((lo + 2^32 hi) * 0x800000008 mod 2^64) >> 32 ≡ 8 (lo + hi) (mod 2^32)` for `lo < 2^29`. -/
theorem x8_slots (lo hi : Nat) (hlo : lo < 2 ^ 29) :
    (lo + 2 ^ 32 * hi) * 0x800000008 % 2 ^ 64 / 2 ^ 32 % 2 ^ 32 = 8 * (lo + hi) % 2 ^ 32 := by
  have e : (lo + 2 ^ 32 * hi) * 0x800000008 =
      (8 * lo + 2 ^ 32 * (8 * (lo + hi) % 2 ^ 32)) + 2 ^ 64 * (8 * hi + 8 * (lo + hi) / 2 ^ 32) := by
    simp only [Nat.reducePow]; omega
  have hr : 8 * (lo + hi) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hlt : 8 * lo + 2 ^ 32 * (8 * (lo + hi) % 2 ^ 32) < 2 ^ 64 := by
    have : 2 ^ 32 * (8 * (lo + hi) % 2 ^ 32) ≤ 2 ^ 32 * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.reducePow] at this hr ⊢; omega
  have h8 : 8 * lo < 2 ^ 32 := by simp only [Nat.reducePow] at hlo ⊢; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt h8, Nat.zero_add, Nat.mod_mod]

end ZlibNgF.Math.Adler32Swar
