import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `adler32.c`, `arch/generic/adler32_c.c`, and `adler32_p.h` (`ZlibNgF`)

Proves safety and exact RFC 1950 §8.2 functional correctness of `adler32_combine` and `adler32_combine64`.
The goals of `adler32` and `adler32_z` are not done here: the SWAR kernel `adler32_swar` is proved in
`adler32_c.c.kernel.lean`, the rest of `adler32_c` is not yet.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Adler32
open C ZlibNg.Adler32P ZlibNg.Adler32C ZlibNg.Adler32
open ZlibNgF.Math.Adler32 ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

/-! ## Bitwise & modular word helpers -/

private theorem u32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

private theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

private theorem u32_ofNat_toNat {n : Nat} (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  show (BitVec.ofNat 32 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem u64_ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem or_shift32 (x y : UInt32) (hx : x.toNat < 65536) (hy : y.toNat < 65536) :
    (x ||| (y <<< 16)).toNat = x.toNat + 65536 * y.toNat := by
  rw [UInt32.toNat_or, UInt32.toNat_shiftLeft]
  have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [h16]
  have hs : (y.toNat <<< 16) % (2 ^ 32) = y.toNat * 65536 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hs, Nat.or_comm,
    show y.toNat * 65536 = y.toNat <<< 16 by rw [Nat.shiftLeft_eq],
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

private theorem low16_32 (a : UInt32) : (a &&& 0xffff).toNat = a.toNat % 65536 := by
  rw [UInt32.toNat_and]
  have hf : (0xffff : UInt32).toNat = 2 ^ 16 - 1 := rfl
  rw [hf]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 16

private theorem high16_32 (a : UInt32) : ((a >>> 16) &&& (0xffff : UInt32)).toNat = (a.toNat / 65536) % 65536 := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
  have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
  have hf : (0xffff : UInt32).toNat = 2 ^ 16 - 1 := rfl
  rw [h16, hf, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem seed_high16 (seed : UInt64) :
    ((seed.toUInt32 >>> 16) &&& (0xffff : UInt32)).toNat = (seed.toNat / 65536) % 65536 := by
  rw [high16_32, UInt64.toNat_toUInt32]
  have hdiv : (seed.toNat % (2 ^ 32)) / 65536 = (seed.toNat / 65536) % 65536 := by
    have hdm := Nat.div_add_mod seed.toNat (2 ^ 32)
    have hmul : 2 ^ 32 = 65536 * 65536 := rfl
    omega
  rw [hdiv, Nat.mod_mod]

/-! ## `adler32_combine` and `adler32_combine64` -/

private theorem reduce_two_base (x : UInt32) (hx : x.toNat < 3 * 65521) :
    let x1 := if x >= ZlibNg.Adler32P.BASE then x - ZlibNg.Adler32P.BASE else x
    let x2 := if x1 >= ZlibNg.Adler32P.BASE then x1 - ZlibNg.Adler32P.BASE else x1
    x2.toNat = x.toNat % 65521 := by
  intro x1 x2
  have hb : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  have hx1 : x1.toNat = if 65521 ≤ x.toNat then x.toNat - 65521 else x.toNat := by
    dsimp [x1]
    by_cases h1 : x >= ZlibNg.Adler32P.BASE
    · have h1n : 65521 ≤ x.toNat := h1
      simp only [h1, h1n, ↓reduceIte]
      rw [UInt32.toNat_sub_of_le _ _ h1, hb]
    · have h1n : ¬ (65521 ≤ x.toNat) := h1
      simp only [h1, h1n, ↓reduceIte]
  have hx2 : x2.toNat = if 65521 ≤ x1.toNat then x1.toNat - 65521 else x1.toNat := by
    dsimp [x2]
    by_cases h2 : x1 >= ZlibNg.Adler32P.BASE
    · have h2n : 65521 ≤ x1.toNat := h2
      simp only [h2, h2n, ↓reduceIte]
      rw [UInt32.toNat_sub_of_le _ _ h2, hb]
    · have h2n : ¬ (65521 ≤ x1.toNat) := h2
      simp only [h2, h2n, ↓reduceIte]
  rw [hx2, hx1]
  by_cases c1 : 65521 ≤ x.toNat
  · simp only [c1, ↓reduceIte]
    by_cases c2 : 65521 ≤ x.toNat - 65521 <;> simp only [c2, ↓reduceIte] <;> omega
  · simp only [c1, ↓reduceIte]; omega

private theorem reduce_four_base (x : UInt32) (hx : x.toNat < 4 * 65521) :
    let x1 : UInt32 := if x >= (ZlibNg.Adler32P.BASE <<< 1) then x - (ZlibNg.Adler32P.BASE <<< 1) else x
    let x2 : UInt32 := if x1 >= ZlibNg.Adler32P.BASE then x1 - ZlibNg.Adler32P.BASE else x1
    x2.toNat = x.toNat % 65521 := by
  intro x1 x2
  have hb : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  have h2b : (ZlibNg.Adler32P.BASE <<< 1).toNat = 131042 := rfl
  have hx1 : x1.toNat = if 131042 ≤ x.toNat then x.toNat - 131042 else x.toNat := by
    dsimp [x1]
    by_cases h1 : x >= (ZlibNg.Adler32P.BASE <<< 1)
    · have h1n : 131042 ≤ x.toNat := by
        have : (ZlibNg.Adler32P.BASE <<< 1).toNat ≤ x.toNat := h1
        rw [h2b] at this; exact this
      simp only [h1, h1n, ↓reduceIte]
      rw [UInt32.toNat_sub_of_le _ _ h1, h2b]
    · have h1n : ¬ (131042 ≤ x.toNat) := by
        intro hc; apply h1
        show (ZlibNg.Adler32P.BASE <<< 1).toNat ≤ x.toNat
        rw [h2b]; exact hc
      simp only [h1, h1n, ↓reduceIte]
  have hx2 : x2.toNat = if 65521 ≤ x1.toNat then x1.toNat - 65521 else x1.toNat := by
    dsimp [x2]
    by_cases h2 : x1 >= ZlibNg.Adler32P.BASE
    · have h2n : 65521 ≤ x1.toNat := h2
      simp only [h2, h2n, ↓reduceIte]
      rw [UInt32.toNat_sub_of_le _ _ h2, hb]
    · have h2n : ¬ (65521 ≤ x1.toNat) := h2
      simp only [h2, h2n, ↓reduceIte]
  rw [hx2, hx1]
  by_cases c1 : 131042 ≤ x.toNat
  · simp only [c1, ↓reduceIte]
    by_cases c2 : 65521 ≤ x.toNat - 131042 <;> simp only [c2, ↓reduceIte] <;> omega
  · simp only [c1, ↓reduceIte]
    by_cases c2 : 65521 ≤ x.toNat <;> simp only [c2, ↓reduceIte] <;> omega

private theorem int64_mod_65521_of_nat (len2 : Int64) (n : Nat) (h : len2.toInt = (n : Int)) :
    (len2 % 65521).toUInt64.toUInt32.toNat = n % 65521 := by
  have hn_lt : n < 2 ^ 63 := by
    have := Int64.toInt_lt len2
    omega
  have hlen_eq : len2 = Int64.ofNat n := by
    have h2 : (Int64.ofNat n).toInt = (n : Int) := Int64.toInt_ofNat_of_lt hn_lt
    exact Int64.toInt_inj.mp (h.trans h2.symm)
  subst hlen_eq
  have hb_srem : (Int64.ofNat n % 65521).toBitVec = BitVec.srem (BitVec.ofNat 64 n) (BitVec.ofNat 64 65521) := rfl
  have hmsb1 : (BitVec.ofNat 64 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    omega
  have hmsb2 : (BitVec.ofNat 64 65521).msb = false := by decide
  have hsrem : BitVec.srem (BitVec.ofNat 64 n) (BitVec.ofNat 64 65521) =
      BitVec.umod (BitVec.ofNat 64 n) (BitVec.ofNat 64 65521) := by
    unfold BitVec.srem
    rw [hmsb1, hmsb2]
  have hnat64 : (Int64.ofNat n % 65521).toUInt64.toNat = n % 65521 := by
    show (Int64.ofNat n % 65521).toBitVec.toNat = n % 65521
    rw [hb_srem, hsrem]
    show (BitVec.ofNat 64 n).toNat % (65521#64).toNat = n % 65521
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    rfl
  rw [UInt64.toNat_toUInt32, hnat64]
  exact Nat.mod_eq_of_lt (by omega)

private def finishCombinePure (u1 u2 : UInt32) : UInt32 :=
  let sum1_1 := if u1 >= ZlibNg.Adler32P.BASE then u1 - ZlibNg.Adler32P.BASE else u1
  let sum1_2 := if sum1_1 >= ZlibNg.Adler32P.BASE then sum1_1 - ZlibNg.Adler32P.BASE else sum1_1
  let sum2_1 := if u2 >= (ZlibNg.Adler32P.BASE <<< 1) then u2 - (ZlibNg.Adler32P.BASE <<< 1) else u2
  let sum2_2 := if sum2_1 >= ZlibNg.Adler32P.BASE then sum2_1 - ZlibNg.Adler32P.BASE else sum2_1
  sum1_2 ||| (sum2_2 <<< 16)

/-- Pure expression computed by `adler32_combine_` when `¬ (len2 < 0)`. -/
private def combineNonneg (a1 a2 : UInt32) (len2 : Int64) : UInt32 :=
  let rem : UInt32 := (len2 % 65521).toUInt64.toUInt32
  let sum1_0 : UInt32 := a1 &&& 0xffff
  let sum2_0 : UInt32 := (rem * sum1_0) % ZlibNg.Adler32P.BASE
  let sum1_raw : UInt32 := sum1_0 + (a2 &&& 0xffff) + ZlibNg.Adler32P.BASE - 1
  let sum2_raw : UInt32 := sum2_0 + (((a1 >>> 16) &&& (0xffff : UInt32)) + ((a2 >>> 16) &&& (0xffff : UInt32)) + ZlibNg.Adler32P.BASE - rem)
  finishCombinePure sum1_raw sum2_raw

private theorem finish_combine_steps (h : Heap) (u1 u2 : UInt32) :
    C.run (do
      let mut sum1 : UInt32 := u1
      let mut sum2 : UInt32 := u2
      if sum1 >= ZlibNg.Adler32P.BASE then sum1 := sum1 - ZlibNg.Adler32P.BASE
      if sum1 >= ZlibNg.Adler32P.BASE then sum1 := sum1 - ZlibNg.Adler32P.BASE
      if sum2 >= (ZlibNg.Adler32P.BASE <<< 1) then sum2 := sum2 - (ZlibNg.Adler32P.BASE <<< 1)
      if sum2 >= ZlibNg.Adler32P.BASE then sum2 := sum2 - ZlibNg.Adler32P.BASE
      return sum1 ||| (sum2 <<< 16)) h = .ok (finishCombinePure u1 u2, h) := by
  unfold finishCombinePure
  by_cases c1 : u1 >= ZlibNg.Adler32P.BASE
  · simp only [c1, ↓reduceIte]
    by_cases c2 : u1 - ZlibNg.Adler32P.BASE >= ZlibNg.Adler32P.BASE
    · simp only [c2, ↓reduceIte]
      by_cases c3 : u2 >= (ZlibNg.Adler32P.BASE <<< 1)
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 - (ZlibNg.Adler32P.BASE <<< 1) >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
    · simp only [c2, ↓reduceIte]
      by_cases c3 : u2 >= (ZlibNg.Adler32P.BASE <<< 1)
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 - (ZlibNg.Adler32P.BASE <<< 1) >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
  · simp only [c1, ↓reduceIte]
    by_cases c3 : u2 >= (ZlibNg.Adler32P.BASE <<< 1)
    · simp only [c3, ↓reduceIte]
      by_cases c4 : u2 - (ZlibNg.Adler32P.BASE <<< 1) >= ZlibNg.Adler32P.BASE <;>
        simp only [c4, ↓reduceIte] <;> rfl
    · simp only [c3, ↓reduceIte]
      by_cases c4 : u2 >= ZlibNg.Adler32P.BASE <;>
        simp only [c4, ↓reduceIte] <;> rfl

private theorem adler32_combine_run_nonneg (h : Heap) (a1 a2 : UInt32) (len2 : Int64) (hnn : ¬ (len2 < 0)) :
    C.run (adler32_combine_ a1 a2 len2) h = .ok (combineNonneg a1 a2 len2, h) := by
  unfold adler32_combine_ combineNonneg
  simp only [hnn, ↓reduceIte]
  exact finish_combine_steps h _ _

/-- `sums_combine` with `BASE` written as the literal `65521`, split by component. -/
private theorem sums_combine_lit (xs ys : List UInt8) :
    (sums (1, 0) (xs ++ ys)).1 = ((sums (1, 0) xs).1 + (sums (1, 0) ys).1 + 65521 - 1) % 65521 ∧
    (sums (1, 0) (xs ++ ys)).2 =
      (((ys.length % 65521) * (sums (1, 0) xs).1) % 65521 +
        (sums (1, 0) xs).2 + (sums (1, 0) ys).2 + 65521 - (ys.length % 65521)) % 65521 := by
  have h := sums_combine xs ys
  simp only [ZlibNgF.Math.Adler32.BASE] at h
  rw [h]
  exact ⟨rfl, rfl⟩

theorem adler32_combine_spec_proof : AdlerCombineSpec ZlibNg.Adler32.adler32_combine := by
  intro h adler1 adler2 len2
  unfold ZlibNg.Adler32.adler32_combine
  by_cases hneg : len2 < 0
  · refine ⟨0xffffffff, ?_, fun _ => rfl, ?_⟩
    · unfold ZlibNg.Adler32.adler32_combine_
      simp only [hneg, ↓reduceIte, C.run_bind, C.run_pure]
      rfl
    · intro xs ys _ _ hlen
      exfalso
      have hn : len2.toInt < 0 := by simpa using Int64.lt_iff_toInt_lt.mp hneg
      omega
  · let a1 := adler1.toUInt32
    let a2 := adler2.toUInt32
    let res : UInt64 := (combineNonneg a1 a2 len2).toUInt64
    have hrun : C.run (adler32_combine_ a1 a2 len2 >>= fun r => pure r.toUInt64) h = .ok (res, h) := by
      rw [C.run_bind, adler32_combine_run_nonneg h a1 a2 len2 hneg]
      rfl
    refine ⟨res, hrun, fun hn => absurd hn hneg, ?_⟩
    intro xs ys hx1 hx2 hlen
    let rem : UInt32 := (len2 % 65521).toUInt64.toUInt32
    let sum1_0 : UInt32 := a1 &&& 0xffff
    let sum2_0 : UInt32 := (rem * sum1_0) % ZlibNg.Adler32P.BASE
    let sum1_raw : UInt32 := sum1_0 + (a2 &&& 0xffff) + ZlibNg.Adler32P.BASE - 1
    let sum2_raw : UInt32 := sum2_0 + (((a1 >>> 16) &&& (0xffff : UInt32)) + ((a2 >>> 16) &&& (0xffff : UInt32)) + ZlibNg.Adler32P.BASE - rem)
    let sum1_1 := if sum1_raw >= ZlibNg.Adler32P.BASE then sum1_raw - ZlibNg.Adler32P.BASE else sum1_raw
    let sum1_2 := if sum1_1 >= ZlibNg.Adler32P.BASE then sum1_1 - ZlibNg.Adler32P.BASE else sum1_1
    let sum2_1 := if sum2_raw >= (ZlibNg.Adler32P.BASE <<< 1)
      then sum2_raw - (ZlibNg.Adler32P.BASE <<< 1) else sum2_raw
    let sum2_2 := if sum2_1 >= ZlibNg.Adler32P.BASE then sum2_1 - ZlibNg.Adler32P.BASE else sum2_1
    let sx := sums (1, 0) xs
    let sy := sums (1, 0) ys
    have ⟨hsx1, hsx2⟩ := sums_lt_base (1, 0) xs (by dsimp [ZlibNgF.Math.Adler32.BASE]; omega)
    have ⟨hsy1, hsy2⟩ := sums_lt_base (1, 0) ys (by dsimp [ZlibNgF.Math.Adler32.BASE]; omega)
    dsimp [ZlibNgF.Math.Adler32.BASE] at hsx1 hsx2 hsy1 hsy2
    have hsx1' : sx.1 < 65521 := hsx1
    have hsx2' : sx.2 < 65521 := hsx2
    have hsy1' : sy.1 < 65521 := hsy1
    have hsy2' : sy.2 < 65521 := hsy2
    have ha1_lo : sum1_0.toNat = sx.1 := by
      dsimp [sum1_0, a1]
      rw [hx1, low16_32]
      unfold ZlibNgF.Math.Adler32.adler32
      change (UInt32.ofNat (sx.1 + 65536 * sx.2)).toNat % 65536 = sx.1
      rw [u32_ofNat_toNat (by omega)]
      omega
    have ha1_hi : ((a1 >>> 16) &&& (0xffff : UInt32)).toNat = sx.2 := by
      dsimp [a1]
      rw [hx1, high16_32]
      unfold ZlibNgF.Math.Adler32.adler32
      change ((UInt32.ofNat (sx.1 + 65536 * sx.2)).toNat / 65536) % 65536 = sx.2
      rw [u32_ofNat_toNat (by omega)]
      omega
    have ha2_lo : (a2 &&& 0xffff).toNat = sy.1 := by
      dsimp [a2]
      rw [hx2, low16_32]
      unfold ZlibNgF.Math.Adler32.adler32
      change (UInt32.ofNat (sy.1 + 65536 * sy.2)).toNat % 65536 = sy.1
      rw [u32_ofNat_toNat (by omega)]
      omega
    have ha2_hi : ((a2 >>> 16) &&& (0xffff : UInt32)).toNat = sy.2 := by
      dsimp [a2]
      rw [hx2, high16_32]
      unfold ZlibNgF.Math.Adler32.adler32
      change ((UInt32.ofNat (sy.1 + 65536 * sy.2)).toNat / 65536) % 65536 = sy.2
      rw [u32_ofNat_toNat (by omega)]
      omega
    have hrem_nat : rem.toNat = ys.length % 65521 := int64_mod_65521_of_nat len2 ys.length hlen
    have hrem_lt : rem.toNat < 65521 := by rw [hrem_nat]; exact Nat.mod_lt _ (by omega)
    have hbase : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
    have hs2_0_nat : sum2_0.toNat = (rem.toNat * sx.1) % 65521 := by
      dsimp [sum2_0]
      rw [UInt32.toNat_mod, hbase, UInt32.toNat_mul, ha1_lo]
      have hmul_lt : rem.toNat * sx.1 < 2 ^ 32 := by
        have : rem.toNat * sx.1 ≤ 65520 * 65520 := Nat.mul_le_mul (by omega) (by omega)
        omega
      rw [Nat.mod_eq_of_lt hmul_lt]
    have hs1_raw_nat : sum1_raw.toNat = sx.1 + sy.1 + 65521 - 1 := by
      dsimp [sum1_raw]
      have h1 : (sum1_0 + (a2 &&& 0xffff)).toNat = sx.1 + sy.1 := by
        rw [UInt32.toNat_add, ha1_lo, ha2_lo, Nat.mod_eq_of_lt (by omega)]
      have h2 : (sum1_0 + (a2 &&& 0xffff) + ZlibNg.Adler32P.BASE).toNat = sx.1 + sy.1 + 65521 := by
        rw [UInt32.toNat_add, h1, hbase, Nat.mod_eq_of_lt (by omega)]
      have hle1 : (1 : UInt32) ≤ sum1_0 + (a2 &&& 0xffff) + ZlibNg.Adler32P.BASE := by
        show 1 ≤ (sum1_0 + (a2 &&& 0xffff) + ZlibNg.Adler32P.BASE).toNat
        rw [h2]; omega
      rw [UInt32.toNat_sub_of_le _ _ hle1, h2]
      rfl
    have hs2_raw_nat : sum2_raw.toNat = sum2_0.toNat + sx.2 + sy.2 + 65521 - rem.toNat := by
      dsimp [sum2_raw]
      let hi1 := (a1 >>> 16) &&& (0xffff : UInt32)
      let hi2 := (a2 >>> 16) &&& (0xffff : UInt32)
      have hh1 : (hi1 + hi2).toNat = sx.2 + sy.2 := by
        rw [UInt32.toNat_add, ha1_hi, ha2_hi, Nat.mod_eq_of_lt (by omega)]
      have hh2 : (hi1 + hi2 + ZlibNg.Adler32P.BASE).toNat = sx.2 + sy.2 + 65521 := by
        rw [UInt32.toNat_add, hh1, hbase, Nat.mod_eq_of_lt (by omega)]
      have hler : rem ≤ hi1 + hi2 + ZlibNg.Adler32P.BASE := by
        show rem.toNat ≤ (hi1 + hi2 + ZlibNg.Adler32P.BASE).toNat
        rw [hh2]; omega
      have hh3 : (hi1 + hi2 + ZlibNg.Adler32P.BASE - rem).toNat = sx.2 + sy.2 + 65521 - rem.toNat := by
        rw [UInt32.toNat_sub_of_le _ _ hler, hh2]
      have hs2_lt : sum2_0.toNat < 65521 := by rw [hs2_0_nat]; exact Nat.mod_lt _ (by omega)
      rw [UInt32.toNat_add, hh3, Nat.mod_eq_of_lt (by omega)]
      omega
    have hs1_lt3 : sum1_raw.toNat < 3 * 65521 := by rw [hs1_raw_nat]; omega
    have hs2_lt4 : sum2_raw.toNat < 4 * 65521 := by
      rw [hs2_raw_nat, hs2_0_nat]
      by_cases hr0 : rem.toNat = 0
      · rw [hr0]; simp; omega
      · have : (rem.toNat * sx.1) % 65521 < 65521 := Nat.mod_lt _ (by omega)
        omega
    have h_s1_final : sum1_2.toNat = (sx.1 + sy.1 + 65521 - 1) % 65521 := by
      have := reduce_two_base sum1_raw hs1_lt3
      simpa [sum1_1, sum1_2, hs1_raw_nat] using this
    have h_s2_final : sum2_2.toNat = (((ys.length % 65521) * sx.1) % 65521 + sx.2 + sy.2 + 65521 - (ys.length % 65521)) % 65521 := by
      have := reduce_four_base sum2_raw hs2_lt4
      simpa [sum2_1, sum2_2, hs2_raw_nat, hs2_0_nat, hrem_nat] using this
    obtain ⟨hc1, hc2⟩ := sums_combine_lit xs ys
    have hcomb1 : (sums (1, 0) (xs ++ ys)).1 = sum1_2.toNat := hc1.trans h_s1_final.symm
    have hcomb2 : (sums (1, 0) (xs ++ ys)).2 = sum2_2.toNat := hc2.trans h_s2_final.symm
    have hs1_lt_16 : sum1_2.toNat < 65536 := by rw [h_s1_final]; omega
    have hs2_lt_16 : sum2_2.toNat < 65536 := by rw [h_s2_final]; omega
    apply u64_eq_of_toNat
    change (sum1_2 ||| (sum2_2 <<< 16)).toUInt64.toNat = (ZlibNgF.Math.Adler32.adler32 (xs ++ ys)).toUInt64.toNat
    rw [UInt32.toNat_toUInt64, or_shift32 sum1_2 sum2_2 hs1_lt_16 hs2_lt_16, ← hcomb1, ← hcomb2]
    unfold ZlibNgF.Math.Adler32.adler32
    let sab := sums (1, 0) (xs ++ ys)
    have ⟨hab1, hab2⟩ := sums_lt_base (1, 0) (xs ++ ys) (by dsimp [ZlibNgF.Math.Adler32.BASE]; omega)
    dsimp [ZlibNgF.Math.Adler32.BASE] at hab1 hab2
    have hab1' : sab.1 < 65521 := hab1
    have hab2' : sab.2 < 65521 := hab2
    change sab.1 + 65536 * sab.2 = (UInt32.ofNat (sab.1 + 65536 * sab.2)).toUInt64.toNat
    rw [UInt32.toNat_toUInt64, u32_ofNat_toNat (by omega)]

theorem adler32_combine_functional : Goal.adler32_combine_functional :=
  adler32_combine_spec_proof

theorem adler32_combine64_functional : Goal.adler32_combine64_functional :=
  adler32_combine_spec_proof

theorem adler32_combine_safety : Goal.adler32_combine_safety := by
  intro h a1 a2 l2
  obtain ⟨r, hr, _, _⟩ := adler32_combine_spec_proof h a1 a2 l2
  exact ⟨r, hr⟩

theorem adler32_combine64_safety : Goal.adler32_combine64_safety := by
  intro h a1 a2 l2
  obtain ⟨r, hr, _, _⟩ := adler32_combine_spec_proof h a1 a2 l2
  exact ⟨r, hr⟩

end ZlibNgF.Proof.Adler32
