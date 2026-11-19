import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `adler32.c`, `arch/generic/adler32_c.c`, and `adler32_p.h` (`ZlibNgF`)

Proves safety, non-vacuity, and exact RFC 1950 §8.2 functional correctness of `adler32`, `adler32_z`,
`adler32_combine`, and `adler32_combine64`, including `zlib-ng`'s 32-bit `uint32_t` accumulators over
`NMAX = 5552` blocks.
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

/-! ## Slice & `rawSums` monotonicity helpers -/

private abbrev slice (data : Array UInt8) (off len : Nat) : List UInt8 :=
  (data.toList.drop off).take len

private theorem slice_zero (data : Array UInt8) (off : Nat) : slice data off 0 = [] := by
  simp [slice]

private theorem slice_one {data : Array UInt8} {off : Nat} (hlt : off < data.size) :
    slice data off 1 = [data[off]] := by
  unfold slice
  have hlt_l : off < data.toList.length := by simpa using hlt
  rw [List.drop_eq_getElem_cons hlt_l]
  simp

private theorem slice_split (data : Array UInt8) (off m n : Nat) :
    slice data off (m + n) = slice data off m ++ slice data (off + m) n := by
  unfold slice
  rw [List.take_add, List.drop_drop, Nat.add_comm off m]

private theorem slice_len {data : Array UInt8} {off len : Nat} (hle : off + len ≤ data.size) :
    (slice data off len).length = len := by
  unfold slice
  rw [List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem rawSums_mono (s : Nat × Nat) (xs : List UInt8) :
    s.1 ≤ (rawSums s xs).1 ∧ s.2 ≤ (rawSums s xs).2 := by
  induction xs generalizing s with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons x xs ih =>
    simp only [rawSums_cons, rawStep]
    have ⟨h1, h2⟩ := ih (s.1 + x.toNat, s.2 + (s.1 + x.toNat))
    exact ⟨by omega, by omega⟩

private theorem rawSums_prefix_lt_u32 {s : Nat × Nat} {xs ys : List UInt8}
    (h : (rawSums s (xs ++ ys)).1 < 2 ^ 32 ∧ (rawSums s (xs ++ ys)).2 < 2 ^ 32) :
    (rawSums s xs).1 < 2 ^ 32 ∧ (rawSums s xs).2 < 2 ^ 32 := by
  rw [rawSums_append] at h
  have ⟨m1, m2⟩ := rawSums_mono (rawSums s xs) ys
  omega

/-! ## Heap read-only primitive lemmas -/

private theorem ptr_add_ok_on {h : Heap} {r : BRef} {off k : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hle : off + k ≤ data.size) :
    OkOn h ((Ptr.ref r off).add (Int.ofNat k)) (.ref r (off + k)) := by
  dsimp only [OkOn, C.run, Ptr.add]
  rw [hg]
  dsimp only
  have hc : off ≤ data.size ∧ 0 ≤ (off : Int) + Int.ofNat k ∧ (off : Int) + Int.ofNat k ≤ (data.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hnat : ((off : Int) + Int.ofNat k).toNat = off + k := by
    simp only [Int.ofNat_eq_natCast]; omega
  split
  · rw [hnat]
  · rename_i hneg; exact absurd hc hneg

private theorem load8_ok_on {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hlt : off < data.size) :
    OkOn h (load8 (.ref r off)) (data[off]'hlt) := by
  dsimp only [OkOn, C.run, load8, Ptr.load]
  rw [hg]
  dsimp only
  split
  · rfl
  · rename_i hn; exact absurd hlt hn

private theorem index8_ok_on {h : Heap} {r : BRef} {off i : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hlt : off + i < data.size) :
    OkOn h (index8 (.ref r off) (Int.ofNat i)) (data[off + i]'hlt) := by
  unfold index8 Ptr.index
  exact OkOn.bind (ptr_add_ok_on hg (by omega)) (load8_ok_on hg hlt)

/-! ## `adler_do1` and `adler_do8` -/

private theorem adler_do1_ok {h : Heap} {r : BRef} {off i : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hlt : off + i < data.size)
    (a s2 : UInt32)
    (hu32 : (rawStep (a.toNat, s2.toNat) (data[off + i]'hlt)).1 < 2 ^ 32 ∧
            (rawStep (a.toNat, s2.toNat) (data[off + i]'hlt)).2 < 2 ^ 32) :
    OkOn h (adler_do1 a s2 (.ref r off) (Int.ofNat i))
      (UInt32.ofNat (rawStep (a.toNat, s2.toNat) (data[off + i]'hlt)).1,
       UInt32.ofNat (rawStep (a.toNat, s2.toNat) (data[off + i]'hlt)).2) := by
  unfold adler_do1
  refine OkOn.bind (index8_ok_on hg hlt) ?_
  let b := data[off + i]'hlt
  dsimp [rawStep] at hu32 ⊢
  have hb_nat : b.toUInt32.toNat = b.toNat := UInt8.toNat_toUInt32 b
  have ha' : a + b.toUInt32 = UInt32.ofNat (a.toNat + b.toNat) := by
    apply u32_eq_of_toNat
    rw [UInt32.toNat_add, hb_nat, Nat.mod_eq_of_lt hu32.1, u32_ofNat_toNat hu32.1]
  have hs' : s2 + (a + b.toUInt32) = UInt32.ofNat (s2.toNat + (a.toNat + b.toNat)) := by
    apply u32_eq_of_toNat
    rw [ha', UInt32.toNat_add, u32_ofNat_toNat hu32.1, Nat.mod_eq_of_lt hu32.2, u32_ofNat_toNat hu32.2]
  show OkOn h (pure (a + b.toUInt32, s2 + (a + b.toUInt32))) _
  rw [hs', ha']
  exact OkOn.pure h _

private theorem slice8_expand {data : Array UInt8} {off : Nat} (hle : off + 8 ≤ data.size) :
    slice data off 8 =
      [data[off + 0]'(by omega), data[off + 1]'(by omega), data[off + 2]'(by omega), data[off + 3]'(by omega),
       data[off + 4]'(by omega), data[off + 5]'(by omega), data[off + 6]'(by omega), data[off + 7]'(by omega)] := by
  have e0 : slice data off 1 = [data[off + 0]'(by omega)] := by
    simpa [Nat.add_zero] using slice_one (data := data) (off := off) (by omega)
  have e1 : slice data (off + 1) 1 = [data[off + 1]'(by omega)] := slice_one (by omega)
  have e2 : slice data (off + 2) 1 = [data[off + 2]'(by omega)] := slice_one (by omega)
  have e3 : slice data (off + 3) 1 = [data[off + 3]'(by omega)] := slice_one (by omega)
  have e4 : slice data (off + 4) 1 = [data[off + 4]'(by omega)] := slice_one (by omega)
  have e5 : slice data (off + 5) 1 = [data[off + 5]'(by omega)] := slice_one (by omega)
  have e6 : slice data (off + 6) 1 = [data[off + 6]'(by omega)] := slice_one (by omega)
  have e7 : slice data (off + 7) 1 = [data[off + 7]'(by omega)] := slice_one (by omega)
  calc slice data off 8
      = slice data off 1 ++ slice data (off + 1) 7 := slice_split data off 1 7
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ slice data (off + 2) 6) := by
        rw [show (7 : Nat) = 1 + 6 from rfl, slice_split data (off + 1) 1 6, show off + 1 + 1 = off + 2 by omega]
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ (slice data (off + 2) 1 ++ slice data (off + 3) 5)) := by
        rw [show (6 : Nat) = 1 + 5 from rfl, slice_split data (off + 2) 1 5, show off + 2 + 1 = off + 3 by omega]
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ (slice data (off + 2) 1 ++
          (slice data (off + 3) 1 ++ slice data (off + 4) 4))) := by
        rw [show (5 : Nat) = 1 + 4 from rfl, slice_split data (off + 3) 1 4, show off + 3 + 1 = off + 4 by omega]
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ (slice data (off + 2) 1 ++
          (slice data (off + 3) 1 ++ (slice data (off + 4) 1 ++ slice data (off + 5) 3)))) := by
        rw [show (4 : Nat) = 1 + 3 from rfl, slice_split data (off + 4) 1 3, show off + 4 + 1 = off + 5 by omega]
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ (slice data (off + 2) 1 ++
          (slice data (off + 3) 1 ++ (slice data (off + 4) 1 ++ (slice data (off + 5) 1 ++ slice data (off + 6) 2))))) := by
        rw [show (3 : Nat) = 1 + 2 from rfl, slice_split data (off + 5) 1 2, show off + 5 + 1 = off + 6 by omega]
    _ = slice data off 1 ++ (slice data (off + 1) 1 ++ (slice data (off + 2) 1 ++
          (slice data (off + 3) 1 ++ (slice data (off + 4) 1 ++
            (slice data (off + 5) 1 ++ (slice data (off + 6) 1 ++ slice data (off + 7) 1)))))) := by
        rw [show (2 : Nat) = 1 + 1 from rfl, slice_split data (off + 6) 1 1, show off + 6 + 1 = off + 7 by omega]
    _ = [data[off + 0]'(by omega), data[off + 1]'(by omega), data[off + 2]'(by omega), data[off + 3]'(by omega),
         data[off + 4]'(by omega), data[off + 5]'(by omega), data[off + 6]'(by omega), data[off + 7]'(by omega)] := by
        rw [e0, e1, e2, e3, e4, e5, e6, e7]; rfl

private theorem adler_do8_ok {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hle : off + 8 ≤ data.size)
    (a s2 : UInt32)
    (hu32 : (rawSums (a.toNat, s2.toNat) (slice data off 8)).1 < 2 ^ 32 ∧
            (rawSums (a.toNat, s2.toNat) (slice data off 8)).2 < 2 ^ 32) :
    OkOn h (adler_do8 a s2 (.ref r off))
      (UInt32.ofNat (rawSums (a.toNat, s2.toNat) (slice data off 8)).1,
       UInt32.ofNat (rawSums (a.toNat, s2.toNat) (slice data off 8)).2) := by
  rw [slice8_expand hle] at hu32 ⊢
  let b0 := data[off + 0]'(by omega)
  let b1 := data[off + 1]'(by omega)
  let b2 := data[off + 2]'(by omega)
  let b3 := data[off + 3]'(by omega)
  let b4 := data[off + 4]'(by omega)
  let b5 := data[off + 5]'(by omega)
  let b6 := data[off + 6]'(by omega)
  let b7 := data[off + 7]'(by omega)
  let p0 := (a.toNat, s2.toNat)
  let p1 := rawStep p0 b0
  let p2 := rawStep p1 b1
  let p3 := rawStep p2 b2
  let p4 := rawStep p3 b3
  let p5 := rawStep p4 b4
  let p6 := rawStep p5 b5
  let p7 := rawStep p6 b6
  let p8 := rawStep p7 b7
  have hp1 : p1.1 < 2 ^ 32 ∧ p1.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0]) (ys := [b1, b2, b3, b4, b5, b6, b7]) hu32
  have hp2 : p2.1 < 2 ^ 32 ∧ p2.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1]) (ys := [b2, b3, b4, b5, b6, b7]) hu32
  have hp3 : p3.1 < 2 ^ 32 ∧ p3.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1, b2]) (ys := [b3, b4, b5, b6, b7]) hu32
  have hp4 : p4.1 < 2 ^ 32 ∧ p4.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1, b2, b3]) (ys := [b4, b5, b6, b7]) hu32
  have hp5 : p5.1 < 2 ^ 32 ∧ p5.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1, b2, b3, b4]) (ys := [b5, b6, b7]) hu32
  have hp6 : p6.1 < 2 ^ 32 ∧ p6.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1, b2, b3, b4, b5]) (ys := [b6, b7]) hu32
  have hp7 : p7.1 < 2 ^ 32 ∧ p7.2 < 2 ^ 32 :=
    rawSums_prefix_lt_u32 (xs := [b0, b1, b2, b3, b4, b5, b6]) (ys := [b7]) hu32
  have hp8 : p8.1 < 2 ^ 32 ∧ p8.2 < 2 ^ 32 := hu32
  unfold adler_do8
  refine OkOn.bind (adler_do1_ok hg (i := 0) (by omega) a s2 hp1) ?_
  have s1_ok : OkOn h (adler_do1 (UInt32.ofNat p1.1) (UInt32.ofNat p1.2) (.ref r off) 1)
      (UInt32.ofNat p2.1, UInt32.ofNat p2.2) := by
    have hlt1 : off + 1 < data.size := by omega
    have := adler_do1_ok hg hlt1 (UInt32.ofNat p1.1) (UInt32.ofNat p1.2)
    rw [u32_ofNat_toNat hp1.1, u32_ofNat_toNat hp1.2] at this
    exact this hp2
  refine OkOn.bind s1_ok ?_
  have s2_ok : OkOn h (adler_do1 (UInt32.ofNat p2.1) (UInt32.ofNat p2.2) (.ref r off) 2)
      (UInt32.ofNat p3.1, UInt32.ofNat p3.2) := by
    have hlt2 : off + 2 < data.size := by omega
    have := adler_do1_ok hg hlt2 (UInt32.ofNat p2.1) (UInt32.ofNat p2.2)
    rw [u32_ofNat_toNat hp2.1, u32_ofNat_toNat hp2.2] at this
    exact this hp3
  refine OkOn.bind s2_ok ?_
  have s3_ok : OkOn h (adler_do1 (UInt32.ofNat p3.1) (UInt32.ofNat p3.2) (.ref r off) 3)
      (UInt32.ofNat p4.1, UInt32.ofNat p4.2) := by
    have hlt3 : off + 3 < data.size := by omega
    have := adler_do1_ok hg hlt3 (UInt32.ofNat p3.1) (UInt32.ofNat p3.2)
    rw [u32_ofNat_toNat hp3.1, u32_ofNat_toNat hp3.2] at this
    exact this hp4
  refine OkOn.bind s3_ok ?_
  have s4_ok : OkOn h (adler_do1 (UInt32.ofNat p4.1) (UInt32.ofNat p4.2) (.ref r off) 4)
      (UInt32.ofNat p5.1, UInt32.ofNat p5.2) := by
    have hlt4 : off + 4 < data.size := by omega
    have := adler_do1_ok hg hlt4 (UInt32.ofNat p4.1) (UInt32.ofNat p4.2)
    rw [u32_ofNat_toNat hp4.1, u32_ofNat_toNat hp4.2] at this
    exact this hp5
  refine OkOn.bind s4_ok ?_
  have s5_ok : OkOn h (adler_do1 (UInt32.ofNat p5.1) (UInt32.ofNat p5.2) (.ref r off) 5)
      (UInt32.ofNat p6.1, UInt32.ofNat p6.2) := by
    have hlt5 : off + 5 < data.size := by omega
    have := adler_do1_ok hg hlt5 (UInt32.ofNat p5.1) (UInt32.ofNat p5.2)
    rw [u32_ofNat_toNat hp5.1, u32_ofNat_toNat hp5.2] at this
    exact this hp6
  refine OkOn.bind s5_ok ?_
  have s6_ok : OkOn h (adler_do1 (UInt32.ofNat p6.1) (UInt32.ofNat p6.2) (.ref r off) 6)
      (UInt32.ofNat p7.1, UInt32.ofNat p7.2) := by
    have hlt6 : off + 6 < data.size := by omega
    have := adler_do1_ok hg hlt6 (UInt32.ofNat p6.1) (UInt32.ofNat p6.2)
    rw [u32_ofNat_toNat hp6.1, u32_ofNat_toNat hp6.2] at this
    exact this hp7
  refine OkOn.bind s6_ok ?_
  have hlt7 : off + 7 < data.size := by omega
  have s7_ok := adler_do1_ok hg hlt7 (UInt32.ofNat p7.1) (UInt32.ofNat p7.2)
  rw [u32_ofNat_toNat hp7.1, u32_ofNat_toNat hp7.2] at s7_ok
  exact s7_ok hp8

/-! ## `adler32_len_1`, `adler32_len_16`, and `adler32_len_64` -/

private def packSums (s : Nat × Nat) : UInt32 :=
  UInt32.ofNat (s.1 + 65536 * s.2)

private theorem mod_pack_u32 (a s2 : UInt32) :
    let am := a % ZlibNg.Adler32P.BASE
    let sm := s2 % ZlibNg.Adler32P.BASE
    am ||| (sm <<< 16) = packSums (a.toNat % 65521, s2.toNat % 65521) := by
  intro am sm
  have hb : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  have ham : am.toNat = a.toNat % 65521 := by rw [UInt32.toNat_mod, hb]
  have hsm : sm.toNat = s2.toNat % 65521 := by rw [UInt32.toNat_mod, hb]
  have ham_lt : am.toNat < 65536 := by rw [ham]; omega
  have hsm_lt : sm.toNat < 65536 := by rw [hsm]; omega
  apply u32_eq_of_toNat
  rw [or_shift32 am sm ham_lt hsm_lt, ham, hsm]
  unfold packSums
  rw [u32_ofNat_toNat (by omega)]

private theorem adler32_len_1_ok {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hlt : off < data.size)
    (a s2 : UInt32) (ha : a.toNat ≤ 65535) (hs2 : s2.toNat ≤ 65535) :
    OkOn h (adler32_len_1 a (.ref r off) s2)
      (packSums (sums (a.toNat % 65521, s2.toNat % 65521) (slice data off 1))) := by
  rw [slice_one hlt]
  unfold adler32_len_1
  refine OkOn.bind (index8_ok_on hg (i := 0) (by omega)) ?_
  let b := data[off + 0]'(by omega)
  have hb_eq : b = data[off]'hlt := by simp [b]
  have hb_lt : b.toNat < 256 := b.toBitVec.isLt
  have hb_nat : b.toUInt32.toNat = b.toNat := UInt8.toNat_toUInt32 b
  have hbase : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  let a1 := (a + b.toUInt32) % ZlibNg.Adler32P.BASE
  let s1 := (s2 + a1) % ZlibNg.Adler32P.BASE
  have ha1_nat : a1.toNat = (a.toNat % 65521 + b.toNat) % 65521 := by
    have hadd_a : (a + b.toUInt32).toNat = a.toNat + b.toNat := by
      rw [UInt32.toNat_add, hb_nat]; exact Nat.mod_eq_of_lt (by omega)
    dsimp [a1]
    rw [UInt32.toNat_mod, hbase, hadd_a]
    rw [Nat.add_mod (a.toNat % 65521), Nat.mod_mod, ← Nat.add_mod]
  have ha1_lt : a1.toNat < 65521 := by rw [ha1_nat]; exact Nat.mod_lt _ (by omega)
  have hs1_nat : s1.toNat = (s2.toNat % 65521 + a1.toNat) % 65521 := by
    have hadd_s : (s2 + a1).toNat = s2.toNat + a1.toNat := by
      rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    dsimp [s1]
    rw [UInt32.toNat_mod, hbase, hadd_s]
    rw [Nat.add_mod (s2.toNat % 65521), Nat.mod_mod, ← Nat.add_mod]
  have hs1_lt : s1.toNat < 65521 := by rw [hs1_nat]; exact Nat.mod_lt _ (by omega)
  have hres : a1 ||| (s1 <<< 16) = packSums (sums (a.toNat % 65521, s2.toNat % 65521) [data[off]'hlt]) := by
    apply u32_eq_of_toNat
    rw [or_shift32 a1 s1 (by omega) (by omega)]
    unfold packSums
    simp only [sums_cons, sums_nil, step, ZlibNgF.Math.Adler32.BASE]
    rw [u32_ofNat_toNat (by omega), hs1_nat, ha1_nat, hb_eq]
  change OkOn h (pure (a1 ||| (s1 <<< 16))) _
  rw [hres]
  exact OkOn.pure h _

private theorem adler32_len_16_ok {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (len : UInt64) (hle : off + len.toNat ≤ data.size)
    (a s2 : UInt32)
    (hu32 : (rawSums (a.toNat, s2.toNat) (slice data off len.toNat)).1 < 2 ^ 32 ∧
            (rawSums (a.toNat, s2.toNat) (slice data off len.toNat)).2 < 2 ^ 32) :
    OkOn h (adler32_len_16 a (.ref r off) len s2)
      (packSums (sums (a.toNat % 65521, s2.toNat % 65521) (slice data off len.toNat))) := by
  unfold adler32_len_16
  let L := len.toNat
  let target := rawSums (a.toNat, s2.toNat) (slice data off L)
  have htarget_lt : target.1 < 2 ^ 32 ∧ target.2 < 2 ^ 32 := hu32
  let P : Nat → State32 → Prop := fun k st =>
    k ≤ L ∧
    st.buf = .ref r (off + (L - k)) ∧
    st.len.toNat = k ∧
    (rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + (L - k)) k)) = target ∧
    st.adler.toNat ≤ target.1 ∧ st.sum2.toNat ≤ target.2
  let Q : State32 → Prop := fun st =>
    st.adler.toNat = target.1 ∧ st.sum2.toNat = target.2
  refine OkOn.bind_ex (R := Q) ?_ ?_
  · refine cwhile_ok P Q ?_ ?_ (k := L) (s := { adler := a, sum2 := s2, buf := .ref r off, len := len, n := 0 }) ?_ ?_
    · intro k st ⟨hkL, hbuf, hlen, hraw, ha_le, hs_le⟩
      have hne0 : (st.len != 0) = true := by
        have hne : st.len ≠ 0 := fun hz => by rw [hz] at hlen; simp at hlen
        simp [hne]
      let curOff := off + (L - (k + 1))
      have hlt_cur : curOff < data.size := by dsimp [curOff, L]; omega
      let b := data[curOff]'hlt_cur
      have hsplit : slice data curOff (k + 1) = [b] ++ slice data (curOff + 1) k := by
        rw [show k + 1 = 1 + k by omega, slice_split, slice_one hlt_cur]
      rw [hsplit, List.singleton_append, rawSums_cons] at hraw
      let nextPair := rawStep (st.adler.toNat, st.sum2.toNat) b
      have hmono := rawSums_mono nextPair (slice data (curOff + 1) k)
      rw [hraw] at hmono
      have hnext_lt : nextPair.1 < 2 ^ 32 ∧ nextPair.2 < 2 ^ 32 := ⟨by omega, by omega⟩
      have hb_nat : b.toUInt32.toNat = b.toNat := UInt8.toNat_toUInt32 b
      have ha_add : (st.adler + b.toUInt32).toNat = nextPair.1 := by
        have hlt1 : st.adler.toNat + b.toNat < 2 ^ 32 := hnext_lt.1
        rw [UInt32.toNat_add, hb_nat, Nat.mod_eq_of_lt hlt1]
        rfl
      have hs_add : (st.sum2 + (st.adler + b.toUInt32)).toNat = nextPair.2 := by
        have hlt2 : st.sum2.toNat + nextPair.1 < 2 ^ 32 := hnext_lt.2
        rw [UInt32.toNat_add, ha_add, Nat.mod_eq_of_lt hlt2]
        rfl
      have hlen1 : (st.len - 1).toNat = k := by
        have hle1 : (1 : UInt64) ≤ st.len := by show 1 ≤ st.len.toNat; omega
        rw [UInt64.toNat_sub_of_le _ _ hle1]; show st.len.toNat - 1 = k; omega
      let st2 : State32 := {
        st with
        adler := st.adler + b.toUInt32
        sum2 := st.sum2 + (st.adler + b.toUInt32)
        buf := .ref r (curOff + 1)
        len := st.len - 1
      }
      refine ⟨st, st2, ?_, ?_, ?_⟩
      · show OkOn h (pure (st.len != 0, st)) (true, st)
        rw [hne0]; exact OkOn.pure h _
      · show OkOn h (do
          let len := st.len - 1
          let b ← load8 st.buf
          let buf ← st.buf.add 1
          let adler := st.adler + b.toUInt32
          let sum2 := st.sum2 + adler
          pure { st with adler, sum2, buf, len }) st2
        rw [hbuf]
        refine OkOn.bind (load8_ok_on hg hlt_cur) ?_
        refine OkOn.bind (ptr_add_ok_on hg (k := 1) (by dsimp [curOff, L]; omega)) ?_
        exact OkOn.pure h _
      · have hoff_eq : curOff + 1 = off + (L - k) := by dsimp [curOff]; omega
        refine ⟨by omega, ?_, hlen1, ?_, ?_, ?_⟩
        · dsimp [st2]; rw [hoff_eq]
        · dsimp [st2]; rw [ha_add, hs_add, ← hoff_eq]; exact hraw
        · dsimp [st2]; rw [ha_add]; exact hmono.1
        · dsimp [st2]; rw [hs_add]; exact hmono.2
    · intro st ⟨_, _, hlen, hraw, _, _⟩
      have hz : st.len = 0 := u64_eq_of_toNat hlen
      have hne0 : (st.len != 0) = false := by rw [hz]; rfl
      rw [slice_zero, rawSums_nil] at hraw
      refine ⟨st, ?_, ?_⟩
      · show OkOn h (pure (st.len != 0, st)) (false, st)
        rw [hne0]; exact OkOn.pure h _
      · exact ⟨congrArg Prod.fst hraw, congrArg Prod.snd hraw⟩
    · refine ⟨Nat.le_refl _, ?_, rfl, ?_, ?_⟩
      · simp
      · simp [target]
      · exact rawSums_mono (a.toNat, s2.toNat) (slice data off L)
    · show L < 2 ^ 64
      exact len.toBitVec.isLt
  · intro st ⟨ha_eq, hs_eq⟩
    show OkOn h (pure ((st.adler % ZlibNg.Adler32P.BASE) ||| ((st.sum2 % ZlibNg.Adler32P.BASE) <<< 16))) _
    rw [mod_pack_u32 st.adler st.sum2, ha_eq, hs_eq]
    have hmod := rawSums_mod (a.toNat, s2.toNat) (slice data off len.toNat)
    dsimp [ZlibNgF.Math.Adler32.BASE] at hmod
    have hm1 : target.1 % 65521 = (sums (a.toNat % 65521, s2.toNat % 65521) (slice data off len.toNat)).1 :=
      congrArg Prod.fst hmod
    have hm2 : target.2 % 65521 = (sums (a.toNat % 65521, s2.toNat % 65521) (slice data off len.toNat)).2 :=
      congrArg Prod.snd hmod
    rw [hm1, hm2]
    exact OkOn.pure h _

private theorem adler32_len_64_ok {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (len : UInt64)
    (hle : off + len.toNat ≤ data.size) (hnmax : len.toNat ≤ 5552)
    (a s2 : UInt32) (ha : a.toNat ≤ 65535) (hs2 : s2.toNat ≤ 65535) :
    OkOn h (adler32_len_64 a (.ref r off) len s2)
      (packSums (sums (a.toNat % 65521, s2.toNat % 65521) (slice data off len.toNat))) := by
  unfold adler32_len_64
  let L := len.toNat
  have hlen_sl : (slice data off L).length ≤ ZlibNgF.Math.Adler32.NMAX := by
    rw [slice_len hle]; exact hnmax
  have hu32_total := rawSums_lt_u32 (a.toNat, s2.toNat) (slice data off L) ha hs2 hlen_sl
  let target := rawSums (a.toNat, s2.toNat) (slice data off L)
  have htarget_lt : target.1 < 2 ^ 32 ∧ target.2 < 2 ^ 32 := hu32_total
  let K := L / 8
  let rem := L % 8
  let P : Nat → State32 → Prop := fun k st =>
    k ≤ K ∧
    st.buf = .ref r (off + 8 * (K - k)) ∧
    st.len.toNat = 8 * k + rem ∧
    rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * (K - k)) (8 * k + rem)) = target ∧
    st.adler.toNat ≤ target.1 ∧ st.sum2.toNat ≤ target.2
  let Q : State32 → Prop := fun st =>
    st.buf = .ref r (off + 8 * K) ∧
    st.len.toNat = rem ∧
    rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * K) rem) = target ∧
    st.adler.toNat ≤ target.1 ∧ st.sum2.toNat ≤ target.2
  refine OkOn.bind_ex (R := Q) ?_ ?_
  · refine cwhile_ok P Q ?_ ?_ (k := K) (s := { adler := a, sum2 := s2, buf := .ref r off, len := len, n := 0 }) ?_ ?_
    · intro k st ⟨hkK, hbuf, hlen, hraw, ha_le, hs_le⟩
      have hge8 : (decide (st.len >= 8)) = true := by
        simp only [ge_iff_le, decide_eq_true_eq]
        show 8 ≤ st.len.toNat; omega
      let curOff := off + 8 * (K - (k + 1))
      have hcur_le : curOff + 8 ≤ data.size := by dsimp [curOff, K, L]; omega
      have hsplit := slice_split data curOff 8 (8 * k + rem)
      have h8_eq : 8 + (8 * k + rem) = 8 * (k + 1) + rem := by omega
      rw [h8_eq] at hsplit
      rw [hsplit, rawSums_append] at hraw
      let mid := rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)
      have hmono := rawSums_mono mid (slice data (curOff + 8) (8 * k + rem))
      rw [hraw] at hmono
      have hmid_lt : mid.1 < 2 ^ 32 ∧ mid.2 < 2 ^ 32 := ⟨by omega, by omega⟩
      have hlen8 : (st.len - 8).toNat = 8 * k + rem := by
        have hle8 : (8 : UInt64) ≤ st.len := by show 8 ≤ st.len.toNat; omega
        rw [UInt64.toNat_sub_of_le _ _ hle8]; show st.len.toNat - 8 = 8 * k + rem; omega
      let st2 : State32 := {
        st with
        adler := UInt32.ofNat mid.1
        sum2 := UInt32.ofNat mid.2
        buf := .ref r (curOff + 8)
        len := st.len - 8
      }
      refine ⟨st, st2, ?_, ?_, ?_⟩
      · show OkOn h (pure (decide (st.len >= 8), st)) (true, st)
        rw [hge8]; exact OkOn.pure h _
      · show OkOn h (do
          let len := st.len - 8
          let (adler, sum2) ← adler_do8 st.adler st.sum2 st.buf
          let buf ← st.buf.add 8
          pure { st with adler, sum2, buf, len }) st2
        rw [hbuf]
        refine OkOn.bind (adler_do8_ok hg hcur_le st.adler st.sum2 hmid_lt) ?_
        refine OkOn.bind (ptr_add_ok_on hg (k := 8) hcur_le) ?_
        exact OkOn.pure h _
      · have hoff_eq : curOff + 8 = off + 8 * (K - k) := by dsimp [curOff]; omega
        refine ⟨by omega, ?_, hlen8, ?_, ?_, ?_⟩
        · dsimp [st2]; rw [hoff_eq]
        · dsimp [st2]
          rw [u32_ofNat_toNat hmid_lt.1, u32_ofNat_toNat hmid_lt.2, ← hoff_eq]
          exact hraw
        · dsimp [st2]; rw [u32_ofNat_toNat hmid_lt.1]; exact hmono.1
        · dsimp [st2]; rw [u32_ofNat_toNat hmid_lt.2]; exact hmono.2
    · intro st ⟨_, hbuf, hlen, hraw, ha_le, hs_le⟩
      have hlt8 : (decide (st.len >= 8)) = false := by
        simp only [ge_iff_le, decide_eq_false_iff_not]
        show ¬ (8 ≤ st.len.toNat)
        dsimp [rem] at hlen; omega
      simp only [Nat.sub_zero] at hbuf hraw
      simp only [Nat.mul_zero, Nat.zero_add] at hlen hraw
      refine ⟨st, ?_, hbuf, hlen, hraw, ha_le, hs_le⟩
      show OkOn h (pure (decide (st.len >= 8), st)) (false, st)
      rw [hlt8]; exact OkOn.pure h _
    · have hL_eq : 8 * K + rem = L := Nat.div_add_mod L 8
      refine ⟨Nat.le_refl _, ?_, ?_, ?_, rawSums_mono (a.toNat, s2.toNat) (slice data off L)⟩
      · simp
      · simp [hL_eq, L]
      · simp [hL_eq, target]
    · show K < 2 ^ 64
      have : L < 2 ^ 64 := len.toBitVec.isLt
      dsimp [K]; omega
  · intro st ⟨hbuf, hlen, hraw, _, _⟩
    rw [hbuf]
    have hrem_le : off + 8 * K + st.len.toNat ≤ data.size := by
      rw [hlen]; dsimp [K, rem, L]; omega
    have hu32_tail : (rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * K) st.len.toNat)).1 < 2 ^ 32 ∧
        (rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * K) st.len.toNat)).2 < 2 ^ 32 := by
      rw [hlen, hraw]; exact htarget_lt
    have htail := adler32_len_16_ok hg st.len hrem_le st.adler st.sum2 hu32_tail
    have hsums_eq :
        sums (st.adler.toNat % 65521, st.sum2.toNat % 65521) (slice data (off + 8 * K) st.len.toNat) =
          sums (a.toNat % 65521, s2.toNat % 65521) (slice data off L) := by
      have hm1 := rawSums_mod (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * K) st.len.toNat)
      have hm2 := rawSums_mod (a.toNat, s2.toNat) (slice data off L)
      dsimp [ZlibNgF.Math.Adler32.BASE] at hm1 hm2
      rw [← hm1, hlen, hraw, hm2]
    rw [hsums_eq] at htail
    exact htail

/-! ## Inner `cdoWhile` (694 × 8 = 5552 bytes) and full `adler32_c` -/

private theorem nmax_block_ok {h : Heap} {r : BRef} {off : Nat} {data : Array UInt8}
    (hg : Space.get h r = some data) (hle : off + 5552 ≤ data.size)
    (a s2 : UInt32) (ha : a.toNat ≤ 65535) (hs2 : s2.toNat ≤ 65535)
    (remLen : UInt64) :
    ∃ st',
      OkOn h
        (cdoWhile
          (fun (s : State32) => do
            let (adler, sum2) ← adler_do8 s.adler s.sum2 s.buf
            let buf ← s.buf.add 8
            pure { s with adler, sum2, buf })
          (fun (s : State32) =>
            let n := s.n - 1
            pure (n != 0, { s with n }))
          { adler := a, sum2 := s2, buf := .ref r off, len := remLen, n := 694 })
        st' ∧
      st'.buf = .ref r (off + 5552) ∧
      st'.len = remLen ∧
      ((st'.adler % ZlibNg.Adler32P.BASE).toNat, (st'.sum2 % ZlibNg.Adler32P.BASE).toNat) =
        sums (a.toNat % 65521, s2.toNat % 65521) (slice data off 5552) := by
  have hlen_sl : (slice data off 5552).length ≤ ZlibNgF.Math.Adler32.NMAX := by
    rw [slice_len hle]; decide
  have hu32_total := rawSums_lt_u32 (a.toNat, s2.toNat) (slice data off 5552) ha hs2 hlen_sl
  let target := rawSums (a.toNat, s2.toNat) (slice data off 5552)
  have htarget_lt : target.1 < 2 ^ 32 ∧ target.2 < 2 ^ 32 := hu32_total
  let bodyFn : State32 → M State32 := fun s => do
    let (adler, sum2) ← adler_do8 s.adler s.sum2 s.buf
    let buf ← s.buf.add 8
    pure { s with adler, sum2, buf }
  let condFn : State32 → M (Bool × State32) := fun s =>
    let n := s.n - 1
    pure (n != 0, { s with n })
  let P : Nat → State32 → Prop := fun k st =>
    k ≤ 693 ∧
    st.buf = .ref r (off + 8 * (693 - k)) ∧
    st.len = remLen ∧
    st.n.toNat = k + 1 ∧
    rawSums (st.adler.toNat, st.sum2.toNat) (slice data (off + 8 * (693 - k)) (8 * (k + 1))) = target ∧
    st.adler.toNat ≤ target.1 ∧ st.sum2.toNat ≤ target.2
  let Q : State32 → Prop := fun st =>
    st.buf = .ref r (off + 5552) ∧
    st.len = remLen ∧
    st.adler.toNat = target.1 ∧ st.sum2.toNat = target.2
  have hcdo : ∃ st', OkOn h (cdoWhile bodyFn condFn
      { adler := a, sum2 := s2, buf := .ref r off, len := remLen, n := 694 }) st' ∧ Q st' := by
    refine cdoWhile_ok P Q ?_ ?_ (k := 693)
      (s := { adler := a, sum2 := s2, buf := .ref r off, len := remLen, n := 694 }) ?_ ?_
    · intro k st ⟨hk, hbuf, hlen, hn, hraw, ha_le, hs_le⟩
      let curOff := off + 8 * (693 - (k + 1))
      have hcur_le : curOff + 8 ≤ data.size := by dsimp [curOff]; omega
      have hsplit := slice_split data curOff 8 (8 * (k + 1))
      have h8_eq : 8 + 8 * (k + 1) = 8 * (k + 1 + 1) := by omega
      rw [h8_eq] at hsplit
      rw [hsplit, rawSums_append] at hraw
      let mid := rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)
      have hmono := rawSums_mono mid (slice data (curOff + 8) (8 * (k + 1)))
      rw [hraw] at hmono
      have hmid_lt : mid.1 < 2 ^ 32 ∧ mid.2 < 2 ^ 32 := ⟨by omega, by omega⟩
      let st1 : State32 := {
        st with
        adler := UInt32.ofNat mid.1
        sum2 := UInt32.ofNat mid.2
        buf := .ref r (curOff + 8)
      }
      have hn_sub : (st1.n - 1).toNat = k + 1 := by
        dsimp [st1]
        have hle1 : (1 : UInt32) ≤ st.n := by show 1 ≤ st.n.toNat; omega
        rw [UInt32.toNat_sub_of_le _ _ hle1]; show st.n.toNat - 1 = k + 1; omega
      have hne0 : (st1.n - 1 != 0) = true := by
        have hne : st1.n - 1 ≠ 0 := fun hz => by rw [hz] at hn_sub; simp at hn_sub
        simp [hne]
      refine ⟨st1, { st1 with n := st1.n - 1 }, ?_, ?_, ?_⟩
      · dsimp [bodyFn]; rw [hbuf]
        refine OkOn.bind (adler_do8_ok hg hcur_le st.adler st.sum2 hmid_lt) ?_
        refine OkOn.bind (ptr_add_ok_on hg (k := 8) hcur_le) ?_
        exact OkOn.pure h _
      · dsimp [condFn]; rw [hne0]; exact OkOn.pure h _
      · have hoff_eq : curOff + 8 = off + 8 * (693 - k) := by dsimp [curOff]; omega
        refine ⟨by omega, ?_, hlen, hn_sub, ?_, ?_, ?_⟩
        · dsimp [st1]; rw [hoff_eq]
        · dsimp [st1]; rw [u32_ofNat_toNat hmid_lt.1, u32_ofNat_toNat hmid_lt.2, ← hoff_eq]; exact hraw
        · dsimp [st1]; rw [u32_ofNat_toNat hmid_lt.1]; exact hmono.1
        · dsimp [st1]; rw [u32_ofNat_toNat hmid_lt.2]; exact hmono.2
    · intro st ⟨_, hbuf, hlen, hn, hraw, _, _⟩
      let curOff := off + 8 * 693
      have hcur_le : curOff + 8 ≤ data.size := by dsimp [curOff]; omega
      simp only [Nat.sub_zero, Nat.zero_add, Nat.mul_one] at hbuf hraw
      have hmid_lt' : (rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)).1 < 2 ^ 32 ∧
          (rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)).2 < 2 ^ 32 := by
        dsimp [curOff]; rw [hraw]; exact htarget_lt
      let st1 : State32 := {
        st with
        adler := UInt32.ofNat (rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)).1
        sum2 := UInt32.ofNat (rawSums (st.adler.toNat, st.sum2.toNat) (slice data curOff 8)).2
        buf := .ref r (curOff + 8)
      }
      have hn1 : st.n = 1 := u32_eq_of_toNat hn
      have hne0 : (st1.n - 1 != 0) = false := by dsimp [st1]; rw [hn1]; rfl
      refine ⟨st1, { st1 with n := st1.n - 1 }, ?_, ?_, ?_⟩
      · dsimp [bodyFn]; rw [hbuf]
        refine OkOn.bind (adler_do8_ok hg hcur_le st.adler st.sum2 hmid_lt') ?_
        refine OkOn.bind (ptr_add_ok_on hg (k := 8) hcur_le) ?_
        exact OkOn.pure h _
      · dsimp [condFn]; rw [hne0]; exact OkOn.pure h _
      · refine ⟨by dsimp [st1, curOff], hlen, ?_, ?_⟩
        · dsimp [st1]; rw [u32_ofNat_toNat hmid_lt'.1]; dsimp [curOff]; exact congrArg Prod.fst hraw
        · dsimp [st1]; rw [u32_ofNat_toNat hmid_lt'.2]; dsimp [curOff]; exact congrArg Prod.snd hraw
    · refine ⟨Nat.le_refl _, by simp, rfl, rfl, by simp [target], rawSums_mono (a.toNat, s2.toNat) (slice data off 5552)⟩
    · show 693 < 2 ^ 64; decide
  obtain ⟨st', hrun, hbuf', hlen', ha', hs'⟩ := hcdo
  refine ⟨st', hrun, hbuf', hlen', ?_⟩
  have hb : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  rw [UInt32.toNat_mod, UInt32.toNat_mod, hb, ha', hs']
  exact rawSums_mod (a.toNat, s2.toNat) (slice data off 5552)

private theorem adler32_c_ok {h : Heap} (seed : UInt32) (buf : BPtr) (len : UInt64) (bytes : List UInt8)
    (hbuf : BufferBytes h buf len.toNat bytes) :
    OkOn h (adler32_c seed buf len)
      (if buf = .null then 1
       else packSums (sums ((seed.toNat % 65536) % 65521, ((seed.toNat / 65536) % 65536) % 65521) bytes)) := by
  rcases hbuf with ⟨rfl, rfl⟩ | ⟨r, off, data, rfl, hg, hle, rfl⟩
  · unfold adler32_c
    rfl
  · simp only [show (Ptr.ref r off = (.null : BPtr)) ↔ False by simp, ↓reduceIte]
    unfold adler32_c
    have hnn : (Ptr.ref r off == (.null : BPtr)) = false := rfl
    simp only [hnn, Bool.false_eq_true, ↓reduceIte]
    let a0 : UInt32 := seed &&& 0xffff
    let s0 : UInt32 := (seed >>> 16) &&& (0xffff : UInt32)
    have ha0_nat : a0.toNat = seed.toNat % 65536 := low16_32 seed
    have hs0_nat : s0.toNat = (seed.toNat / 65536) % 65536 := high16_32 seed
    have ha0_le : a0.toNat ≤ 65535 := by rw [ha0_nat]; omega
    have hs0_le : s0.toNat ≤ 65535 := by rw [hs0_nat]; omega
    by_cases h1 : len == 1
    · have hlen1 : len = 1 := beq_iff_eq.mp h1
      subst hlen1
      simp only [show ((1 : UInt64) == 1) = true from rfl, ↓reduceIte]
      have h1nat : (1 : UInt64).toNat = 1 := rfl
      rw [h1nat] at hle ⊢
      have hlt_off : off < data.size := by omega
      have := adler32_len_1_ok hg hlt_off a0 s0 ha0_le hs0_le
      rw [ha0_nat, hs0_nat] at this
      exact this
    · have h1f : (len == 1) = false := Bool.eq_false_iff.mpr h1
      by_cases h16 : len < 16
      · have h16_nat : len.toNat < 16 := h16
        simp only [h1f, Bool.false_eq_true, ↓reduceIte, h16]
        have hu32 := rawSums_lt_u32 (a0.toNat, s0.toNat) (slice data off len.toNat) ha0_le hs0_le
          (by rw [slice_len hle]; dsimp [ZlibNgF.Math.Adler32.NMAX]; omega)
        have := adler32_len_16_ok hg len hle a0 s0 hu32
        rw [ha0_nat, hs0_nat] at this
        exact this
      · simp only [h1f, Bool.false_eq_true, ↓reduceIte, h16]
        let L := len.toNat
        let B := L / 5552
        let R := L % 5552
        let initS := (a0.toNat % 65521, s0.toNat % 65521)
        let P : Nat → State32 → Prop := fun k st =>
          k ≤ B ∧
          st.buf = .ref r (off + 5552 * (B - k)) ∧
          st.len.toNat = 5552 * k + R ∧
          st.adler.toNat ≤ 65535 ∧ st.sum2.toNat ≤ 65535 ∧
          (st.adler.toNat % 65521, st.sum2.toNat % 65521) = sums initS (slice data off (5552 * (B - k)))
        let Q : State32 → Prop := fun st =>
          st.buf = .ref r (off + 5552 * B) ∧
          st.len.toNat = R ∧
          st.adler.toNat ≤ 65535 ∧ st.sum2.toNat ≤ 65535 ∧
          (st.adler.toNat % 65521, st.sum2.toNat % 65521) = sums initS (slice data off (5552 * B))
        refine OkOn.bind_ex (R := Q) ?_ ?_
        · refine cwhile_ok P Q ?_ ?_
            (k := B) (s := { adler := a0, sum2 := s0, buf := .ref r off, len := len, n := 0 }) ?_ ?_
          · intro k st ⟨hkB, hbuf, hlen, ha_le, hs_le, hsums⟩
            have hgeN : (decide (st.len >= ZlibNg.Adler32P.NMAX)) = true := by
              simp only [ge_iff_le, decide_eq_true_eq]
              show 5552 ≤ st.len.toNat; omega
            let curOff := off + 5552 * (B - (k + 1))
            have hcur_le : curOff + 5552 ≤ data.size := by dsimp [curOff, B, L]; omega
            have hrem_nat : (st.len - ZlibNg.Adler32P.NMAX).toNat = 5552 * k + R := by
              have hleN : ZlibNg.Adler32P.NMAX ≤ st.len := by show 5552 ≤ st.len.toNat; omega
              rw [UInt64.toNat_sub_of_le _ _ hleN]
              show st.len.toNat - 5552 = 5552 * k + R; omega
            have hn694 : (ZlibNg.Adler32P.NMAX / 8).toUInt32 = 694 := rfl
            obtain ⟨st', hcdo, hbuf', hlen', hmod'⟩ :=
              nmax_block_ok hg hcur_le st.adler st.sum2 ha_le hs_le (st.len - ZlibNg.Adler32P.NMAX)
            let st2 : State32 := {
              st' with
              adler := st'.adler % ZlibNg.Adler32P.BASE
              sum2 := st'.sum2 % ZlibNg.Adler32P.BASE
            }
            refine ⟨st, st2, ?_, ?_, ?_⟩
            · show OkOn h (pure (decide (st.len >= ZlibNg.Adler32P.NMAX), st)) (true, st)
              rw [hgeN]; exact OkOn.pure h _
            · show OkOn h (do
                let s := { st with len := st.len - ZlibNg.Adler32P.NMAX, n := (ZlibNg.Adler32P.NMAX / 8).toUInt32 }
                let s ← cdoWhile _ _ s
                pure { s with adler := s.adler % ZlibNg.Adler32P.BASE, sum2 := s.sum2 % ZlibNg.Adler32P.BASE }) st2
              rw [hn694, hbuf]
              exact OkOn.bind hcdo (OkOn.pure h _)
            · have hoff_eq : curOff + 5552 = off + 5552 * (B - k) := by dsimp [curOff]; omega
              have hbase : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
              have ha2_lt : st2.adler.toNat < 65521 := by
                dsimp [st2]; rw [UInt32.toNat_mod, hbase]; exact Nat.mod_lt _ (by omega)
              have hs2_lt : st2.sum2.toNat < 65521 := by
                dsimp [st2]; rw [UInt32.toNat_mod, hbase]; exact Nat.mod_lt _ (by omega)
              refine ⟨by omega, ?_, ?_, by omega, by omega, ?_⟩
              · dsimp [st2]; rw [hbuf', hoff_eq]
              · dsimp [st2]; rw [hlen', hrem_nat]
              · dsimp [st2]
                rw [Nat.mod_eq_of_lt ha2_lt, Nat.mod_eq_of_lt hs2_lt, hmod', hsums]
                have hsp : slice data off (5552 * (B - k)) =
                    slice data off (5552 * (B - (k + 1))) ++ slice data curOff 5552 := by
                  have hm : 5552 * (B - (k + 1)) + 5552 = 5552 * (B - k) := by omega
                  rw [← hm]
                  exact slice_split data off (5552 * (B - (k + 1))) 5552
                rw [hsp, sums_append]
          · intro st ⟨_, hbuf, hlen, ha_le, hs_le, hsums⟩
            have hltN : (decide (st.len >= ZlibNg.Adler32P.NMAX)) = false := by
              simp only [ge_iff_le, decide_eq_false_iff_not]
              show ¬ (5552 ≤ st.len.toNat)
              dsimp [R] at hlen; omega
            simp only [Nat.sub_zero] at hbuf hsums
            simp only [Nat.mul_zero, Nat.zero_add] at hlen
            refine ⟨st, ?_, hbuf, hlen, ha_le, hs_le, hsums⟩
            show OkOn h (pure (decide (st.len >= ZlibNg.Adler32P.NMAX), st)) (false, st)
            rw [hltN]; exact OkOn.pure h _
          · have hBL : 5552 * B + R = L := Nat.div_add_mod L 5552
            refine ⟨Nat.le_refl _, by simp, by simp [hBL, L], ha0_le, hs0_le, ?_⟩
            simp only [Nat.sub_self, Nat.mul_zero, slice_zero, sums_nil]
            rfl
          · show B < 2 ^ 64
            have : L < 2 ^ 64 := len.toBitVec.isLt
            dsimp [B]; omega
        · intro st ⟨hbuf, hlen, ha_le, hs_le, hsums⟩
          rw [hbuf]
          have hrem_le : off + 5552 * B + st.len.toNat ≤ data.size := by
            rw [hlen]; dsimp [B, R, L]; omega
          have hnmax_rem : st.len.toNat ≤ 5552 := by
            rw [hlen]; dsimp [R]; omega
          have htail := adler32_len_64_ok hg st.len hrem_le hnmax_rem st.adler st.sum2 ha_le hs_le
          have hfin : sums (st.adler.toNat % 65521, st.sum2.toNat % 65521) (slice data (off + 5552 * B) st.len.toNat) =
              sums initS (slice data off L) := by
            rw [hsums, hlen, ← sums_append]
            have hBL : 5552 * B + R = L := Nat.div_add_mod L 5552
            have hsp := slice_split data off (5552 * B) R
            rw [hBL] at hsp
            rw [← hsp]
          rw [hfin] at htail
          dsimp [initS, L] at htail
          rw [ha0_nat, hs0_nat] at htail
          exact htail

/-! ## Public `adler32` & `adler32_z` goals -/

theorem adler32_z_functional : Goal.adler32_z_functional := by
  intro h seed buf len bytes hbuf
  unfold ZlibNg.Adler32.adler32_z
  have hc := adler32_c_ok seed.toUInt32 buf len bytes hbuf
  have hfin : OkOn h (adler32_c seed.toUInt32 buf len >>= fun r => pure r.toUInt64)
      ((if buf = .null then (1 : UInt32)
        else packSums (sums ((seed.toUInt32.toNat % 65536) % 65521,
          ((seed.toUInt32.toNat / 65536) % 65536) % 65521) bytes)).toUInt64) :=
    OkOn.bind hc (OkOn.pure h _)
  unfold OkOn at hfin
  by_cases hnull : buf = .null
  · subst hnull
    simpa using hfin
  · simp only [hnull, ↓reduceIte] at hfin ⊢
    rw [hfin]
    congr 1; congr 1
    have hlo : seed.toUInt32.toNat % 65536 = seed.toNat % 65536 := by
      rw [UInt64.toNat_toUInt32]
      exact Nat.mod_mod_of_dvd seed.toNat (by decide : 65536 ∣ 2 ^ 32)
    have hhi : (seed.toUInt32.toNat / 65536) % 65536 = (seed.toNat / 65536) % 65536 := by
      have := seed_high16 seed
      rw [high16_32] at this
      exact this
    rw [hlo, hhi]
    unfold ZlibNgF.Math.Adler32.adler32Update packSums ZlibNgF.Math.Adler32.BASE
    have ⟨hp1, hp2⟩ := sums_lt_base ((seed.toNat % 65536) % 65521, ((seed.toNat / 65536) % 65536) % 65521) bytes
      ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
    dsimp [ZlibNgF.Math.Adler32.BASE] at hp1 hp2
    let q := sums ((seed.toNat % 65536) % 65521, ((seed.toNat / 65536) % 65536) % 65521) bytes
    have hq1 : q.1 < 65521 := hp1
    have hq2 : q.2 < 65521 := hp2
    apply u64_eq_of_toNat
    change (UInt32.ofNat (q.1 + 65536 * q.2)).toUInt64.toNat = (UInt64.ofNat (q.1 + 65536 * q.2)).toNat
    rw [UInt32.toNat_toUInt64, u32_ofNat_toNat (by omega), u64_ofNat_toNat (by omega)]

theorem adler32_functional : Goal.adler32_functional := by
  intro h seed buf len bytes hbuf
  have hnat : len.toUInt64.toNat = len.toNat := UInt32.toNat_toUInt64 len
  have hbuf64 : BufferBytes h buf len.toUInt64.toNat bytes := by rwa [hnat]
  exact adler32_z_functional h seed buf len.toUInt64 bytes hbuf64

theorem adler32_z_safety : Goal.adler32_z_safety := by
  intro h seed buf len bytes hbuf
  exact ⟨_, adler32_z_functional h seed buf len bytes hbuf⟩

theorem adler32_safety : Goal.adler32_safety := by
  intro h seed buf len bytes hbuf
  exact ⟨_, adler32_functional h seed buf len bytes hbuf⟩

theorem adler32_nonvacuous : Goal.adler32_nonvacuous := by
  let arr : Array UInt8 := Array.replicate 6000 0x41
  let h : Heap := { Heap.empty with bytes := upd Heap.empty.bytes 0 (some arr), nextBlk := 1 }
  let buf : BPtr := .ref (.heap 0) 0
  let bytes : List UInt8 := (arr.toList.drop 0).take 6000
  have hg : Space.get h (BRef.heap 0) = some arr := by
    simp only [Space.get, Heap.getBytes, h, upd_same]
  have harr_sz : arr.size = 6000 := Array.size_replicate
  have hlen_bytes : bytes.length = 6000 := by
    dsimp [bytes]
    rw [List.length_take, List.length_drop, Array.length_toList, harr_sz]
    omega
  have hbuf_ne : buf ≠ .null := by dsimp [buf]; intro hc; cases hc
  have hab : BufferBytes h buf 6000 bytes :=
    Or.inr ⟨BRef.heap 0, 0, arr, rfl, hg, by omega, rfl⟩
  obtain ⟨r, hrun⟩ := adler32_safety h 1 buf 6000 bytes hab
  exact ⟨h, buf, bytes, r, hbuf_ne, hlen_bytes, hab, hrun⟩

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
    let twoB : UInt64 := ZlibNg.Adler32P.BASE.toUInt64 <<< 1
    let x1 : UInt32 := if x.toUInt64 >= twoB then (x.toUInt64 - twoB).toUInt32 else x
    let x2 : UInt32 := if x1 >= ZlibNg.Adler32P.BASE then x1 - ZlibNg.Adler32P.BASE else x1
    x2.toNat = x.toNat % 65521 := by
  intro twoB x1 x2
  have hb : ZlibNg.Adler32P.BASE.toNat = 65521 := rfl
  have h2b : twoB.toNat = 131042 := rfl
  have hx1 : x1.toNat = if 131042 ≤ x.toNat then x.toNat - 131042 else x.toNat := by
    dsimp [x1]
    by_cases h1 : x.toUInt64 >= twoB
    · have h1n : 131042 ≤ x.toNat := by
        have : twoB.toNat ≤ x.toUInt64.toNat := h1
        rw [h2b, UInt32.toNat_toUInt64] at this
        exact this
      simp only [h1, h1n, ↓reduceIte]
      rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ h1, UInt32.toNat_toUInt64, h2b]
      exact Nat.mod_eq_of_lt (by omega)
    · have h1n : ¬ (131042 ≤ x.toNat) := by
        intro hc; apply h1
        show twoB.toNat ≤ x.toUInt64.toNat
        rw [h2b, UInt32.toNat_toUInt64]; exact hc
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
  let sum2_1 := if u2.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)
    then (u2.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32 else u2
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
      if sum2.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1) then
        sum2 := (sum2.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32
      if sum2 >= ZlibNg.Adler32P.BASE then sum2 := sum2 - ZlibNg.Adler32P.BASE
      return sum1 ||| (sum2 <<< 16)) h = .ok (finishCombinePure u1 u2, h) := by
  unfold finishCombinePure
  by_cases c1 : u1 >= ZlibNg.Adler32P.BASE
  · simp only [c1, ↓reduceIte]
    by_cases c2 : u1 - ZlibNg.Adler32P.BASE >= ZlibNg.Adler32P.BASE
    · simp only [c2, ↓reduceIte]
      by_cases c3 : u2.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)
      · simp only [c3, ↓reduceIte]
        by_cases c4 : (u2.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
    · simp only [c2, ↓reduceIte]
      by_cases c3 : u2.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)
      · simp only [c3, ↓reduceIte]
        by_cases c4 : (u2.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
      · simp only [c3, ↓reduceIte]
        by_cases c4 : u2 >= ZlibNg.Adler32P.BASE <;>
          simp only [c4, ↓reduceIte] <;> rfl
  · simp only [c1, ↓reduceIte]
    by_cases c3 : u2.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)
    · simp only [c3, ↓reduceIte]
      by_cases c4 : (u2.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32 >= ZlibNg.Adler32P.BASE <;>
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
    let sum2_1 := if sum2_raw.toUInt64 >= (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)
      then (sum2_raw.toUInt64 - (ZlibNg.Adler32P.BASE.toUInt64 <<< 1)).toUInt32 else sum2_raw
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
