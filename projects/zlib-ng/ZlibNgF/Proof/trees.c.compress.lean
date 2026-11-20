import ZlibNgF.Proof.«trees.c.overlay»
import ZlibNgF.Proof.«trees.c.init»
import ZlibNgF.Proof.«trees_emit.h.static»

/-!
# `compress_block` (`ZlibNgF`)

`compress_block` on `SH` heaps for any pair of trees `ltree` / `dtree` that read as arrays `LT` / `DT` with the code
lengths that it reads at most 15 (the literal/length code of each tallied symbol and `END_BLOCK`, the distance code of
each tallied match; the other entries may hold anything, such as the guard `0xffff` that `scan_tree` stores at
`max_code + 1`): the symbol loop over
`sym_buf[0 .. sym_next)` with the merged literal look-ahead, each iteration's 8-byte store kept below the unread
symbols by `room_before` (`Math/TreesOverlay.lean`), and the end-of-block code by `room_end`. The budget is an
explicit hypothesis `Budget B t0 (blockCosts LT DT d sbo n)`: the bits before the first symbol and the excess of the
symbol costs under `LT` / `DT` fit the overlay.

The bits emitted are exact: `8 * pending + bi_valid` grows by the sum of the symbol costs and the length of the
end-of-block code.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesCompress
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateBits ZlibNgF.Proof.TreesEmitP ZlibNgF.Math.TreesOverlay
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.TreesEmitP (ival_get WrIn.cat)

/-! ## Bit arithmetic -/

theorem or_mul (a x k : Nat) (ha : a < 2 ^ k) : a ||| x * 2 ^ k = a + x * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]; omega

theorem m4_toNat (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (24 : UInt32).toNat % 32 = 24 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [or_mul _ _ 8 (by omega), or_mul _ _ 16 (by omega), or_mul _ _ 24 (by omega)]
  omega

theorem m8_toNat (lo hi : UInt32) :
    (lo.toUInt64 ||| (hi.toUInt64 <<< 32)).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
  have h0 := lo.toNat_lt; have h1 := hi.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), or_mul _ _ 32 (by omega)]
  omega

theorem and_ffff (x : UInt32) : (x &&& 0xffff).toNat = x.toNat % 65536 := by
  rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 16

theorem shr16_ff (x : UInt32) : ((x >>> 16) &&& 0xff).toNat = x.toNat / 65536 % 256 := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem shr_ff64 (x : UInt64) (k : UInt64) (hk : k.toNat < 64) :
    ((x >>> k) &&& 0xff).toUInt32.toNat = x.toNat / 2 ^ k.toNat % 256 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  rw [show (0xff : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 8]; omega

theorem and_shl (x m k : Nat) : x &&& (m <<< k) = ((x >>> k) &&& m) <<< k := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : k ≤ i
  · simp [h, Nat.add_sub_cancel' h]
  · simp [h]

theorem lit3_mask (x : UInt64) : (x &&& ZlibNg.Trees.LIT3_DIST1_MASK) = 0 ↔ x.toNat / 2 ^ 24 % 65536 = 0 := by
  have e : (ZlibNg.Trees.LIT3_DIST1_MASK).toNat = (2 ^ 16 - 1) <<< 24 := rfl
  rw [← UInt64.toNat_inj, UInt64.toNat_and, e, and_shl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  simp only [UInt64.toNat_zero]
  omega

/-- `send_bits_flush`'s split of `bi_valid` into whole bytes and the rest. -/
theorem flush_split (bv : UInt32) (h : bv.toNat < 64) :
    (bv >>> 3).toNat = bv.toNat / 8 ∧ (bv &&& 7).toNat = bv.toNat % 8 ∧ (bv &&& ~~~7) < 64 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  · rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 3
  · rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_left h

/-! ## Byte reads -/

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem index8_SH {o : Nat} (k : Int) (h0 : 0 ≤ k) (hk : o + k.toNat < d.size) :
    index8 (.ref (.heap b) o) k (SH H i z b st d) = .ok (d[o + k.toNat]!, SH H i z b st d) := by
  unfold index8 Ptr.index
  rw [bind_app, addI_SH k h0 (by omega)]
  have e : ((o : Int) + k).toNat = o + k.toNat := by omega
  have hs : Space.get (SH H i z b st d) (BRef.heap b) = some d := SH_bytes H i z b st d
  simp only [Ptr.load, hs, e, hk, ↓reduceDIte]
  rw [getElem!_pos d _ hk]

theorem memread4_SH {o : Nat} (hk : o + 4 ≤ d.size) :
    memread4 (.ref (.heap b) o) (SH H i z b st d) =
      .ok (d[o]!.toUInt32 ||| (d[o + 1]!.toUInt32 <<< 8) ||| (d[o + 2]!.toUInt32 <<< 16) |||
        (d[o + 3]!.toUInt32 <<< 24), SH H i z b st d) := by
  unfold memread4
  have r := fun (k : Nat) (hk' : o + k < d.size) =>
    index8_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) (o := o) (k : Int) (by omega) (by simpa using hk')
  simp only [Int.toNat_natCast] at r
  simp only [bind_app, show (0 : Int) = ((0 : Nat) : Int) from rfl, show (1 : Int) = ((1 : Nat) : Int) from rfl,
    show (2 : Int) = ((2 : Nat) : Int) from rfl, show (3 : Int) = ((3 : Nat) : Int) from rfl,
    r 0 (by omega), r 1 (by omega), r 2 (by omega), r 3 (by omega), Nat.add_zero]
  rfl

/-- The value of `zng_memread_4` as a number. -/
def rd4 (d : Array UInt8) (o : Nat) : Nat :=
  d[o]!.toNat + 256 * d[o + 1]!.toNat + 65536 * d[o + 2]!.toNat + 16777216 * d[o + 3]!.toNat

theorem memread4_val {o : Nat} (hk : o + 4 ≤ d.size) :
    ∃ v, memread4 (.ref (.heap b) o) (SH H i z b st d) = .ok (v, SH H i z b st d) ∧ v.toNat = rd4 d o :=
  ⟨_, memread4_SH hk, m4_toNat _ _ _ _⟩

theorem memread8_val {o : Nat} (hk : o + 8 ≤ d.size) :
    ∃ v, memread8 (.ref (.heap b) o) (SH H i z b st d) = .ok (v, SH H i z b st d) ∧
      v.toNat = rd4 d o + 2 ^ 32 * rd4 d (o + 4) := by
  obtain ⟨lo, e1, h1⟩ := memread4_val (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (o := o) (by omega)
  obtain ⟨hi, e2, h2⟩ := memread4_val (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (o := o + 4) (by omega)
  refine ⟨_, ?_, (m8_toNat lo hi).trans (by rw [h1, h2])⟩
  unfold memread8
  have e3 := addI_SH (H := H) (i := i) (z := z) (st := st) (b := b) (d := d) (off := o) 4 (by decide) (by omega)
  have e4 : ((o : Int) + 4).toNat = o + 4 := by omega
  rw [e4] at e3
  simp only [bind_app, e1, e3, e2]
  rfl

end

/-! ## Trees read as arrays -/

/-- On every heap of the family `F`, the tree pointer `tp` reads `T[k]` at each `k < n`. -/
def TreeRd (F : Heap → Prop) (tp : CtPtr) (T : Array Ct) (n : Nat) : Prop :=
  ∀ H', F H' → ∀ k, k < n → ctGet tp (k : Int) H' = .ok (T[k]!, H')

theorem TreeRd.fc {F : Heap → Prop} {tp : CtPtr} {T : Array Ct} {n : Nat} (t : TreeRd F tp T n) {H' : Heap}
    (hF : F H') (k : Nat) (hk : k < n) : ctFc tp (k : Int) H' = .ok ((T[k]!).fc, H') := by
  simp [ctFc, bind_app, t H' hF k hk]

theorem TreeRd.dl {F : Heap → Prop} {tp : CtPtr} {T : Array Ct} {n : Nat} (t : TreeRd F tp T n) {H' : Heap}
    (hF : F H') (k : Nat) (hk : k < n) : ctDl tp (k : Int) H' = .ok ((T[k]!).dl, H') := by
  simp [ctDl, bind_app, t H' hF k hk]

theorem treeRd_sl (F : Heap → Prop) : TreeRd F (.ref .static_ltree 0) static_ltree 288 :=
  fun H' _ k hk => ctGet_sl H' k hk

theorem treeRd_sd (F : Heap → Prop) : TreeRd F (.ref .static_dtree 0) static_dtree 30 :=
  fun H' _ k hk => ctGet_sd H' k hk

/-- The heaps of `compress_block` on `SH H i z b st _`: the state changed outside the trees. -/
def Fam (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (H' : Heap) : Prop :=
  ∃ st' d', H' = SH H i z b st' d' ∧ st'.dyn_ltree = st.dyn_ltree ∧ st'.dyn_dtree = st.dyn_dtree

theorem treeRd_dl (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) :
    TreeRd (Fam H i z b st) (.ref (CtRef.dyn_ltree b) 0) st.dyn_ltree st.dyn_ltree.size := by
  rintro _ ⟨st', d', rfl, hl, -⟩ k hk
  rw [← hl] at hk ⊢
  exact TreesInit.ctGet_dl st' k hk

/-! ## Symbol costs -/

/-- The bits of a match with length symbol `lc` and distance `dm + 1` under the trees `LT` / `DT`: the length code
and its extra bits, the distance code and its extra bits. -/
def matchCost (LT DT : Array Ct) (lc dm : Nat) : Nat :=
  (LT[(zng_length_code[lc]!).toNat + 257]!).dl.toNat + (lmask_extra[(zng_length_code[lc]!).toNat]!.toUInt32 >>> 8).toNat +
    (DT[dCodeOf dm]!).dl.toNat + (dmask_extra[dCodeOf dm]! >>> 16).toNat

/-- The bits of tallied symbol `j` (bytes `d` from `sym_buf` offset `sbo`) under the trees `LT` / `DT`. -/
def symCost (LT DT : Array Ct) (d : Array UInt8) (sbo j : Nat) : Nat :=
  if symDist d sbo j = 0 then (LT[d[sbo + 3 * j + 2]!.toNat]!).dl.toNat
  else matchCost LT DT d[sbo + 3 * j + 2]!.toNat (symDist d sbo j - 1)

/-- `symCost` in terms of the decoding of the invariant (`symLCode`, `symDist`, `dCodeOf`): the length of the
literal/length code, plus for a match the length extra bits, the distance code and its extra bits. -/
theorem symCost_eq (LT DT : Array Ct) (d : Array UInt8) (sbo j : Nat) :
    symCost LT DT d sbo j = (LT[symLCode d sbo j]!).dl.toNat +
      (if symDist d sbo j = 0 then 0 else
        (lmask_extra[(zng_length_code[d[sbo + 3 * j + 2]!.toNat]!).toNat]!.toUInt32 >>> 8).toNat +
        (DT[dCodeOf (symDist d sbo j - 1)]!).dl.toNat + (dmask_extra[dCodeOf (symDist d sbo j - 1)]! >>> 16).toNat) := by
  unfold symCost symLCode matchCost
  by_cases h : symDist d sbo j = 0
  · simp [h]
  · simp only [h, ↓reduceIte]; omega

/-- The bit costs of the first `n` tallied symbols. -/
def blockCosts (LT DT : Array Ct) (d : Array UInt8) (sbo n : Nat) : List Nat :=
  (List.range n).map (symCost LT DT d sbo)

theorem blockCosts_length (LT DT : Array Ct) (d : Array UInt8) (sbo n : Nat) :
    (blockCosts LT DT d sbo n).length = n := by simp [blockCosts]

theorem blockCosts_take (LT DT : Array Ct) (d : Array UInt8) (sbo n k : Nat) (hk : k ≤ n) :
    ((blockCosts LT DT d sbo n).take (k + 1)).sum = ((blockCosts LT DT d sbo n).take k).sum + symCost LT DT d sbo k ∨ n ≤ k := by
  by_cases h : k < n
  · left
    rw [List.take_add_one, List.sum_append]
    simp [blockCosts, h]
  · right; omega

theorem dCodeOf_lt (x : Nat) (hx : x < 32768) : dCodeOf x < 30 := by
  unfold dCodeOf
  split
  · exact UInt8.lt_iff_toNat_lt.mp (dc_lt ⟨x, by omega⟩)
  · exact UInt8.lt_iff_toNat_lt.mp (dc_lt ⟨256 + x / 128, by omega⟩)

theorem d_code_val (H : Heap) (x : UInt32) (hx : x.toNat < 32768) :
    ∃ c : UInt8, d_code x H = .ok (c, H) ∧ c.toNat = dCodeOf x.toNat := by
  unfold d_code dCodeOf
  by_cases c : x < 256
  · rw [ite_t c]
    have c' := UInt32.lt_iff_toNat_lt.mp c
    simp only [show (256 : UInt32).toNat = 256 from rfl] at c'
    exact ⟨_, tblGet_ok _ _ (by rw [dc_size]; omega) H, by simp [c']⟩
  · rw [ite_f c]
    have c' : ¬ x.toNat < 256 := fun h => c (UInt32.lt_iff_toNat_lt.mpr h)
    have hs : (x >>> 7).toNat = x.toNat / 128 := by
      rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    exact ⟨_, tblGet_ok _ _ (by rw [dc_size, hs]; omega) H, by simp [c', hs]⟩

/-- `zng_assemble_dist` for trees that read as `LT` / `DT` with the two code lengths it reads at most 15: no fault,
`matchCost` bits. -/
theorem assemble_gen {F : Heap → Prop} {lp dp : CtPtr} {LT DT : Array Ct} (hl : TreeRd F lp LT 286)
    (hd : TreeRd F dp DT 30) {H : Heap} (hF : F H) (lc dist : UInt32) (hlc : lc.toNat < 256)
    (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hl15 : (LT[(zng_length_code[lc.toNat]!).toNat + 257]!).dl.toNat ≤ 15)
    (hd15 : (DT[dCodeOf (dist.toNat - 1)]!).dl.toNat ≤ 15) :
    Sat H (ZlibNg.TreesEmit.zng_assemble_dist lp dp lc dist)
      (fun r H' => H' = H ∧ r.2.toNat = matchCost LT DT lc.toNat (dist.toNat - 1)) := by
  unfold ZlibNg.TreesEmit.zng_assemble_dist
  refine Sat.bind (Sat.of_eq (tblGet_ok _ _ (by rw [lc_size]; exact hlc) H) ?_)
  have hcode : (zng_length_code[lc.toNat]!).toNat < 29 := UInt8.lt_iff_toNat_lt.mp (lc_lt ⟨_, hlc⟩)
  unfold matchCost
  generalize zng_length_code[lc.toNat]! = code at hcode hl15 ⊢
  have hc : (code.toUInt32 + LITERALS.toUInt32 + 1).toNat = code.toNat + 257 := by
    simp only [UInt32.toNat_add, UInt8.toNat_toUInt32, LITERALS]; simp; omega
  try dsimp only
  rw [hc]
  have hl1 := hl15
  have hx1 := lm_ext ⟨_, hcode⟩
  obtain ⟨e1, he1⟩ : ∃ e, LT[code.toNat + 257]! = e := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ e, lmask_extra[code.toNat]! = e := ⟨_, rfl⟩
  rw [he1] at hl1; rw [hm1] at hx1
  refine Sat.bind (Sat.of_eq ((hl.fc hF _ (by omega)).trans (by rw [he1])) ?_)
  refine Sat.bind (Sat.of_eq ((hl.dl hF _ (by omega)).trans (by rw [he1])) ?_)
  refine Sat.bind (Sat.of_eq ((tblGet_ok _ _ (by rw [lm_size]; exact hcode) H).trans (by rw [hm1])) ?_)
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by simp only [UInt16.toNat_toUInt32]; omega) H) ?_)
  have hd1' : (1 : UInt32) ≤ dist := UInt32.le_iff_toNat_le.mpr (by simpa using hd1)
  have hdm : (dist - 1).toNat = dist.toNat - 1 := by rw [UInt32.toNat_sub_of_le _ _ hd1']; rfl
  obtain ⟨c2, hdc, hc2⟩ := d_code_val H (dist - 1) (by rw [hdm]; omega)
  have hc30 : c2.toNat < 30 := by rw [hc2]; exact dCodeOf_lt _ (by omega)
  rw [hdm] at hc2
  rw [← hc2]
  refine Sat.bind (Sat.of_eq hdc ?_)
  have hx2 := (dm_ext ⟨_, hc30⟩).1
  have hl2 : (DT[c2.toNat]!).dl.toNat ≤ 15 := by rw [hc2]; exact hd15
  obtain ⟨e2, he2⟩ : ∃ e, DT[c2.toNat]! = e := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ e, dmask_extra[c2.toNat]! = e := ⟨_, rfl⟩
  rw [he2] at hl2; rw [hm2] at hx2
  have hs1 : (e1.dl.toUInt32 + m1.toUInt32 >>> 8).toNat = e1.dl.toNat + (m1.toUInt32 >>> 8).toNat := by
    rw [UInt32.toNat_add, UInt16.toNat_toUInt32]; omega
  refine Sat.bind (Sat.of_eq ((hd.fc hF _ hc30).trans (by rw [he2])) ?_)
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by rw [hs1]; omega) H) ?_)
  refine Sat.bind (Sat.of_eq ((hd.dl hF _ hc30).trans (by rw [he2])) ?_)
  refine Sat.bind (Sat.of_eq ((tblGet_ok _ _ (by rw [dm_size]; exact hc30) H).trans (by rw [hm2])) ?_)
  have hs2 : (e1.dl.toUInt32 + m1.toUInt32 >>> 8 + e2.dl.toUInt32).toNat =
      e1.dl.toNat + (m1.toUInt32 >>> 8).toNat + e2.dl.toNat := by
    rw [UInt32.toNat_add, hs1, UInt16.toNat_toUInt32]; omega
  refine Sat.bind (Sat.of_eq (shl_ok _ _ (by rw [hs2]; omega) H) ?_)
  refine Sat.pure ⟨rfl, ?_⟩
  show (e1.dl.toUInt32 + m1.toUInt32 >>> 8 + e2.dl.toUInt32 + m2 >>> 16).toNat = _
  rw [UInt32.toNat_add, hs2, he1, hm1, he2, hm2]; omega

/-! ## The symbol loop -/

open ZlibNg.Trees (CBL LIT3_DIST1_MASK) in
open ZlibNg.TreesEmit in
/-- The body of the symbol loop of `compress_block` (copied; `cbBody_eq`). -/
def cbBody (st : StatePtr) (ltree dtree : CtPtr) (sym_next : UInt32) (sym_buf : BPtr) (l : CBL) : M CBL := do
  let (bi_buf, bi_valid, pending) ← send_bits_flush st l.bi_buf l.bi_valid l.pending
  let dist_lc ← memread4 (← sym_buf.add l.sx.toNat)
  let dist : UInt32 := dist_lc &&& 0xffff
  let lc : Int32 := ((dist_lc >>> 16) &&& 0xff).toInt32
  let mut sx := l.sx + 3
  if dist == 0 then
    let bits : UInt64 := 0
    let nbits : UInt32 := 0
    let (bits, nbits) ← send_code_merge st lc.toInt ltree bits nbits
    let mut bits := bits
    let mut nbits := nbits
    if sx + 8 <= sym_next then
      let next_syms ← memread8 (← sym_buf.add sx.toNat)
      if next_syms.toUInt16 == 0 then
        (bits, nbits) ← send_code_merge st ((next_syms >>> 16) &&& 0xff).toUInt32.toNat ltree bits nbits
        sx := sx + 3
        if next_syms &&& LIT3_DIST1_MASK == 0 then
          (bits, nbits) ← send_code_merge st ((next_syms >>> 40) &&& 0xff).toUInt32.toNat ltree bits nbits
          sx := sx + 3
    let bi_buf := bi_buf ||| (← shl64 bits bi_valid)
    let bi_valid := bi_valid + nbits
    pure ⟨sx, bi_buf, bi_valid, pending⟩
  else
    let (match_bits, match_bits_len) ← zng_assemble_dist ltree dtree lc.toUInt32 dist
    let (bi_buf, bi_valid) ← send_bits_merge st match_bits match_bits_len bi_buf bi_valid
    pure ⟨sx, bi_buf, bi_valid, pending⟩

set_option maxRecDepth 20000 in
open ZlibNg.Trees (CBL) in
theorem cbBody_eq (st : StatePtr) (ltree dtree : CtPtr) :
    ZlibNg.Trees.compress_block st ltree dtree = (do
      let sx : UInt32 := 0
      let sym_next : UInt32 ← rdD st (·.sym_next)
      let sym_buf : BPtr ← (← rdD st (·.sym_buf)).get
      let bi_buf : UInt64 ← rdD st (·.bi_buf)
      let bi_valid : UInt32 := (← rdD st (·.bi_valid)).toUInt32
      let pending : UInt32 ← rdD st (·.pending)
      let l0 : CBL := ⟨sx, bi_buf, bi_valid, pending⟩
      let l ← if sym_next != 0 then
          cdoWhile (cbBody st ltree dtree sym_next sym_buf) (fun (l : CBL) => pure (l.sx < sym_next, l)) l0
        else pure l0
      wrD st fun s => { s with pending := l.pending }
      let (bi_buf, bi_valid) ← ZlibNg.TreesEmit.zng_emit_end_block st ltree 0 l.bi_buf l.bi_valid
      wrD st fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 }) := by
  unfold ZlibNg.Trees.compress_block cbBody
  rfl

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `send_bits_flush`: the 8-byte store at `pending_buf + pending`, the whole bytes of `bi_valid` counted. -/
theorem flush_SH {pbo : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo)) (bb : UInt64) (bv p : UInt32)
    (hbv : bv.toNat < 64) (hroom : pbo + p.toNat + 8 ≤ d.size) (hp : p.toNat + 8 < 2 ^ 32) :
    Sat (SH H i z b st d) (ZlibNg.TreesEmit.send_bits_flush (some b) bb bv p) (fun r H1 => ∃ d1,
      H1 = SH H i z b st d1 ∧ WrIn d (pbo + p.toNat) (pbo + p.toNat + 8) d1 ∧
      r.2.2.toNat = p.toNat + bv.toNat / 8 ∧ r.2.1.toNat = bv.toNat % 8) := by
  unfold ZlibNg.TreesEmit.send_bits_flush
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (ival_get hpb _) ?_)
  have ea := addI_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) (off := pbo) (p.toNat : Int)
    (by omega) (by omega)
  rw [show ((pbo : Int) + (p.toNat : Int)).toNat = pbo + p.toNat by omega] at ea
  refine Sat.bind (Sat.of_eq ea (Sat.bind (Sat.mono (memwrite8_SH bb (by omega)) ?_)))
  rintro _ _ ⟨d1, rfl, w⟩
  obtain ⟨h1, h2, h3⟩ := flush_split bv hbv
  simp only [shr64, h3, ↓reduceIte, pure_bind_M]
  refine Sat.pure ⟨d1, rfl, w, ?_, h2⟩
  dsimp only
  rw [UInt32.toNat_add, h1]; omega

end

/-- The code lengths that `compress_block` reads are at most 15: the literal/length code of each of the `n` tallied
symbols and `END_BLOCK`, the distance code of each tallied match. -/
def UsedLe15 (LT DT : Array Ct) (d : Array UInt8) (sbo n : Nat) : Prop :=
  (LT[256]!).dl.toNat ≤ 15 ∧ ∀ j, j < n → (LT[symLCode d sbo j]!).dl.toNat ≤ 15 ∧
    (symDist d sbo j ≠ 0 → (DT[dCodeOf (symDist d sbo j - 1)]!).dl.toNat ≤ 15)

/-- The setting of `compress_block` on `SH H i z b st d`: `pending_buf` at `pbo`, `n` whole symbols at
`sbo = pbo + lit_bufsize + 8`, at most `lit_bufsize - 1` of them, the trees `lp` / `dp` read as `LT` / `DT` with the
code lengths that `compress_block` reads at most 15 (`UsedLe15`), tallied distances at most 32768, fewer than 64 bits waiting, and the overlay budget. -/
structure CBCtx (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
    (lp dp : CtPtr) (LT DT : Array Ct) (pbo sbo n : Nat) : Prop where
  hpb : st.pending_buf = .val (.ref (.heap b) pbo)
  hsb : st.sym_buf = .val (.ref (.heap b) sbo)
  hsn : st.sym_next.toNat = 3 * n
  hsbo : sbo = pbo + st.lit_bufsize.toNat + 8
  hend : pbo + 4 * st.lit_bufsize.toNat + 9 ≤ d.size
  hn : n + 1 ≤ st.lit_bufsize.toNat
  hlb : st.lit_bufsize.toNat ≤ 32768
  hl : TreeRd (Fam H i z b st) lp LT 286
  hd : TreeRd (Fam H i z b st) dp DT 30
  hu15 : UsedLe15 LT DT d sbo n
  hdist : ∀ j, j < n → symDist d sbo j ≤ 32768
  v0 : 0 ≤ st.bi_valid.toInt
  v64 : st.bi_valid.toInt < 64
  budget : Budget st.lit_bufsize.toNat (8 * st.pending.toNat + st.bi_valid.toInt.toNat) (blockCosts LT DT d sbo n)

/-- The loop invariant: `k` symbols consumed, the bytes changed only below symbol `k`, the bits counted exactly. -/
def CBInv (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (LT DT : Array Ct)
    (pbo sbo n : Nat) (l : ZlibNg.Trees.CBL) (H' : Heap) : Prop :=
  ∃ k d', H' = SH H i z b st d' ∧ WrIn d (pbo + st.pending.toNat) (sbo + 3 * k) d' ∧ l.sx.toNat = 3 * k ∧ k ≤ n ∧
    8 * l.pending.toNat + l.bi_valid.toNat =
      8 * st.pending.toNat + st.bi_valid.toInt.toNat + ((blockCosts LT DT d sbo n).take k).sum ∧
    l.bi_valid.toNat < 64 ∧ st.pending.toNat ≤ l.pending.toNat

theorem rd4_eq {d d1 : Array UInt8} {lo o : Nat} (h : ∀ m, lo ≤ m → d1[m]! = d[m]!) (ho : lo ≤ o) :
    rd4 d1 o = rd4 d o := by
  unfold rd4; rw [h o ho, h (o + 1) (by omega), h (o + 2) (by omega), h (o + 3) (by omega)]


theorem rd4_lo (d : Array UInt8) (o : Nat) :
    rd4 d o % 65536 = d[o]!.toNat + 256 * d[o + 1]!.toNat ∧ rd4 d o / 65536 % 256 = d[o + 2]!.toNat := by
  have := d[o]!.toNat_lt; have := d[o + 1]!.toNat_lt; have := d[o + 2]!.toNat_lt; have := d[o + 3]!.toNat_lt
  unfold rd4; omega

theorem rd8_digits (d : Array UInt8) (o : Nat) :
    (rd4 d o + 2 ^ 32 * rd4 d (o + 4)) % 65536 = d[o]!.toNat + 256 * d[o + 1]!.toNat ∧
    (rd4 d o + 2 ^ 32 * rd4 d (o + 4)) / 2 ^ 16 % 256 = d[o + 2]!.toNat ∧
    (rd4 d o + 2 ^ 32 * rd4 d (o + 4)) / 2 ^ 24 % 65536 = d[o + 3]!.toNat + 256 * d[o + 4]!.toNat ∧
    (rd4 d o + 2 ^ 32 * rd4 d (o + 4)) / 2 ^ 40 % 256 = d[o + 5]!.toNat := by
  have := d[o]!.toNat_lt; have := d[o + 1]!.toNat_lt; have := d[o + 2]!.toNat_lt; have := d[o + 3]!.toNat_lt
  have := d[o + 4]!.toNat_lt; have := d[o + 5]!.toNat_lt; have := d[o + 6]!.toNat_lt; have := d[o + 7]!.toNat_lt
  unfold rd4
  simp only [show o + 4 + 1 = o + 5 by omega, show o + 4 + 2 = o + 6 by omega, show o + 4 + 3 = o + 7 by omega]
  omega

theorem matchCost_le (LT DT : Array Ct) (lc dm : Nat) (hlc : lc < 256) (hdm : dm < 32768)
    (hl15 : (LT[(zng_length_code[lc]!).toNat + 257]!).dl.toNat ≤ 15) (hd15 : (DT[dCodeOf dm]!).dl.toNat ≤ 15) :
    matchCost LT DT lc dm ≤ 48 := by
  have hc : (zng_length_code[lc]!).toNat < 29 := UInt8.lt_iff_toNat_lt.mp (lc_lt ⟨lc, hlc⟩)
  have h1 := hl15
  have h2 := lm_ext ⟨_, hc⟩
  have h3 := dCodeOf_lt dm hdm
  have h4 := hd15
  have h5 := (dm_ext ⟨_, h3⟩).1
  simp only at h2 h5
  unfold matchCost; omega

theorem merge_ok {F : Heap → Prop} {lp : CtPtr} {LT : Array Ct} (hl : TreeRd F lp LT 286) {H' : Heap} (hF : F H')
    (b : Nat) (c : Nat) (hc : c < 286) (bits : UInt64) (nb : UInt32) (hn : nb.toNat < 64) :
    ∃ r : UInt64 × UInt32, ZlibNg.TreesEmit.send_code_merge (some b) (c : Int) lp bits nb H' = .ok (r, H') ∧
      r.2.toNat = nb.toNat + (LT[c]!).dl.toNat := by
  refine ⟨(bits ||| ((LT[c]!).fc.toUInt64 <<< nb.toUInt64), nb + (LT[c]!).dl.toUInt32), ?_, ?_⟩
  · unfold ZlibNg.TreesEmit.send_code_merge ZlibNg.TreesEmit.send_bits_merge
    simp only [bind_app, hl.fc hF c hc, hl.dl hF c hc, shl_ok _ _ hn]
    rfl
  · dsimp only
    rw [UInt32.toNat_add, UInt16.toNat_toUInt32]
    have := (LT[c]!).dl.toNat_lt
    omega

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}


theorem u32_add (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem cb_fin {LT DT : Array Ct} {pbo sbo n k k' : Nat} {d1 : Array UInt8}
    (w2 : WrIn d (pbo + st.pending.toNat) (sbo + 3 * k) d1) (hkk : k < k') (hk' : k' ≤ n) (lsx sx : UInt32)
    (bb : UInt64) (bv p : UInt32) (hl : lsx.toNat = 3 * k) (hsx : sx.toNat = 3 * k')
    (hacc : 8 * p.toNat + bv.toNat =
      8 * st.pending.toNat + st.bi_valid.toInt.toNat + ((blockCosts LT DT d sbo n).take k').sum)
    (h55 : bv.toNat < 64) (hp : st.pending.toNat ≤ p.toNat) :
    CBInv H i z b st d LT DT pbo sbo n ⟨sx, bb, bv, p⟩ (SH H i z b st d1) ∧ lsx.toNat < sx.toNat :=
  ⟨⟨k', d1, rfl, w2.widen (Nat.le_refl _) (by omega), hsx, hk', hacc, h55, hp⟩, by omega⟩

theorem take_succ_cost (LT DT : Array Ct) (d : Array UInt8) (sbo n k : Nat) (hk : k < n) :
    ((blockCosts LT DT d sbo n).take (k + 1)).sum = ((blockCosts LT DT d sbo n).take k).sum + symCost LT DT d sbo k :=
  (blockCosts_take LT DT d sbo n k (by omega)).resolve_right (by omega)

theorem cb_body {lp dp : CtPtr} {LT DT : Array Ct} {pbo sbo n : Nat}
    (C : CBCtx H i z b st d lp dp LT DT pbo sbo n) (l : ZlibNg.Trees.CBL) (H' : Heap)
    (hI : CBInv H i z b st d LT DT pbo sbo n l H') (hlt : l.sx.toNat < 3 * n) :
    Sat H' (cbBody (some b) lp dp st.sym_next (.ref (.heap b) sbo) l)
      (fun l1 H1 => CBInv H i z b st d LT DT pbo sbo n l1 H1 ∧ l.sx.toNat < l1.sx.toNat) := by
  obtain ⟨k, d', rfl, w, hsx, hkn, hacc, hb55, hp0⟩ := hI
  have hk : k < n := by omega
  have hB := C.hend; have hN := C.hn; have hL := C.hlb; have hS := C.hsbo
  have hsz : d'.size = d.size := w.1
  have hrb := room_before C.budget k l.pending.toNat (by omega)
  unfold cbBody
  refine Sat.bind (Sat.mono (flush_SH C.hpb l.bi_buf l.bi_valid l.pending (by omega) (by omega) (by omega)) ?_)
  rintro ⟨bb1, bv1, p1⟩ _ ⟨d1, rfl, w1, hp1, hbv1⟩
  dsimp only at hp1 hbv1 ⊢
  have w2 : WrIn d (pbo + st.pending.toNat) (sbo + 3 * k) d1 := w.trans w1 (by omega) (by omega)
  have hsz1 : d1.size = d.size := w2.1
  have hby : ∀ m, sbo + 3 * k ≤ m → d1[m]! = d[m]! := fun m hm => w2.2 m (Or.inr hm)
  have ea := addI_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d1) (off := sbo) (l.sx.toNat : Int)
    (by omega) (by omega)
  rw [show ((sbo : Int) + (l.sx.toNat : Int)).toNat = sbo + 3 * k by omega] at ea
  obtain ⟨v, ev, hv⟩ := memread4_val (H := H) (i := i) (z := z) (b := b) (st := st) (d := d1) (o := sbo + 3 * k)
    (by omega)
  rw [rd4_eq hby (Nat.le_refl _)] at hv
  refine Sat.bind (Sat.of_eq ea (Sat.bind (Sat.of_eq ev ?_)))
  obtain ⟨hlo, hlc2⟩ := rd4_lo d (sbo + 3 * k)
  have hdv : (v &&& 65535).toNat = symDist d sbo k := by
    rw [and_ffff, hv, hlo]; rfl
  have hlcv : (v >>> 16 &&& 255).toNat = d[sbo + 3 * k + 2]!.toNat := by rw [shr16_ff, hv, hlc2]
  have hlcN : (d[sbo + 3 * k + 2]!).toNat < 256 := UInt8.toNat_lt _
  have hlci : (v >>> 16 &&& 255).toInt32.toInt = ((d[sbo + 3 * k + 2]!.toNat : Nat) : Int) := by
    rw [DeflateAlloc.u32_toInt32_toInt _ (by omega), hlcv]
  have hF : Fam H i z b st (SH H i z b st d1) := ⟨st, d1, rfl, rfl, rfl⟩
  have hck := take_succ_cost LT DT d sbo n k hk
  have hpa : 8 * p1.toNat + bv1.toNat = 8 * l.pending.toNat + l.bi_valid.toNat := by omega
  have hsx3 : (l.sx + 3).toNat = 3 * k + 3 := by rw [u32_add _ _ (by simp; omega)]; simp; omega
  have hsx6 : (l.sx + 3 + 3).toNat = 3 * k + 6 := by rw [u32_add _ _ (by rw [hsx3]; simp; omega), hsx3]; simp
  have hsx9 : (l.sx + 3 + 3 + 3).toNat = 3 * k + 9 := by rw [u32_add _ _ (by rw [hsx6]; simp; omega), hsx6]; simp
  have hp1 : st.pending.toNat ≤ p1.toNat := by omega
  split
  · rename_i hz
    have hz' : symDist d sbo k = 0 := by
      rw [← hdv, beq_iff_eq.mp hz]; rfl
    have hc0 : symCost LT DT d sbo k = (LT[d[sbo + 3 * k + 2]!.toNat]!).dl.toNat := by simp [symCost, hz']
    have hl1 : (LT[d[sbo + 3 * k + 2]!.toNat]!).dl.toNat ≤ 15 := by
      have := (C.hu15.2 k hk).1; simpa only [symLCode, hz', ↓reduceIte] using this
    obtain ⟨r1, e1, hr1⟩ := merge_ok C.hl hF b _ (show d[sbo + 3 * k + 2]!.toNat < 286 by omega) 0 0 (by decide)
    rw [hlci]
    refine Sat.bind (Sat.of_eq e1 ?_)
    simp only [UInt32.toNat_zero, Nat.zero_add] at hr1
    split
    · rename_i h8
      have h8' : 3 * k + 11 ≤ 3 * n := by
        have := UInt32.le_iff_toNat_le.mp h8
        rw [u32_add _ _ (by rw [hsx3]; simp; omega), hsx3, C.hsn] at this; simpa using this
      have ea2 := addI_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d1) (off := sbo)
        ((l.sx + 3).toNat : Int) (by omega) (by omega)
      rw [show ((sbo : Int) + ((l.sx + 3).toNat : Int)).toNat = sbo + 3 * k + 3 by omega] at ea2
      obtain ⟨v8, e8, h8v⟩ := memread8_val (H := H) (i := i) (z := z) (b := b) (st := st) (d := d1)
        (o := sbo + 3 * k + 3) (by omega)
      rw [rd4_eq hby (by omega), rd4_eq hby (by omega)] at h8v
      obtain ⟨g0, g2, g3, g5⟩ := rd8_digits d (sbo + 3 * k + 3)
      refine Sat.bind (Sat.of_eq ea2 (Sat.bind (Sat.of_eq e8 ?_)))
      have hck1 : ((blockCosts LT DT d sbo n).take (k + 2)).sum =
          ((blockCosts LT DT d sbo n).take (k + 1)).sum + symCost LT DT d sbo (k + 1) :=
        take_succ_cost LT DT d sbo n (k + 1) (by omega)
      split
      · rename_i hz2
        have hz2' : symDist d sbo (k + 1) = 0 := by
          have e := congrArg UInt16.toNat (beq_iff_eq.mp hz2)
          rw [UInt64.toNat_toUInt16, h8v, g0] at e
          unfold symDist; rw [show sbo + 3 * (k + 1) = sbo + 3 * k + 3 by omega]; simpa using e
        have hc1 : symCost LT DT d sbo (k + 1) = (LT[d[sbo + 3 * k + 3 + 2]!.toNat]!).dl.toNat := by
          simp only [symCost, hz2', ↓reduceIte, show sbo + 3 * (k + 1) + 2 = sbo + 3 * k + 3 + 2 by omega]
        have hlc2v : (v8 >>> 16 &&& 255).toUInt32.toNat = d[sbo + 3 * k + 3 + 2]!.toNat := by
          rw [shr_ff64 v8 16 (by decide), h8v]; exact g2
        have hlN2 : (d[sbo + 3 * k + 3 + 2]!).toNat < 256 := UInt8.toNat_lt _
        have hl2 : (LT[d[sbo + 3 * k + 3 + 2]!.toNat]!).dl.toNat ≤ 15 := by
          have := (C.hu15.2 (k + 1) (by omega)).1
          simpa only [symLCode, hz2', ↓reduceIte, show sbo + 3 * (k + 1) + 2 = sbo + 3 * k + 3 + 2 by omega] using this
        obtain ⟨r2, e2, hr2⟩ := merge_ok C.hl hF b _ (show d[sbo + 3 * k + 3 + 2]!.toNat < 286 by omega) r1.1 r1.2
          (by omega)
        rw [hlc2v]
        refine Sat.bind (Sat.of_eq e2 ?_)
        have hck2 : ((blockCosts LT DT d sbo n).take (k + 3)).sum =
            ((blockCosts LT DT d sbo n).take (k + 2)).sum + symCost LT DT d sbo (k + 2) :=
          take_succ_cost LT DT d sbo n (k + 2) (by omega)
        split
        · rename_i hm
          have hz3 : symDist d sbo (k + 2) = 0 := by
            have e := (lit3_mask v8).mp (beq_iff_eq.mp hm)
            rw [h8v, g3] at e
            unfold symDist; rw [show sbo + 3 * (k + 2) = sbo + 3 * k + 3 + 3 by omega]; omega
          have hc2 : symCost LT DT d sbo (k + 2) = (LT[d[sbo + 3 * k + 3 + 5]!.toNat]!).dl.toNat := by
            simp only [symCost, hz3, ↓reduceIte, show sbo + 3 * (k + 2) + 2 = sbo + 3 * k + 3 + 5 by omega]
          have hlc3v : (v8 >>> 40 &&& 255).toUInt32.toNat = d[sbo + 3 * k + 3 + 5]!.toNat := by
            rw [shr_ff64 v8 40 (by decide), h8v]; exact g5
          have hlN3 : (d[sbo + 3 * k + 3 + 5]!).toNat < 256 := UInt8.toNat_lt _
          have hl3 : (LT[d[sbo + 3 * k + 3 + 5]!.toNat]!).dl.toNat ≤ 15 := by
            have := (C.hu15.2 (k + 2) (by omega)).1
            simpa only [symLCode, hz3, ↓reduceIte, show sbo + 3 * (k + 2) + 2 = sbo + 3 * k + 3 + 5 by omega] using this
          obtain ⟨r3, e3, hr3⟩ := merge_ok C.hl hF b _ (show d[sbo + 3 * k + 3 + 5]!.toNat < 286 by omega) r2.1
            r2.2 (by omega)
          rw [hlc3v]
          refine Sat.bind (Sat.of_eq e3 ?_)
          refine Sat.bind (Sat.of_eq (shl_ok _ _ (by omega) _) ?_)
          refine Sat.pure (cb_fin w2 (show k < k + 3 by omega) (by omega) l.sx _ _ _ _ hsx ?_ ?_ ?_ hp1)
          · exact hsx9
          · rw [u32_add _ _ (by omega), hck2, hck1, hck]
            omega
          · rw [u32_add _ _ (by omega)]; omega
        · refine Sat.bind (Sat.of_eq (shl_ok _ _ (by omega) _) ?_)
          refine Sat.pure (cb_fin w2 (show k < k + 2 by omega) (by omega) l.sx _ _ _ _ hsx ?_ ?_ ?_ hp1)
          · exact hsx6
          · rw [u32_add _ _ (by omega), hck1, hck]
            omega
          · rw [u32_add _ _ (by omega)]; omega
      · refine Sat.bind (Sat.of_eq (shl_ok _ _ (by omega) _) ?_)
        refine Sat.pure (cb_fin w2 (show k < k + 1 by omega) (by omega) l.sx _ _ _ _ hsx hsx3 ?_ ?_ hp1)
        · rw [u32_add _ _ (by omega), hck]; omega
        · rw [u32_add _ _ (by omega)]; omega
    · refine Sat.bind (Sat.of_eq (shl_ok _ _ (by omega) _) ?_)
      refine Sat.pure (cb_fin w2 (show k < k + 1 by omega) (by omega) l.sx _ _ _ _ hsx hsx3 ?_ ?_ hp1)
      · rw [u32_add _ _ (by omega), hck]; omega
      · rw [u32_add _ _ (by omega)]; omega
  · rename_i hz
    have hz' : symDist d sbo k ≠ 0 := by
      intro e; apply hz; rw [beq_iff_eq, ← UInt32.toNat_inj, hdv, e]; rfl
    have hd2 := C.hdist k hk
    have hc0 : symCost LT DT d sbo k = matchCost LT DT d[sbo + 3 * k + 2]!.toNat (symDist d sbo k - 1) := by
      simp [symCost, hz']
    have hu1 : (LT[(zng_length_code[d[sbo + 3 * k + 2]!.toNat]!).toNat + 257]!).dl.toNat ≤ 15 := by
      have := (C.hu15.2 k hk).1; simpa only [symLCode, hz', ↓reduceIte] using this
    have hu2 := (C.hu15.2 k hk).2 hz'
    have hmc := matchCost_le LT DT _ (symDist d sbo k - 1) hlcN (by omega) hu1 hu2
    rw [toInt32_toUInt32]
    refine Sat.bind (Sat.mono (assemble_gen C.hl C.hd hF _ _ (by omega) (by omega) (by omega) (by rw [hlcv]; exact hu1)
      (by rw [hdv]; exact hu2)) ?_)
    rintro ⟨mb, ml⟩ _ ⟨rfl, hml⟩
    rw [hlcv, hdv] at hml
    dsimp only at hml
    unfold ZlibNg.TreesEmit.send_bits_merge
    refine Sat.bind (Sat.bind (Sat.of_eq (shl_ok _ _ (by omega) _) ?_))
    refine Sat.pure ?_
    refine Sat.pure (cb_fin w2 (show k < k + 1 by omega) (by omega) l.sx _ _ _ _ hsx hsx3 ?_ ?_ hp1)
    · dsimp only; rw [u32_add _ _ (by omega), hck]; omega
    · dsimp only; rw [u32_add _ _ (by omega)]; omega

end

/-- `do body while (cond)` over a changing heap, with a decreasing measure (as `sat_cdoWhile` of
`Proof/inffast.base.lean`). -/
theorem sat_cdoWhile' {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (I : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (body s) (fun s1 H1 => Sat H1 (cond s1) (fun cs H2 =>
      (cs.1 = true → I cs.2 H2 ∧ μ cs.2 < μ s) ∧ (cs.1 = false → Q cs.2 H2))))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s < fuel) : Sat H (cdoWhile body cond s) Q := by
  unfold cdoWhile
  suffices ∀ n s H, I s H → μ s < n → Sat H (cdoWhile.go body cond n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨s1, H1, eb, ⟨⟨c, s2⟩, H2, ec, ht, hf⟩⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s2, H2, by simp [cdoWhile.go, bind_app, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      simp only at hI2 hμ2
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cdoWhile.go, bind_app, eb, ec, eg], q⟩

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- What the symbol loop leaves: every symbol consumed, the bytes changed only below `sym_buf + sym_next`, the bits of
all symbols counted. -/
def CBExit (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (LT DT : Array Ct)
    (pbo sbo n : Nat) (l : ZlibNg.Trees.CBL) (H' : Heap) : Prop :=
  ∃ d', H' = SH H i z b st d' ∧ WrIn d (pbo + st.pending.toNat) (sbo + 3 * n) d' ∧
    8 * l.pending.toNat + l.bi_valid.toNat =
      8 * st.pending.toNat + st.bi_valid.toInt.toNat + (blockCosts LT DT d sbo n).sum ∧
    l.bi_valid.toNat < 64 ∧ st.pending.toNat ≤ l.pending.toNat

theorem cb_loop {lp dp : CtPtr} {LT DT : Array Ct} {pbo sbo n : Nat}
    (C : CBCtx H i z b st d lp dp LT DT pbo sbo n) (hn : n ≠ 0) (bb : UInt64) :
    Sat (SH H i z b st d) (cdoWhile (cbBody (some b) lp dp st.sym_next (.ref (.heap b) sbo))
        (fun (l : ZlibNg.Trees.CBL) => pure (l.sx < st.sym_next, l))
        ⟨0, bb, st.bi_valid.toUInt32, st.pending⟩)
      (CBExit H i z b st d LT DT pbo sbo n) := by
  have hv := toU32 _ C.v0
  have hv64 := C.v64
  have hpb := C.budget
  unfold Budget at hpb
  refine sat_cdoWhile' (fun l H' => CBInv H i z b st d LT DT pbo sbo n l H' ∧ l.sx.toNat < 3 * n)
    (fun l => 3 * n - l.sx.toNat) _ ?_ ⟨⟨0, d, rfl, WrIn.refl _ _ _, rfl, by omega, by simp [hv], by dsimp only; rw [hv]; omega,
      Nat.le_refl _⟩, by simp; omega⟩ (by simp [fuel]; have := C.hn; have := C.hlb; omega)
  rintro l H' ⟨hI, hlt⟩
  refine Sat.mono (cb_body C l H' hI hlt) ?_
  rintro l1 H1 ⟨hI1, hlt1⟩
  refine Sat.pure ⟨fun hc => ⟨⟨hI1, ?_⟩, ?_⟩, fun hc => ?_⟩
  · have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc); rw [C.hsn] at this; exact this
  · have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hc); rw [C.hsn] at this; dsimp only; omega
  · have hc' : ¬ l1.sx < st.sym_next := fun h => by simp [h] at hc
    have hge : 3 * n ≤ l1.sx.toNat := by
      have := mt UInt32.lt_iff_toNat_lt.mpr hc'; rw [C.hsn] at this; omega
    obtain ⟨k, d', rfl, w, hsx, hkn, hacc, h55, hp⟩ := hI1
    obtain rfl : k = n := by omega
    refine ⟨d', rfl, w, ?_, h55, hp⟩
    rw [hacc, List.take_of_length_le (by rw [blockCosts_length]; exact Nat.le_refl _)]

end

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- What `compress_block` leaves: the pending count and the bit buffer advanced by exactly the bits of the symbols and
the end-of-block code, the bytes changed only in `pending_buf` after the pending bytes, the last 8-byte store inside
`pending_buf`. -/
def CBPost (H : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) (LT DT : Array Ct)
    (pbo sbo n : Nat) (H' : Heap) : Prop :=
  ∃ (np : UInt32) (bb : UInt64) (bv : UInt32) (d' : Array UInt8),
    H' = SH H i z b { st with pending := np, bi_buf := bb, bi_valid := bv.toInt32 } d' ∧
    WrIn d (pbo + st.pending.toNat) (pbo + 4 * st.lit_bufsize.toNat + 9) d' ∧
    8 * np.toNat + bv.toNat = 8 * st.pending.toNat + st.bi_valid.toInt.toNat + (blockCosts LT DT d sbo n).sum +
      (LT[256]!).dl.toNat ∧
    bv.toNat < 64 ∧ st.pending.toNat ≤ np.toNat ∧ np.toNat + 8 ≤ 4 * st.lit_bufsize.toNat + 9

/-- The tail of `compress_block` after the symbol loop: `s->pending = pending`, the end-of-block code. -/
theorem cb_tail {lp dp : CtPtr} {LT DT : Array Ct} {pbo sbo n : Nat}
    (C : CBCtx H i z b st d lp dp LT DT pbo sbo n) (l : ZlibNg.Trees.CBL) (H' : Heap)
    (hx : CBExit H i z b st d LT DT pbo sbo n l H') :
    Sat H' (do
      wrD (some b) fun s => { s with pending := l.pending }
      let (bi_buf, bi_valid) ← ZlibNg.TreesEmit.zng_emit_end_block (some b) lp 0 l.bi_buf l.bi_valid
      wrD (some b) fun s => { s with bi_buf := bi_buf, bi_valid := bi_valid.toInt32 })
      (fun _ H'' => CBPost H i z b st d LT DT pbo sbo n H'') := by
  have hB := C.hend; have hN := C.hn; have hL := C.hlb; have hS := C.hsbo
  have hbud := C.budget
  obtain ⟨d', rfl, w, hacc, h64, hp⟩ := hx
  have hsz : d'.size = d.size := w.1
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hF : Fam H i z b st (SH H i z b { st with pending := l.pending } d') := ⟨_, d', rfl, rfl, rfl⟩
  have hl256 := C.hu15.1
  have hre := room_end hbud (by rw [blockCosts_length]; omega) l.pending.toNat (by omega)
  unfold ZlibNg.TreesEmit.zng_emit_end_block ZlibNg.TreesEmit.send_code
  refine Sat.bind (Sat.bind (Sat.of_eq (C.hl.fc hF 256 (by decide)) (Sat.bind (Sat.of_eq (C.hl.dl hF 256 (by decide))
    ?_))))
  refine Sat.mono (send_bits_SH (st := { st with pending := l.pending }) C.hpb _ _ _ _ h64
    (by simp only [UInt16.toNat_toUInt32]; omega) (by dsimp only; omega) (by dsimp only; omega)) ?_
  rintro ⟨r1, r2⟩ _ ⟨np, d2, rfl, w2, hacc2, hr2, hle, hge⟩
  dsimp only at w2 hacc2 hr2 hle hge
  simp only [UInt16.toNat_toUInt32] at hacc2
  have hre2 := room_end hbud (by rw [blockCosts_length]; omega) np.toNat (by omega)
  refine Sat.of_eq (wrD_SH _) ⟨np, r1, r2, d2, rfl, ?_, ?_, hr2, by omega, by omega⟩
  · exact (w.widen (Nat.le_refl _) (by omega)).trans w2 (by omega) (by omega)
  · omega

/-- `compress_block` for trees that read as `LT` / `DT` with code lengths at most 15, under the overlay budget of
`CBCtx`: no fault, `CBPost`. -/
theorem compress_SH {lp dp : CtPtr} {LT DT : Array Ct} {pbo sbo n : Nat}
    (C : CBCtx H i z b st d lp dp LT DT pbo sbo n) :
    Sat (SH H i z b st d) (ZlibNg.Trees.compress_block (some b) lp dp)
      (fun _ H' => CBPost H i z b st d LT DT pbo sbo n H') := by
  rw [cbBody_eq]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (ival_get C.hsb _) ?_)))
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  dsimp only
  split
  · rename_i hn0
    have hn : n ≠ 0 := by
      intro e; apply (bne_iff_ne.mp hn0); apply UInt32.toNat_inj.mp; rw [C.hsn, e]; rfl
    exact Sat.bind (Sat.mono (cb_loop C hn _) (fun l H' hx => cb_tail C l H' hx))
  · rename_i hn0
    have hn : n = 0 := by
      have := C.hsn; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hn0; rw [hn0] at this; simp at this; omega
    subst hn
    have hv := toU32 _ C.v0
    exact cb_tail C _ _ ⟨d, rfl, WrIn.refl _ _ _, by simp [blockCosts, hv], by dsimp only; rw [hv]; have := C.v64; omega,
      Nat.le_refl _⟩

end

/-! ## The static trees -/

theorem static_l15 : ∀ k, k < 286 → (static_ltree[k]!).dl.toNat ≤ 15 := fun k hk => by
  have := UInt16.le_iff_toNat_le.mp (sl_len ⟨k, by omega⟩); simp only [show (9 : UInt16).toNat = 9 from rfl] at this; omega

theorem static_d15 : ∀ k, k < 30 → (static_dtree[k]!).dl.toNat ≤ 15 := fun k hk => by
  have := UInt16.le_iff_toNat_le.mp (dm_ext ⟨k, hk⟩).2; simp only [show (5 : UInt16).toNat = 5 from rfl] at this; omega

theorem symLCode_lt (d : Array UInt8) (sbo j : Nat) : symLCode d sbo j < 286 := by
  have := (d[sbo + 3 * j + 2]!).toNat_lt
  unfold symLCode; split
  · omega
  · have : (zng_length_code[d[sbo + 3 * j + 2]!.toNat]!).toNat < 29 := UInt8.lt_iff_toNat_lt.mp (lc_lt ⟨_, this⟩)
    omega

/-- With the static trees every code length is at most 15. -/
theorem static_used15 (d : Array UInt8) (sbo n : Nat) (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) :
    UsedLe15 static_ltree static_dtree d sbo n :=
  ⟨static_l15 256 (by decide), fun j hj => ⟨static_l15 _ (symLCode_lt d sbo j),
    fun h0 => static_d15 _ (dCodeOf_lt _ (by have := hdist j hj; omega))⟩⟩

/-- With the static trees a symbol costs at most 31 bits. -/
theorem static_symCost (d : Array UInt8) (sbo j : Nat) (hd : symDist d sbo j ≤ 32768) :
    symCost static_ltree static_dtree d sbo j ≤ 31 := by
  have hlc : (d[sbo + 3 * j + 2]!).toNat < 256 := UInt8.toNat_lt _
  unfold symCost
  split
  · have := TreesOverlayP.static_lit_cost ⟨_, hlc⟩; simp only at this; omega
  · rename_i h
    exact TreesOverlayP.staticMatchCost_le _ _ hlc (dCodeOf_lt _ (by omega))

/-- The overlay budget of a static block: at most 66 bits before the first symbol (up to 63 waiting bits and the 3
header bits), at most `lit_bufsize - 1` symbols, `lit_bufsize ≥ 52`. -/
theorem static_cb_budget (d : Array UInt8) (sbo n B t0 : Nat) (hB : 52 ≤ B) (hn : n + 1 ≤ B) (ht : t0 ≤ 66)
    (hd : ∀ j, j < n → symDist d sbo j ≤ 32768) : Budget B t0 (blockCosts static_ltree static_dtree d sbo n) := by
  have h := bitExcess_le 7 (blockCosts static_ltree static_dtree d sbo n) (fun c hc => by
    simp only [blockCosts, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    have := static_symCost d sbo j (hd j hj); omega)
  rw [blockCosts_length] at h
  unfold Budget; omega

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

/-- `compress_block` with the static trees: the setting of `CBCtx`, its budget discharged by `static_cb_budget`. -/
theorem compress_static_SH {pbo sbo n : Nat} (hpb : st.pending_buf = .val (.ref (.heap b) pbo))
    (hsb : st.sym_buf = .val (.ref (.heap b) sbo)) (hsn : st.sym_next.toNat = 3 * n)
    (hsbo : sbo = pbo + st.lit_bufsize.toNat + 8) (hend : pbo + 4 * st.lit_bufsize.toNat + 9 ≤ d.size)
    (hn : n + 1 ≤ st.lit_bufsize.toNat) (hB : 52 ≤ st.lit_bufsize.toNat) (hlb : st.lit_bufsize.toNat ≤ 32768)
    (hdist : ∀ j, j < n → symDist d sbo j ≤ 32768) (v0 : 0 ≤ st.bi_valid.toInt) (v64 : st.bi_valid.toInt < 64)
    (ht : 8 * st.pending.toNat + st.bi_valid.toInt.toNat ≤ 66) :
    Sat (SH H i z b st d) (ZlibNg.Trees.compress_block (some b) (.ref .static_ltree 0) (.ref .static_dtree 0))
      (fun _ H' => CBPost H i z b st d static_ltree static_dtree pbo sbo n H') :=
  compress_SH ⟨hpb, hsb, hsn, hsbo, hend, hn, hlb,
    fun H' _ k hk => ctGet_sl H' k (by omega), treeRd_sd _, static_used15 d sbo n hdist, hdist, v0, v64,
    static_cb_budget d sbo n _ _ hB hn ht hdist⟩

end

end ZlibNgF.Proof.TreesCompress
