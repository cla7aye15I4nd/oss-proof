import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `zutil.c` safety, alignment, and functional specifications (`ZlibNgF`)
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Zutil
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

private theorem u32_eq_of_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec va =>
  cases b with | ofBitVec vb =>
  congr 1
  exact BitVec.eq_of_toNat_eq h

private theorem i32_eq_of_toInt {a b : Int32} (h : a.toInt = b.toInt) : a = b := by
  have := congrArg Int32.ofInt h
  simpa using this

private theorem i32_lt_toInt {a b : Int32} : (a < b) ↔ (a.toInt < b.toInt) :=
  Int32.lt_iff_toInt_lt

private theorem strLitRef_of_getElem (h : Heap) (s : String) (idx : Nat)
    (hs : strTable[idx]? = some s) :
    ∃ p, C.run (strLitRef s) h = .ok (p, h) ∧ StaticCString h p s := by
  have hmem : s ∈ strTable := by
    rw [Array.getElem?_eq_some_iff] at hs
    obtain ⟨hlt, rfl⟩ := hs
    exact Array.getElem_mem hlt
  cases hx : strTable.findIdx? (· == s) with
  | none =>
    exfalso
    rw [Array.findIdx?_eq_none_iff] at hx
    have := hx s hmem
    simp at this
  | some j =>
    have hj_some : strTable[j]? = some s := by
      rw [Array.findIdx?_eq_some_iff_getElem] at hx
      obtain ⟨hj_lt, hj_eq, _⟩ := hx
      rw [Array.getElem?_eq_getElem hj_lt]
      have : strTable[j] = s := beq_iff_eq.mp hj_eq
      rw [this]
    refine ⟨.ref (.str j) 0, ?_, j, rfl, hj_some, ?_⟩
    · simp only [C.run, C.strLitRef, hx]
    · simp only [Space.get, Heap.getBytes, hj_some, Option.map_some]

theorem zlibVersion_functional : Goal.zlibVersion_functional := by
  intro h
  exact strLitRef_of_getElem h "1.3.2.zlib-ng" 0 rfl

theorem zlibVersion_safety : Goal.zlibVersion_safety := by
  intro h
  obtain ⟨p, hp, _⟩ := zlibVersion_functional h
  exact ⟨p, hp⟩

theorem zlibCompileFlags_functional : Goal.zlibCompileFlags_functional := by
  intro h
  unfold ZlibNg.Zutil.zlibCompileFlags
  dsimp only [C.run, Pure.pure]
  congr 1

theorem zlibCompileFlags_safety : Goal.zlibCompileFlags_safety := by
  intro h
  exact ⟨0xa9, zlibCompileFlags_functional h⟩

theorem zError_functional : Goal.zError_functional := by
  intro h err
  unfold ZlibNg.Zutil.zError expectedZError
  by_cases hlt : err < -6
  · have hlti : err.toInt < -6 := by
      have := i32_lt_toInt.mp hlt
      simpa using this
    have ne : ∀ (k : Int32), -6 ≤ k.toInt → (err == k) = false := by
      intro k hk
      apply beq_false_of_ne
      intro heq; subst heq; omega
    have n2 : (err == 2) = false := ne 2 (by decide)
    have n1 : (err == 1) = false := ne 1 (by decide)
    have n0 : (err == 0) = false := ne 0 (by decide)
    have nm1 : (err == -1) = false := ne (-1) (by decide)
    have nm2 : (err == -2) = false := ne (-2) (by decide)
    have nm3 : (err == -3) = false := ne (-3) (by decide)
    have nm4 : (err == -4) = false := ne (-4) (by decide)
    have nm5 : (err == -5) = false := ne (-5) (by decide)
    have nm6 : (err == -6) = false := ne (-6) (by decide)
    simp only [hlt, decide_true, Bool.true_or, ↓reduceIte,
      n2, n1, n0, nm1, nm2, nm3, nm4, nm5, nm6, Bool.false_eq_true]
    have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 9).toNat]? = some "" := rfl
    rw [hm]
    exact strLitRef_of_getElem h "" 4 rfl
  · by_cases hgt : err > 2
    · have hgti : (2 : Int) < err.toInt := by
        have := i32_lt_toInt.mp hgt
        simpa using this
      have ne : ∀ (k : Int32), k.toInt ≤ 2 → (err == k) = false := by
        intro k hk
        apply beq_false_of_ne
        intro heq; subst heq; omega
      have n2 : (err == 2) = false := ne 2 (by decide)
      have n1 : (err == 1) = false := ne 1 (by decide)
      have n0 : (err == 0) = false := ne 0 (by decide)
      have nm1 : (err == -1) = false := ne (-1) (by decide)
      have nm2 : (err == -2) = false := ne (-2) (by decide)
      have nm3 : (err == -3) = false := ne (-3) (by decide)
      have nm4 : (err == -4) = false := ne (-4) (by decide)
      have nm5 : (err == -5) = false := ne (-5) (by decide)
      have nm6 : (err == -6) = false := ne (-6) (by decide)
      simp only [hlt, decide_false, hgt, decide_true, Bool.false_or, ↓reduceIte,
        n2, n1, n0, nm1, nm2, nm3, nm4, nm5, nm6, Bool.false_eq_true]
      have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 9).toNat]? = some "" := rfl
      rw [hm]
      exact strLitRef_of_getElem h "" 4 rfl
    · have hge : -6 ≤ err.toInt := by
        have : ¬ (err.toInt < (-6 : Int32).toInt) := fun hc => hlt (i32_lt_toInt.mpr hc)
        have hm6 : (-6 : Int32).toInt = -6 := by decide
        omega
      have hle : err.toInt ≤ 2 := by
        have : ¬ ((2 : Int32).toInt < err.toInt) := fun hc => hgt (i32_lt_toInt.mpr hc)
        have hp2 : (2 : Int32).toInt = 2 := by decide
        omega
      have hcases_int :
          err.toInt = 2 ∨ err.toInt = 1 ∨ err.toInt = 0 ∨ err.toInt = -1 ∨ err.toInt = -2 ∨
          err.toInt = -3 ∨ err.toInt = -4 ∨ err.toInt = -5 ∨ err.toInt = -6 := by
        omega
      rcases hcases_int with h2 | h1 | h0 | hm1 | hm2 | hm3 | hm4 | hm5 | hm6
      · rw [i32_eq_of_toInt (h2.trans (by decide : (2 : Int) = (2 : Int32).toInt))]
        have hd : (if (decide ((2 : Int32) < -6) || decide ((2 : Int32) > 2)) = true then (9 : Int32) else 2 - 2) = 0 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 0).toNat]? = some "need dictionary" := rfl
        simp only [hd, hm, show ((2 : Int32) == 2) = true by decide, ↓reduceIte]
        exact strLitRef_of_getElem h "need dictionary" 2 rfl
      · rw [i32_eq_of_toInt (h1.trans (by decide : (1 : Int) = (1 : Int32).toInt))]
        have hd : (if (decide ((1 : Int32) < -6) || decide ((1 : Int32) > 2)) = true then (9 : Int32) else 2 - 1) = 1 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 1).toNat]? = some "stream end" := rfl
        simp only [hd, hm, show ((1 : Int32) == 2) = false by decide, show ((1 : Int32) == 1) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "stream end" 3 rfl
      · rw [i32_eq_of_toInt (h0.trans (by decide : (0 : Int) = (0 : Int32).toInt))]
        have hd : (if (decide ((0 : Int32) < -6) || decide ((0 : Int32) > 2)) = true then (9 : Int32) else 2 - 0) = 2 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 2).toNat]? = some "" := rfl
        simp only [hd, hm, show ((0 : Int32) == 2) = false by decide, show ((0 : Int32) == 1) = false by decide,
          show ((0 : Int32) == 0) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "" 4 rfl
      · rw [i32_eq_of_toInt (hm1.trans (by decide : (-1 : Int) = (-1 : Int32).toInt))]
        have hd : (if (decide ((-1 : Int32) < -6) || decide ((-1 : Int32) > 2)) = true then (9 : Int32) else 2 - (-1)) = 3 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 3).toNat]? = some "file error" := rfl
        simp only [hd, hm, show ((-1 : Int32) == 2) = false by decide, show ((-1 : Int32) == 1) = false by decide,
          show ((-1 : Int32) == 0) = false by decide, show ((-1 : Int32) == -1) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "file error" 5 rfl
      · rw [i32_eq_of_toInt (hm2.trans (by decide : (-2 : Int) = (-2 : Int32).toInt))]
        have hd : (if (decide ((-2 : Int32) < -6) || decide ((-2 : Int32) > 2)) = true then (9 : Int32) else 2 - (-2)) = 4 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 4).toNat]? = some "stream error" := rfl
        simp only [hd, hm, show ((-2 : Int32) == 2) = false by decide, show ((-2 : Int32) == 1) = false by decide,
          show ((-2 : Int32) == 0) = false by decide, show ((-2 : Int32) == -1) = false by decide,
          show ((-2 : Int32) == -2) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "stream error" 6 rfl
      · rw [i32_eq_of_toInt (hm3.trans (by decide : (-3 : Int) = (-3 : Int32).toInt))]
        have hd : (if (decide ((-3 : Int32) < -6) || decide ((-3 : Int32) > 2)) = true then (9 : Int32) else 2 - (-3)) = 5 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 5).toNat]? = some "data error" := rfl
        simp only [hd, hm, show ((-3 : Int32) == 2) = false by decide, show ((-3 : Int32) == 1) = false by decide,
          show ((-3 : Int32) == 0) = false by decide, show ((-3 : Int32) == -1) = false by decide,
          show ((-3 : Int32) == -2) = false by decide, show ((-3 : Int32) == -3) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "data error" 7 rfl
      · rw [i32_eq_of_toInt (hm4.trans (by decide : (-4 : Int) = (-4 : Int32).toInt))]
        have hd : (if (decide ((-4 : Int32) < -6) || decide ((-4 : Int32) > 2)) = true then (9 : Int32) else 2 - (-4)) = 6 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 6).toNat]? = some "insufficient memory" := rfl
        simp only [hd, hm, show ((-4 : Int32) == 2) = false by decide, show ((-4 : Int32) == 1) = false by decide,
          show ((-4 : Int32) == 0) = false by decide, show ((-4 : Int32) == -1) = false by decide,
          show ((-4 : Int32) == -2) = false by decide, show ((-4 : Int32) == -3) = false by decide,
          show ((-4 : Int32) == -4) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "insufficient memory" 8 rfl
      · rw [i32_eq_of_toInt (hm5.trans (by decide : (-5 : Int) = (-5 : Int32).toInt))]
        have hd : (if (decide ((-5 : Int32) < -6) || decide ((-5 : Int32) > 2)) = true then (9 : Int32) else 2 - (-5)) = 7 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 7).toNat]? = some "buffer error" := rfl
        simp only [hd, hm, show ((-5 : Int32) == 2) = false by decide, show ((-5 : Int32) == 1) = false by decide,
          show ((-5 : Int32) == 0) = false by decide, show ((-5 : Int32) == -1) = false by decide,
          show ((-5 : Int32) == -2) = false by decide, show ((-5 : Int32) == -3) = false by decide,
          show ((-5 : Int32) == -4) = false by decide, show ((-5 : Int32) == -5) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "buffer error" 9 rfl
      · rw [i32_eq_of_toInt (hm6.trans (by decide : (-6 : Int) = (-6 : Int32).toInt))]
        have hd : (if (decide ((-6 : Int32) < -6) || decide ((-6 : Int32) > 2)) = true then (9 : Int32) else 2 - (-6)) = 8 := by decide
        have hm : ZlibNg.Zutil.z_errmsg[(Int32.toInt 8).toNat]? = some "incompatible version" := rfl
        simp only [hd, hm, show ((-6 : Int32) == 2) = false by decide, show ((-6 : Int32) == 1) = false by decide,
          show ((-6 : Int32) == 0) = false by decide, show ((-6 : Int32) == -1) = false by decide,
          show ((-6 : Int32) == -2) = false by decide, show ((-6 : Int32) == -3) = false by decide,
          show ((-6 : Int32) == -4) = false by decide, show ((-6 : Int32) == -5) = false by decide,
          show ((-6 : Int32) == -6) = true by decide, Bool.false_eq_true, ↓reduceIte]
        exact strLitRef_of_getElem h "incompatible version" 10 rfl

theorem zError_safety : Goal.zError_safety := by
  intro h err
  obtain ⟨p, hp, _⟩ := zError_functional h err
  exact ⟨p, hp⟩

theorem zcalloc_zcfree_safety : Goal.zcalloc_zcfree_safety := by
  intro h opq items size
  unfold ZlibNg.Zutil.zcalloc ZlibNg.Zutil.zcfree
  by_cases hok : h.allocOk h.nalloc = true
  · let n := (items.toUInt64 * size.toUInt64).toNat
    let arr : Array UInt8 := Array.ofFn (n := n) (fun i => Junk.of (h.garbage h.nalloc i.val))
    let h1 : Heap := {
      h with
      bytes := upd h.bytes h.nextBlk (some arr)
      savedPtrs := upd h.savedPtrs h.nextBlk none
      nextBlk := h.nextBlk + 1
      nalloc := h.nalloc + 1
    }
    let h2 : Heap := { h1 with bytes := upd h1.bytes h.nextBlk none, savedPtrs := upd h1.savedPtrs h.nextBlk none }
    refine ⟨.ref (.heap h.nextBlk) 0, h1, h2, ?_, ?_⟩
    · simp only [C.run, C.allocB, hok, ↓reduceIte]; rfl
    · simp only [C.run, C.freeB, h1, upd_same]; rfl
  · have hokf : h.allocOk h.nalloc = false := Bool.eq_false_iff.mpr hok
    let h1 : Heap := { h with nalloc := h.nalloc + 1 }
    refine ⟨.null, h1, h1, ?_, ?_⟩
    · simp only [C.run, C.allocB, hokf, Bool.false_eq_true, ↓reduceIte]; rfl
    · rfl


/-- `ALIGN_DIFF(ptr, align)` of `zng_alloc_aligned` as a function of the address. -/
private def alignDiff (addr : UInt64) (align : UInt32) : UInt64 :=
  (align.toUInt64 - (addr &&& (align - 1).toUInt64)) &&& (align - 1).toUInt64

private theorem align_m1_toNat (align : UInt32) (ha : 1 ≤ align.toNat) :
    (align - 1).toUInt64.toNat = align.toNat - 1 := by
  have h1 : (1 : UInt32) ≤ align := by show (1 : UInt32).toNat ≤ align.toNat; simpa using ha
  rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ h1]
  rfl

private theorem alignDiff_le (addr : UInt64) (align : UInt32) (ha : 1 ≤ align.toNat) :
    (alignDiff addr align).toNat ≤ align.toNat - 1 := by
  unfold alignDiff
  rw [UInt64.toNat_and, align_m1_toNat align ha]
  exact Nat.and_le_right

private theorem zng_alloc_size_toNat (size align : UInt32) (hw : 8 + size.toNat + align.toNat < 2 ^ 32) :
    ((8 : UInt64) + size.toUInt64 + align.toUInt64).toUInt32.toNat = 8 + size.toNat + align.toNat := by
  have hs64 : size.toUInt64.toNat = size.toNat := UInt32.toNat_toUInt64 size
  have ha64 : align.toUInt64.toNat = align.toNat := UInt32.toNat_toUInt64 align
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h1 : ((8 : UInt64) + size.toUInt64).toNat = 8 + size.toNat := by
    rw [UInt64.toNat_add, h8, hs64]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : ((8 : UInt64) + size.toUInt64 + align.toUInt64).toNat = 8 + size.toNat + align.toNat := by
    rw [UInt64.toNat_add, h1, ha64]; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_toUInt32, h2]
  exact Nat.mod_eq_of_lt hw

private theorem ptr_add_ok {r : BRef} {off : Nat} {k : Int} {h : Heap} {a : Array UInt8}
    (hg : Space.get h r = some a)
    (hc : off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)) :
    C.run ((Ptr.ref r off).add k) h = .ok (.ref r ((off : Int) + k).toNat, h) := by
  simp only [C.run, Ptr.add, hg]
  split
  · rfl
  · rename_i hneg; exact absurd hc hneg

/-- `zng_alloc_aligned` when the allocation fails. -/
private theorem zng_alloc_aligned_when_fail (h : Heap) (size align : UInt32) (hokf : h.allocOk h.nalloc = false) :
    C.run (ZlibNg.Zutil.zng_alloc_aligned size align) h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
  unfold ZlibNg.Zutil.zng_alloc_aligned
  have halloc : ∀ n, C.run (allocB n) h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
    intro n
    simp only [C.run, allocB, hokf, Bool.false_eq_true, ↓reduceIte]
  rw [C.run_bind, halloc]
  rfl

/-- Core characterization of `zng_alloc_aligned` when `8 ≤ align`, `8 + size + align` fits in 32 bits and the
allocation succeeds. -/
private theorem zng_alloc_aligned_when_ok
    (h : Heap) (size align : UInt32) (ha8 : 8 ≤ align.toNat) (hw : 8 + size.toNat + align.toNat < 2 ^ 32)
    (hok : h.allocOk h.nalloc = true) :
    let addr0 := h.baseAddr (.heap h.nextBlk)
    let d : UInt64 := alignDiff (addr0 + UInt64.ofNat 0) align
    let off : Nat := if d < 8 then d.toNat + align.toNat else d.toNat
    ∃ h' data,
      C.run (ZlibNg.Zutil.zng_alloc_aligned size align) h = .ok (.ref (.heap h.nextBlk) off, h') ∧
      h'.baseAddr = h.baseAddr ∧
      h'.bytes h.nextBlk = some data ∧
      data.size = 8 + size.toNat + align.toNat ∧
      8 ≤ off ∧
      off + size.toNat ≤ data.size ∧
      C.run (ZlibNg.Zutil.zng_free_aligned (.ref (.heap h.nextBlk) off)) h' =
        .ok ((), { h' with bytes := upd h'.bytes h.nextBlk none, savedPtrs := upd h'.savedPtrs h.nextBlk none }) := by
  intro addr0 d off
  unfold ZlibNg.Zutil.zng_alloc_aligned
  have hasz := zng_alloc_size_toNat size align hw
  let n := 8 + size.toNat + align.toNat
  let arr : Array UInt8 := Array.ofFn (n := n) (fun i => Junk.of (h.garbage h.nalloc i.val))
  have harr_sz : arr.size = n := Array.size_ofFn
  let b := h.nextBlk
  let h1 : Heap := {
    h with
    bytes := upd h.bytes b (some arr)
    savedPtrs := upd h.savedPtrs b none
    nextBlk := b + 1
    nalloc := h.nalloc + 1
  }
  have halloc_step : C.run (allocB ((8 + size.toUInt64 + align.toUInt64).toUInt32.toNat)) h =
      .ok (.ref (.heap b) 0, h1) := by
    rw [hasz]
    simp only [C.run, C.allocB, hok, ↓reduceIte]
    rfl
  rw [C.run_bind, halloc_step]
  dsimp only
  have hnot_null : (Ptr.ref (BRef.heap b) 0 == (.null : BPtr)) = false := rfl
  rw [hnot_null]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hdiff_step : C.run (ZlibNg.Zutil.ALIGN_DIFF (.ref (.heap b) 0) align) h1 = .ok (d, h1) := rfl
  rw [C.run_bind, hdiff_step]
  dsimp only
  have hd_le : d.toNat ≤ align.toNat - 1 := alignDiff_le _ align (by omega)
  have h1_get : Space.get h1 (BRef.heap b) = some arr := by
    simp only [Space.get, Heap.getBytes, h1, upd_same]
  have h1_bytes : h1.bytes b = some arr := by simp only [h1, upd_same]
  have hstep1_cond : 0 ≤ arr.size ∧ 0 ≤ ((0 : Nat) : Int) + (Int.ofNat d.toNat) ∧
      ((0 : Nat) : Int) + (Int.ofNat d.toNat) ≤ (arr.size : Int) := by
    rw [harr_sz]; dsimp [n]; omega
  have hstep1_nat : (((0 : Nat) : Int) + (Int.ofNat d.toNat)).toNat = d.toNat := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hstep1 : C.run ((Ptr.ref (BRef.heap b) 0).add (Int.ofNat d.toNat)) h1 =
      .ok (.ref (.heap b) d.toNat, h1) := by
    rw [ptr_add_ok h1_get hstep1_cond, hstep1_nat]
  rw [C.run_bind, hstep1]
  dsimp only
  have hoff8 : 8 ≤ off := by
    dsimp [off]
    split
    · omega
    · rename_i hn
      have : ¬ (d.toNat < 8) := hn
      omega
  have hoff_sz : off + size.toNat ≤ arr.size := by
    rw [harr_sz]; dsimp [n, off]
    split
    · rename_i ht
      have : d.toNat < 8 := ht
      omega
    · omega
  have hoff_cond : off ≤ arr.size ∧ 0 ≤ (off : Int) + (-8) ∧ (off : Int) + (-8) ≤ (arr.size : Int) := by omega
  have hoff_m8 : ((off : Int) + (-8)).toNat = off - 8 := by omega
  have hslot_cond : (off - 8) + 8 ≤ arr.size := by omega
  let h' : Heap := { h1 with savedPtrs := upd h1.savedPtrs b (some (off - 8, .ref (.heap b) 0)) }
  have hstep_tail : C.run (do
      let return_ptr ← if d < 8 then (Ptr.ref (BRef.heap b) d.toNat).add (Int.ofNat align.toNat)
        else pure (.ref (.heap b) d.toNat)
      let original_ptr ← return_ptr.add (-8)
      storePtrSlot original_ptr (.ref (.heap b) 0)
      return return_ptr) h1 = .ok (.ref (.heap b) off, h') := by
    by_cases had8 : d < 8
    · have had8_nat : d.toNat < 8 := had8
      have hcond2 : d.toNat ≤ arr.size ∧ 0 ≤ (d.toNat : Int) + (Int.ofNat align.toNat) ∧
          (d.toNat : Int) + (Int.ofNat align.toNat) ≤ (arr.size : Int) := by
        rw [harr_sz]; dsimp [n]; omega
      have hnat2 : ((d.toNat : Int) + (Int.ofNat align.toNat)).toNat = off := by
        dsimp [off]; simp only [had8, ↓reduceIte]; omega
      simp only [had8, ↓reduceIte]
      rw [C.run_bind, ptr_add_ok h1_get hcond2, hnat2]
      dsimp only
      rw [C.run_bind, ptr_add_ok h1_get hoff_cond, hoff_m8]
      dsimp only
      have hs4 : C.run (storePtrSlot (.ref (.heap b) (off - 8)) (.ref (.heap b) 0)) h1 = .ok ((), h') := by
        simp only [C.run, storePtrSlot, h1_bytes, hslot_cond, ↓reduceIte]; rfl
      rw [C.run_bind, hs4]
      rfl
    · have hnat2 : d.toNat = off := by dsimp [off]; simp only [had8, ↓reduceIte]
      simp only [had8, ↓reduceIte]
      rw [C.run_bind, C.run_pure, hnat2]
      dsimp only
      rw [C.run_bind, ptr_add_ok h1_get hoff_cond, hoff_m8]
      dsimp only
      have hs4 : C.run (storePtrSlot (.ref (.heap b) (off - 8)) (.ref (.heap b) 0)) h1 = .ok ((), h') := by
        simp only [C.run, storePtrSlot, h1_bytes, hslot_cond, ↓reduceIte]; rfl
      rw [C.run_bind, hs4]
      rfl
  have hp_get : Space.get h' (BRef.heap b) = some arr := by
    simp only [Space.get, Heap.getBytes, h', h1_bytes]
  have hp_bytes : h'.bytes b = some arr := h1_bytes
  have hp_saved : h'.savedPtrs b = some (off - 8, .ref (.heap b) 0) := by
    simp only [h', upd_same]
  refine ⟨h', arr, hstep_tail, rfl, hp_bytes, harr_sz, hoff8, hoff_sz, ?_⟩
  unfold ZlibNg.Zutil.zng_free_aligned
  have hnn : (Ptr.ref (BRef.heap b) off == (.null : BPtr)) = false := rfl
  rw [hnn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [C.run_bind, ptr_add_ok hp_get hoff_cond, hoff_m8]
  dsimp only
  have hf2 : C.run (loadPtrSlot (.ref (.heap b) (off - 8))) h' = .ok (.ref (.heap b) 0, h') := by
    simp only [C.run, loadPtrSlot, hp_bytes, hp_saved, hslot_cond, and_self, ↓reduceIte]
  rw [C.run_bind, hf2]
  dsimp only
  simp only [C.run, freeB, hp_bytes]
  rfl

theorem zng_alloc_aligned_safety : Goal.zng_alloc_aligned_safety := by
  intro h size align ha8 hw
  by_cases hok : h.allocOk h.nalloc = true
  · obtain ⟨h', data, hrun, _, hbytes, _, hoff8, hoff_sz, hfree⟩ :=
      zng_alloc_aligned_when_ok h size align ha8 hw hok
    exact ⟨_, h', hrun, Or.inr ⟨rfl, _, data, rfl, hbytes, hoff8, hoff_sz, hfree⟩⟩
  · have hokf : h.allocOk h.nalloc = false := Bool.eq_false_iff.mpr hok
    exact ⟨.null, { h with nalloc := h.nalloc + 1 }, zng_alloc_aligned_when_fail h size align hokf,
      Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem zng_alloc_aligned_nonvacuous : Goal.zng_alloc_aligned_nonvacuous := by
  obtain ⟨h', data, hrun, _, hbytes, _, hoff8, hoff_sz, _⟩ :=
    zng_alloc_aligned_when_ok Heap.empty 0xc0000000 64 (by decide) (by decide) rfl
  exact ⟨_, h', data, hrun, hbytes, hoff8, hoff_sz⟩

/-- For a power-of-two `align`, `addr + alignDiff addr align` is a multiple of `align`. -/
private theorem alignDiff_pow (addr : UInt64) (align : UInt32) (k : Nat)
    (hpow : align.toNat = 2 ^ k) :
    (alignDiff addr align).toNat = (align.toNat - addr.toNat % align.toNat) % align.toNat := by
  have hpos : 1 ≤ align.toNat := by rw [hpow]; exact Nat.one_le_two_pow
  have hlt64 : align.toNat < 2 ^ 64 := by
    have : align.toNat < 2 ^ 32 := align.toBitVec.isLt
    omega
  have hm1 := align_m1_toNat align hpos
  have hrem : (addr &&& (align - 1).toUInt64).toNat = addr.toNat % align.toNat := by
    rw [UInt64.toNat_and, hm1, hpow, Nat.and_two_pow_sub_one_eq_mod]
  have hrem_lt : addr.toNat % align.toNat < align.toNat := Nat.mod_lt _ (by omega)
  have hsub : (align.toUInt64 - (addr &&& (align - 1).toUInt64)).toNat = align.toNat - addr.toNat % align.toNat := by
    have hle : (addr &&& (align - 1).toUInt64) ≤ align.toUInt64 := by
      show (addr &&& (align - 1).toUInt64).toNat ≤ align.toUInt64.toNat
      rw [hrem, UInt32.toNat_toUInt64]; omega
    rw [UInt64.toNat_sub_of_le _ _ hle, hrem, UInt32.toNat_toUInt64]
  unfold alignDiff
  rw [UInt64.toNat_and, hsub, hm1, hpow, Nat.and_two_pow_sub_one_eq_mod]

theorem zng_alloc_aligned_alignment : Goal.zng_alloc_aligned_alignment := by
  intro h size align k hk3 hk31 hpow hw ret h' hrun hne
  have ha8 : 8 ≤ align.toNat := by
    have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk3
    omega
  by_cases hok : h.allocOk h.nalloc = true
  · obtain ⟨h_ok, _, hrun_ok, hbase_eq, _, _, _, _, _⟩ :=
      zng_alloc_aligned_when_ok h size align ha8 hw hok
    rw [hrun_ok] at hrun
    injection hrun with hpair
    injection hpair with hret hh'
    subst hret hh'
    let addr0 := h.baseAddr (.heap h.nextBlk)
    let d : UInt64 := alignDiff (addr0 + UInt64.ofNat 0) align
    let off : Nat := if d < 8 then d.toNat + align.toNat else d.toNat
    have hzero : addr0 + UInt64.ofNat 0 = addr0 := UInt64.add_zero addr0
    have hd_eq : d.toNat = (align.toNat - addr0.toNat % align.toNat) % align.toNat := by
      have := alignDiff_pow addr0 align k hpow
      show (alignDiff (addr0 + UInt64.ofNat 0) align).toNat = _
      rw [hzero]
      exact this
    have hd_le : d.toNat ≤ align.toNat - 1 := alignDiff_le _ align (by omega)
    have hdvd64 : align.toNat ∣ 2 ^ 64 := by
      rw [hpow]
      exact ⟨2 ^ (64 - k), by rw [← Nat.pow_add]; congr 1; omega⟩
    have hrem_lt : addr0.toNat % align.toNat < align.toNat := Nat.mod_lt _ (by omega)
    have hoff_lt64 : off < 2 ^ 64 := by
      have : align.toNat < 2 ^ 32 := align.toBitVec.isLt
      dsimp [off]
      split <;> omega
    refine ⟨h_ok.baseAddr (.heap h.nextBlk) + UInt64.ofNat off, rfl, ?_⟩
    rw [hbase_eq]
    change (addr0 + UInt64.ofNat off).toNat % align.toNat = 0
    have hoff_nat : (UInt64.ofNat off).toNat = off := by
      show (BitVec.ofNat 64 off).toNat = off
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hoff_lt64
    rw [UInt64.toNat_add, hoff_nat, Nat.mod_mod_of_dvd _ hdvd64]
    have hbase : (addr0.toNat + d.toNat) % align.toNat = 0 := by
      rw [hd_eq, Nat.add_mod, Nat.mod_mod]
      by_cases hr0 : addr0.toNat % align.toNat = 0
      · rw [hr0, Nat.sub_zero, Nat.mod_self]; simp
      · have : (align.toNat - addr0.toNat % align.toNat) % align.toNat = align.toNat - addr0.toNat % align.toNat :=
          Nat.mod_eq_of_lt (by omega)
        rw [this, show addr0.toNat % align.toNat + (align.toNat - addr0.toNat % align.toNat) = align.toNat by omega,
          Nat.mod_self]
    dsimp [off]
    split
    · rw [← Nat.add_assoc, Nat.add_mod, hbase, Nat.mod_self]; simp
    · exact hbase
  · have hokf : h.allocOk h.nalloc = false := Bool.eq_false_iff.mpr hok
    rw [zng_alloc_aligned_when_fail h size align hokf] at hrun
    injection hrun with hpair
    injection hpair with hret _
    exact absurd hret.symm hne

end ZlibNgF.Proof.Zutil
