import MozjpegF.Spec.Common.Types

/-!
# Shared proof lemmas for `jmemmgr.c` pool allocation and destruction (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.JmemmgrHelpers
open C MozjpegF.Spec Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.Jmemmgr Mozjpeg.Jmemnobs

/-- Folding `upd t b none` never modifies any key `k` outside `arr`. -/
theorem foldl_upd_none_ne {α : Type} (arr : Array Nat) (t0 : Tbl (Option α)) (k : Nat)
    (hn : k ∉ arr) : (arr.foldl (fun t b => upd t b none) t0) k = t0 k := by
  exact arr.foldl_induction (fun _ (t : Tbl (Option α)) => t k = t0 k) rfl fun i b hb => by
    have hne : k ≠ arr[i] := fun heq => hn (heq ▸ Array.getElem_mem i.isLt)
    rw [upd_ne _ _ _ _ hne]
    exact hb

/-- Folding `upd t b none` clears every key `k` that belongs to `arr` or was already `none`. -/
theorem foldl_upd_none_eq_none_of {α : Type} (arr : Array Nat) (t0 : Tbl (Option α)) (k : Nat)
    (hk : k ∈ arr ∨ t0 k = none) : (arr.foldl (fun t b => upd t b none) t0) k = none := by
  have hind := Array.foldl_induction (as := arr) (init := t0) (f := fun t b => upd t b none)
    (fun idx (t : Tbl (Option α)) =>
      (t0 k = none → t k = none) ∧
      (∀ (j : Fin arr.size), j.val < idx → arr[j] = k → t k = none))
    ⟨fun h => h, fun _ hj => by omega⟩
    (fun i b ⟨h0, hprev⟩ => by
      constructor
      · intro hn0
        by_cases hki : k = arr[i]
        · rw [hki]; exact upd_same _ _ _
        · rw [upd_ne _ _ _ _ hki]; exact h0 hn0
      · intro j hjlt hjk
        by_cases hki : k = arr[i]
        · rw [hki]; exact upd_same _ _ _
        · rw [upd_ne _ _ _ _ hki]
          have hjlt' : j.val < i.val := by
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hjlt) with hlt | heq
            · exact hlt
            · exfalso; apply hki; rw [← hjk]; simp [heq]
          exact hprev j hjlt' hjk)
  rcases hk with hmem | h0
  · obtain ⟨j, hj, hjk⟩ := Array.mem_iff_getElem.mp hmem
    exact hind.2 ⟨j, hj⟩ hj hjk
  · exact hind.1 h0

/-- Generic `free_pool` execution lemma on a valid `cinfo` with live `cinfo->mem`. -/
theorem free_pool_ok (h : C.Heap) (bdc bmem : Nat) (pid32 : Int32)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (mems : Array C.JpegMemMgr)
    (hgetdc : C.Space.get h (C.DecompRef.decomp bdc) = some dcs) (hszdc : 0 < dcs.size)
    (hdc : dc = dcs[0]!) (hmem : dc.mem = .ref (.mem bmem) 0)
    (hgetmem : C.Space.get h (C.MemRef.mem bmem) = some mems) (hszmem : 0 < mems.size)
    (hpid0 : 0 ≤ pid32.toInt) (hpid2 : pid32.toInt < JPOOL_NUMPOOLS.toInt) :
    let pid := pid32.toInt.toNat
    let pa := (mems[0]!).poolAllocs[pid]!
    let h_f := freePoolAllocs pa h
    let mem' := {
      mems[0]! with
      livePools := mems[0]!.livePools.set! pid false
      poolAllocs := mems[0]!.poolAllocs.set! pid {}
    }
    C.run (free_pool (.ref (.decomp bdc) 0) pid32) h =
      .ok ((), C.Space.put h_f (C.MemRef.mem bmem) (mems.set! 0 mem')) := by
  intro pid pa h_f mem'
  unfold free_pool
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hbad : (pid32 < 0 || pid32 ≥ JPOOL_NUMPOOLS) = false := by
    apply Bool.eq_false_iff.mpr
    intro hor
    rcases Bool.or_eq_true _ _ |>.mp hor with hlt | hge
    · have := Int32.lt_iff_toInt_lt.mp (of_decide_eq_true hlt)
      change pid32.toInt < 0 at this
      omega
    · have := Int32.le_iff_toInt_le.mp (of_decide_eq_true hge)
      omega
  simp only [hbad, Bool.false_eq_true, ↓reduceIte, hmem]
  have hgetmem' : C.Space.get h (C.MemRef.mem bmem) = some mems := hgetmem
  rw [Ptr.load_bind h (C.MemRef.mem bmem) 0 mems _ hgetmem' hszmem]
  have hm0 : mems[0] = mems[0]! := by rw [← getElem!_pos mems 0 hszmem]
  rw [hm0]
  have hfree_m : C.run (freePoolM pa) h = .ok ((), h_f) := rfl
  rw [C.run_bind, hfree_m]
  dsimp only
  have hgetmem_f : C.Space.get h_f (C.MemRef.mem bmem) = some mems := hgetmem
  have hro_mem_f : C.Space.ro h_f (C.MemRef.mem bmem) = false := rfl
  simp only [C.run, Ptr.store, hgetmem_f, hro_mem_f, hszmem, ↓reduceIte,
    C.Space.modify_eq h_f (C.MemRef.mem bmem) mems _ hgetmem_f]
  congr 2

/-- All slots at or above `base` are covered by `(mbmem, p0, p1)`. -/
def PoolsCoverSince (base : Nat) (h : C.Heap) (mbmem : Option Nat) (p0 p1 : PoolAllocs) : Prop :=
  ∀ k, base ≤ k →
    h.bytes k = none ∧
    h.i32s k = none ∧
    h.comps k = none ∧
    (h.srcs k ≠ none → k ∈ p0.srcs ∨ k ∈ p1.srcs) ∧
    (h.markers k ≠ none → k ∈ p0.markers ∨ k ∈ p1.markers) ∧
    (h.inputctls k ≠ none → k ∈ p0.inputctls ∨ k ∈ p1.inputctls) ∧
    (h.masters k ≠ none → k ∈ p0.masters ∨ k ∈ p1.masters) ∧
    (h.mems k ≠ none → some k = mbmem) ∧
    (h.quants k = none ∧ h.huffs k = none ∧ h.savedMarkers k = none)

theorem poolsCoverSince_of_fresh {h : C.Heap} (hf : FreshNextBlk h) :
    PoolsCoverSince h.nextBlk h none {} {} := by
  intro k hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hq, hh, hsm⟩ := hf k hk
  exact ⟨h1, h2, h8, fun hne => False.elim (hne h7), fun hne => False.elim (hne h5),
    fun hne => False.elim (hne h6), fun hne => False.elim (hne h4), fun hne => False.elim (hne h3),
    hq, hh, hsm⟩

theorem poolsCoverSince_decomps_err_irrel {base : Nat} {h : C.Heap} {mbmem : Option Nat}
    {p0 p1 : PoolAllocs} (hc : PoolsCoverSince base h mbmem p0 p1)
    (d' : Tbl (Option (Array JpegDecompressStruct))) (e' : Tbl (Option (Array JpegErrorMgr)))
    (na' : Nat) :
    PoolsCoverSince base { h with decomps := d', errMgrs := e', nalloc := na' } mbmem p0 p1 := hc

/-- Generic `allocSlopRetry` theorem: under ANY `h.allocOk`, either returns `.errExit JERR_OUT_OF_MEMORY`
preserving `cinfo`, `mem`, and `PoolAllocs`, or succeeds with a single call to `allocFn`. -/
theorem allocSlopRetry_ok {R : Type} [DecidableEq R] (cinfo : DecompPtr) (allocFn : M (Ptr R))
    (Pred : C.Heap → Prop) (PostErr : C.Heap → Prop) (PostOk : Ptr R → C.Heap → Prop)
    (hOom : ∀ h1, Pred h1 →
      ∃ h_err, C.run (out_of_memory cinfo 2) h1 = .ok (.errExit JERR_OUT_OF_MEMORY, h_err) ∧ PostErr h_err)
    (hStep : ∀ h1, Pred h1 →
      (∃ h_fail, C.run allocFn h1 = .ok (.null, h_fail) ∧ Pred h_fail) ∨
      (∃ p h_ok, p ≠ .null ∧ C.run allocFn h1 = .ok (p, h_ok) ∧ PostOk p h_ok)) :
    ∀ (k : Nat) (slop : UInt64) (h : C.Heap), Pred h →
      (∃ h_err, C.run (allocSlopRetry cinfo allocFn k slop) h = .ok (.errExit JERR_OUT_OF_MEMORY, h_err) ∧
        PostErr h_err) ∨
      (∃ p h_ok, p ≠ .null ∧ C.run (allocSlopRetry cinfo allocFn k slop) h = .ok (.ok p, h_ok) ∧
        PostOk p h_ok) := by
  intro k
  induction k with
  | zero =>
    intro slop h hp
    left
    obtain ⟨h_err, herr_run, hpost⟩ := hOom h hp
    refine ⟨h_err, ?_, hpost⟩
    unfold allocSlopRetry
    rw [C.run_bind, herr_run]
    rfl
  | succ k ih =>
    intro slop h hp
    unfold allocSlopRetry
    rcases hStep h hp with ⟨h_fail, hfail_run, hp'⟩ | ⟨p, h_ok, hpne, hok_run, hpost⟩
    · rw [C.run_bind, hfail_run]
      dsimp only
      have hnull : ((Ptr.null : Ptr R) != .null) = false := rfl
      simp only [hnull, Bool.false_eq_true, ↓reduceIte]
      by_cases hmin : slop / 2 < MIN_SLOP
      · simp only [hmin, ↓reduceIte]
        left
        obtain ⟨h_err, herr_run, hpost⟩ := hOom h_fail hp'
        refine ⟨h_err, ?_, hpost⟩
        rw [C.run_bind, herr_run]
        rfl
      · simp only [hmin, ↓reduceIte]
        exact ih (slop / 2) h_fail hp'
    · rw [C.run_bind, hok_run]
      dsimp only
      have hne : (p != .null) = true := by simp [bne, hpne]
      simp only [hne, ↓reduceIte]
      exact Or.inr ⟨p, h_ok, hpne, rfl, hpost⟩

/-- Under `∀ n, h.allocOk n = true` and `0 < k`, `allocSlopRetry` succeeds on the first attempt. -/
theorem allocSlopRetry_allOk {R : Type} [DecidableEq R] (cinfo : DecompPtr) (allocFn : M (Ptr R))
    (PostOk : Ptr R → C.Heap → Prop)
    (hOkStep : ∀ h1, (∀ n, h1.allocOk n = true) →
      ∃ p h_ok, p ≠ .null ∧ C.run allocFn h1 = .ok (p, h_ok) ∧ PostOk p h_ok)
    (k : Nat) (hk : 0 < k) (slop : UInt64) (h : C.Heap) (hall : ∀ n, h.allocOk n = true) :
    ∃ p h_ok, p ≠ .null ∧ C.run (allocSlopRetry cinfo allocFn k slop) h = .ok (.ok p, h_ok) ∧
      PostOk p h_ok := by
  cases k with
  | zero => omega
  | succ k' =>
    unfold allocSlopRetry
    obtain ⟨p, h_ok, hpne, hok_run, hpost⟩ := hOkStep h hall
    rw [C.run_bind, hok_run]
    dsimp only
    have hne : (p != .null) = true := by simp [bne, hpne]
    simp only [hne, ↓reduceIte]
    exact ⟨p, h_ok, hpne, rfl, hpost⟩

end MozjpegF.Proof.JmemmgrHelpers
