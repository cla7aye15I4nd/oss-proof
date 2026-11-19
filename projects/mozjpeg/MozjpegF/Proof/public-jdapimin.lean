import MozjpegF.Spec.Safety.Goals
import MozjpegF.Spec.Functional.Goals
import MozjpegF.Proof.«jmemmgr.c.helpers»

/-!
# Proofs of `jcomapi.c` and `jdapimin.c` safety specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdapimin
open C MozjpegF.Spec MozjpegF.Spec.Safety MozjpegF.Spec.Functional MozjpegF.Proof.JmemmgrHelpers
open Mozjpeg.Jcomapi Mozjpeg.Jdapimin Mozjpeg.Jmemmgr Mozjpeg.Jmemnobs Mozjpeg.Jdmarker Mozjpeg.Jdinput
open Mozjpeg.JpeglibH Mozjpeg.JerrorH Mozjpeg.MoreCfg

private theorem poolsCoverSince_put_mem_same {base bmem : Nat} {h : C.Heap} {p0 p1 : PoolAllocs}
    (hc : PoolsCoverSince base h (some bmem) p0 p1) (ms : Array C.JpegMemMgr) :
    PoolsCoverSince base (C.Space.put h (C.MemRef.mem bmem) ms) (some bmem) p0 p1 := by
  intro k hk
  obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hc k hk
  refine ⟨hb, hi, hco, hsrc, hmk, hic, hms, fun hne => ?_⟩
  by_cases hkb : k = bmem
  · exact congrArg some hkb
  · simp only [C.Space.put, upd_ne _ _ _ _ hkb] at hne
    exact hmm hne

private theorem poolsCoverSince_put_marker_mem {base bmem bmk : Nat} {h : C.Heap} {p0 p1 : PoolAllocs}
    (hc : PoolsCoverSince base h (some bmem) p0 p1)
    (hin : bmk ∈ p0.markers ∨ bmk ∈ p1.markers) (mrks : Array C.JpegMarkerReader) :
    PoolsCoverSince base (C.Space.put h (C.MarkerRef.marker bmk) mrks) (some bmem) p0 p1 := by
  intro k hk
  obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hc k hk
  refine ⟨hb, hi, hco, hsrc, fun hne => ?_, hic, hms, hmm⟩
  by_cases hkb : k = bmk
  · subst hkb; exact hin
  · simp only [C.Space.put, upd_ne _ _ _ _ hkb] at hne
    exact hmk hne

private theorem poolsCoverSince_put_inputctl_mem {base bmem bic : Nat} {h : C.Heap} {p0 p1 : PoolAllocs}
    (hc : PoolsCoverSince base h (some bmem) p0 p1)
    (hin : bic ∈ p0.inputctls ∨ bic ∈ p1.inputctls) (ics : Array C.JpegInputController) :
    PoolsCoverSince base (C.Space.put h (C.InputCtlRef.inputctl bic) ics) (some bmem) p0 p1 := by
  intro k hk
  obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hc k hk
  refine ⟨hb, hi, hco, hsrc, hmk, fun hne => ?_, hms, hmm⟩
  by_cases hkb : k = bic
  · subst hkb; exact hin
  · simp only [C.Space.put, upd_ne _ _ _ _ hkb] at hne
    exact hic hne

private theorem poolsCoverSince_put_master_mem {base bmem bmas : Nat} {h : C.Heap} {p0 p1 : PoolAllocs}
    (hc : PoolsCoverSince base h (some bmem) p0 p1)
    (hin : bmas ∈ p0.masters ∨ bmas ∈ p1.masters) (mas : Array C.JpegDecompMaster) :
    PoolsCoverSince base (C.Space.put h (C.MasterRef.master bmas) mas) (some bmem) p0 p1 := by
  intro k hk
  obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hc k hk
  refine ⟨hb, hi, hco, hsrc, hmk, hic, fun hne => ?_, hmm⟩
  by_cases hkb : k = bmas
  · subst hkb; exact hin
  · simp only [C.Space.put, upd_ne _ _ _ _ hkb] at hne
    exact hms hne

private theorem free_pool_ok (h : C.Heap) (bdc bmem : Nat) (pid32 : Int32)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (mems : Array C.JpegMemMgr)
    (hgetdc : C.Space.get h (C.DecompRef.decomp bdc) = some dcs) (hszdc : 0 < dcs.size)
    (hdc : dc = dcs[0]!) (hmem : dc.mem = .ref (.mem bmem) 0)
    (hgetmem : C.Space.get h (C.MemRef.mem bmem) = some mems) (hszmem : 0 < mems.size)
    (hpid0 : 0 ≤ pid32.toInt) (hpid2 : pid32.toInt < Mozjpeg.JpeglibH.JPOOL_NUMPOOLS.toInt) :
    let pid := pid32.toInt.toNat
    let pa := (mems[0]!).poolAllocs[pid]!
    let h_f := freePoolAllocs pa h
    let mem' := {
      mems[0]! with
      livePools := mems[0]!.livePools.set! pid false
      poolAllocs := mems[0]!.poolAllocs.set! pid {}
    }
    C.run (Mozjpeg.Jmemmgr.free_pool (.ref (.decomp bdc) 0) pid32) h =
      .ok ((), C.Space.put h_f (C.MemRef.mem bmem) (mems.set! 0 mem')) := by
  intro pid pa h_f mem'
  unfold Mozjpeg.Jmemmgr.free_pool
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hbad : (pid32 < 0 || pid32 ≥ Mozjpeg.JpeglibH.JPOOL_NUMPOOLS) = false := by
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

theorem jpeg_abort_safety : Goal.jpeg_abort_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, rm, mems, rmas, masters, _ric, _ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, _herr, hmem, hgetmem, hszmem, hmas, hgetmas, hszmas,
    _hin, _hgetin, _hszin, _hmrk, _hgetmrk, _hszmrk, _hpoolSz, hnotIn1⟩ := hvalid
  subst hc
  unfold jpeg_abort
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  cases rmas with | master bmas =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hmemne : (Ptr.ref (C.MemRef.mem bmem) 0 == Ptr.null) = false := rfl
  simp only [hmem, hmemne, Bool.false_eq_true, ↓reduceIte]
  have hfp := free_pool_ok h bdc bmem 1 dcs dc mems hgetdc hszdc hdc hmem hgetmem hszmem
    (by decide) (by decide)
  dsimp only at hfp
  rw [C.run_bind, hfp]
  dsimp only
  let pa1 := (mems[0]!).poolAllocs[(1 : Int32).toInt.toNat]!
  let h_freed := freePoolAllocs pa1 h
  let mem' := {
    mems[0]! with
    livePools := mems[0]!.livePools.set! (1 : Int32).toInt.toNat false
    poolAllocs := mems[0]!.poolAllocs.set! (1 : Int32).toInt.toNat {}
  }
  let h1 := C.Space.put h_freed (C.MemRef.mem bmem) (mems.set! 0 mem')
  have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs := hgetdc
  rw [Ptr.load_bind h1 _ 0 dcs _ hgetdc1 hszdc, hdc0]
  have hpidNat : (1 : Int32).toInt.toNat = 1 := rfl
  have hnmem : bmas ∉ pa1.masters := by
    have := hnotIn1 bmas rfl
    simpa [pa1, hpidNat] using this
  have hmasNotFold : ∀ (arr : Array Nat) (t0 : C.Tbl (Option (Array C.JpegDecompMaster))),
      bmas ∉ arr → (arr.foldl (fun t b => upd t b none) t0) bmas = t0 bmas := by
    intro arr t0 hn
    exact arr.foldl_induction (fun _ (t : C.Tbl (Option (Array C.JpegDecompMaster))) => t bmas = t0 bmas) rfl fun i b hb => by
      have hne : bmas ≠ arr[i] := fun heq => hn (heq ▸ Array.getElem_mem i.isLt)
      rw [upd_ne _ _ _ _ hne]
      exact hb
  have hgetmas1 : C.Space.get h1 (C.MasterRef.master bmas) = some masters := by
    change h_freed.masters bmas = some masters
    change (pa1.masters.foldl (fun t b => upd t b none) h.masters) bmas = some masters
    rw [hmasNotFold pa1.masters h.masters hnmem]
    exact hgetmas
  by_cases his : (dc.isDecompressor != 0) = true
  · simp only [his, ↓reduceIte, hmas]
    have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
    let dc_upd := { dc with globalState := Mozjpeg.JpeglibH.DSTATE_START, markerList := .null, master := Ptr.ref (C.MasterRef.master bmas) 0 }
    change ∃ h', C.run (Ptr.store (Ptr.ref (C.DecompRef.decomp bdc) 0) dc_upd >>= fun () => do
      let mst ← Ptr.load (Ptr.ref (C.MasterRef.master bmas) 0)
      Ptr.store (Ptr.ref (C.MasterRef.master bmas) 0) { mst with markerListEnd := .null }) h1 = .ok ((), h')
    rw [Ptr.store_bind h1 (C.DecompRef.decomp bdc) 0 dc_upd dcs _ hgetdc1 hro_dc1 hszdc]
    let h2 := C.Space.put h1 (C.DecompRef.decomp bdc) (dcs.set! 0 dc_upd)
    have hgetmas2 : C.Space.get h2 (C.MasterRef.master bmas) = some masters := hgetmas1
    rw [Ptr.load_bind h2 (C.MasterRef.master bmas) 0 masters _ hgetmas2 hszmas]
    have hro_mas2 : C.Space.ro h2 (C.MasterRef.master bmas) = false := rfl
    simp [C.run, Ptr.store, hgetmas2, hro_mas2, hszmas]
  · have hisF : (dc.isDecompressor != 0) = false := Bool.eq_false_iff.mpr his
    simp only [hisF, Bool.false_eq_true, ↓reduceIte]
    have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
    simp [C.run, Ptr.store, hgetdc1, hro_dc1, hszdc]

theorem jpeg_destroy_safety : Goal.jpeg_destroy_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, rm, mems, _rmas, _masters, _ric, _ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, _herr, hmem, hgetmem, hszmem, _⟩ := hvalid
  subst hc
  unfold jpeg_destroy Mozjpeg.Jmemmgr.self_destruct Mozjpeg.Jmemnobs.jpeg_free_small_mem Mozjpeg.Jmemnobs.jpeg_mem_term
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hmemne : (Ptr.ref (C.MemRef.mem bmem) 0 != Ptr.null) = true := rfl
  simp only [hmem, hmemne, ↓reduceIte, bind_assoc_m]
  have hfp1 := free_pool_ok h bdc bmem 1 dcs dc mems hgetdc hszdc hdc hmem hgetmem hszmem
    (by decide) (by decide)
  dsimp only at hfp1
  rw [C.run_bind, hfp1]
  dsimp only
  let pa1 := (mems[0]!).poolAllocs[(1 : Int32).toInt.toNat]!
  let h1_f := freePoolAllocs pa1 h
  let mem1 := { mems[0]! with livePools := mems[0]!.livePools.set! (1 : Int32).toInt.toNat false,
                              poolAllocs := mems[0]!.poolAllocs.set! (1 : Int32).toInt.toNat {} }
  let h1 := C.Space.put h1_f (C.MemRef.mem bmem) (mems.set! 0 mem1)
  have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs := hgetdc
  have hgetmem1 : C.Space.get h1 (C.MemRef.mem bmem) = some (mems.set! 0 mem1) := by
    simp [h1, C.Space.get, C.Space.put]
  have hszmem1 : 0 < (mems.set! 0 mem1).size := by rw [Array.size_set!]; exact hszmem
  have hfp0 := free_pool_ok h1 bdc bmem 0 dcs dc (mems.set! 0 mem1) hgetdc1 hszdc hdc hmem hgetmem1 hszmem1
    (by decide) (by decide)
  dsimp only at hfp0
  rw [C.run_bind, hfp0]
  dsimp only
  let mems1 := mems.set! 0 mem1
  let pa0 := (mems1[0]!).poolAllocs[(0 : Int32).toInt.toNat]!
  let h2_f := freePoolAllocs pa0 h1
  let mem2 := { mems1[0]! with livePools := mems1[0]!.livePools.set! (0 : Int32).toInt.toNat false,
                               poolAllocs := mems1[0]!.poolAllocs.set! (0 : Int32).toInt.toNat {} }
  let h2 := C.Space.put h2_f (C.MemRef.mem bmem) (mems1.set! 0 mem2)
  have hgetdc2 : C.Space.get h2 (C.DecompRef.decomp bdc) = some dcs := hgetdc1
  rw [Ptr.load_bind h2 _ 0 dcs _ hgetdc2 hszdc, hdc0, hmem]
  have hgetmem2 : h2.mems bmem = some (mems1.set! 0 mem2) := by
    simp [h2, C.Space.put, h2_f, freePoolAllocs]
  let h3 : C.Heap := { h2 with mems := upd h2.mems bmem none }
  have hfree_mem : C.run (freeMemMgr (Ptr.ref (C.MemRef.mem bmem) 0)) h2 = .ok ((), h3) := by
    simp [C.run, freeMemMgr, hgetmem2]; rfl
  rw [C.run_bind, hfree_mem]
  dsimp only
  have hgetdc3 : C.Space.get h3 (C.DecompRef.decomp bdc) = some dcs := hgetdc2
  rw [Ptr.load_bind h3 _ 0 dcs _ hgetdc3 hszdc, hdc0]
  have hro_dc3 : C.Space.ro h3 (C.DecompRef.decomp bdc) = false := rfl
  let dc3 := { dc with mem := .null }
  let h4 := C.Space.put h3 (C.DecompRef.decomp bdc) (dcs.set! 0 dc3)
  rw [Ptr.store_bind h3 _ 0 dc3 dcs _ hgetdc3 hro_dc3 hszdc]
  simp only [pure_bind_m]
  have hgetdc4 : C.Space.get h4 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc3) := by
    simp [h4, C.Space.get, C.Space.put]
  have hszdc4 : 0 < (dcs.set! 0 dc3).size := by rw [Array.size_set!]; exact hszdc
  rw [Ptr.load_bind h4 _ 0 (dcs.set! 0 dc3) _ hgetdc4 hszdc4]
  have hro_dc4 : C.Space.ro h4 (C.DecompRef.decomp bdc) = false := rfl
  simp [C.run, Ptr.store, hgetdc4, hro_dc4, hszdc]

theorem jpeg_abort_decompress_safety : Goal.jpeg_abort_decompress_safety :=
  jpeg_abort_safety

theorem jpeg_destroy_decompress_safety : Goal.jpeg_destroy_decompress_safety :=
  jpeg_destroy_safety

theorem jpeg_input_complete_safety : Goal.jpeg_input_complete_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, _rm, _mems, _rmas, _masters, ric, ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, herrValid, _hmem, _hgetmem, _hszmem, _hmas, _hgetmas, _hszmas,
    hin, hgetin, hszin, _⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_input_complete Mozjpeg.JerrorH.errexit1
  cases rc with | decomp bdc =>
  cases ric with | inputctl bic =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hbad : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_START ||
                   dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = true
  · simp only [hbad, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
    rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
    rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hbadF : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_START ||
                  dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = false :=
      Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, hin]
    rw [Ptr.load_bind h _ 0 ics _ hgetin hszin]
    exact ⟨_, _, rfl⟩

theorem jpeg_has_multiple_scans_safety : Goal.jpeg_has_multiple_scans_safety := by
  intro h cinfo hvalid
  obtain ⟨rc, dcs, dc, _rm, _mems, _rmas, _masters, ric, ics, _rmrk, _mrks,
    hc, hgetdc, hszdc, hdc, herrValid, _hmem, _hgetmem, _hszmem, _hmas, _hgetmas, _hszmas,
    hin, hgetin, hszin, _⟩ := hvalid
  subst hc
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  unfold jpeg_has_multiple_scans Mozjpeg.JerrorH.errexit1
  cases rc with | decomp bdc =>
  cases ric with | inputctl bic =>
  cases rerr with | err berr =>
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hbad : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_READY ||
                   dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = true
  · simp only [hbad, ↓reduceIte, herr, bind_assoc_m, pure_bind_m]
    rw [Ptr.load_bind h _ 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h (C.ErrRef.err berr) = false := rfl
    rw [Ptr.store_bind h _ 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hbadF : (dc.globalState < Mozjpeg.JpeglibH.DSTATE_READY ||
                  dc.globalState > Mozjpeg.JpeglibH.DSTATE_STOPPING) = false :=
      Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte, hin]
    rw [Ptr.load_bind h _ 0 ics _ hgetin hszin]
    exact ⟨_, _, rfl⟩

/-! ## `jpeg_CreateDecompress` safety, non-leakage on any failure, and invariant establishment -/

private theorem jinit_memory_mgr_outcome (h : C.Heap) (bdc : Nat) (base : Nat)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (rerr : C.ErrRef)
    (hgetdc : C.Space.get h (C.DecompRef.decomp bdc) = some dcs) (hszdc : 0 < dcs.size)
    (hdc : dc = dcs[0]!)
    (herrp : dc.err = .ref rerr 0) (herrLive : ∃ errs, C.Space.get h rerr = some errs ∧ 0 < errs.size)
    (hbase : base ≤ h.nextBlk)
    (hcover : PoolsCoverSince base h none {} {}) :
    ∃ res h1 dcs1 dc1,
      C.run (jinit_memory_mgr (.ref (.decomp bdc) 0)) h = .ok (res, h1) ∧
      C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs1 ∧ dcs1.size = dcs.size ∧ dc1 = dcs1[0]! ∧
      dc1.err = .ref rerr 0 ∧ (∃ errs1, C.Space.get h1 rerr = some errs1 ∧ 0 < errs1.size) ∧
      base ≤ h1.nextBlk ∧ h1.allocOk = h.allocOk ∧
      match res with
      | .errExit _ => dc1.mem = .null ∧ PoolsCoverSince base h1 none {} {} ∧ ¬ (∀ n, h.allocOk n = true)
      | .ok () =>
        ∃ bmem mems1,
          dc1.mem = .ref (.mem bmem) 0 ∧ base ≤ bmem ∧
          C.Space.get h1 (C.MemRef.mem bmem) = some mems1 ∧ 0 < mems1.size ∧
          mems1[0]!.poolAllocs = #[{}, {}] ∧
          mems1[0]!.livePools = #[true, true] ∧
          (h.allocOk h.nalloc = true → bmem = h.nextBlk) ∧
          PoolsCoverSince base h1 (some bmem) {} {} := by
  obtain ⟨errs, hgeterr, hszerr⟩ := herrLive
  unfold jinit_memory_mgr jpeg_mem_init jpeg_get_small_mem jpeg_mem_term errexit1
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hro_dc : C.Space.ro h (C.DecompRef.decomp bdc) = false := rfl
  let dc0 := { dc with mem := .null }
  let dcs0 := dcs.set! 0 dc0
  let h0 := C.Space.put h (C.DecompRef.decomp bdc) dcs0
  rw [Ptr.store_bind h (C.DecompRef.decomp bdc) 0 dc0 dcs _ hgetdc hro_dc hszdc]
  have h1c : ((ALIGN_SIZE &&& (ALIGN_SIZE - 1)) != 0) = false := by decide
  have h2c : (MAX_ALLOC_CHUNK % (Int64.ofNat ALIGN_SIZE.toNat) != 0) = false := by decide
  simp only [h1c, h2c, Bool.false_eq_true, ↓reduceIte, bind_assoc_m, pure_bind_m]
  have hsz0 : dcs0.size = dcs.size := by simp [dcs0]
  have hsz0_pos : 0 < dcs0.size := by rw [hsz0]; exact hszdc
  have hgetdc0 : C.Space.get h0 (C.DecompRef.decomp bdc) = some dcs0 := by simp [h0, C.Space.get, C.Space.put]
  have hgeterr0 : C.Space.get h0 rerr = some errs := by cases rerr; exact hgeterr
  by_cases ha : h.allocOk h.nalloc = true
  · let bmem := h.nextBlk
    let haHeap : C.Heap := {
      h0 with
      mems := upd h0.mems bmem (some #[default])
      nextBlk := bmem + 1
      nalloc := h.nalloc + 1
    }
    have ha0 : h0.allocOk h0.nalloc = true := ha
    have halloc : C.run allocMemMgr h0 = .ok (.ref (.mem bmem) 0, haHeap) := by
      change (if h0.allocOk h0.nalloc = true then Except.ok (Ptr.ref (C.MemRef.mem h0.nextBlk) 0, {
        h0 with
        mems := upd h0.mems h0.nextBlk (some #[default])
        nextBlk := h0.nextBlk + 1
        nalloc := h0.nalloc + 1
      }) else _) = .ok (.ref (.mem bmem) 0, haHeap)
      simp [ha0]
      exact ⟨rfl, rfl⟩
    have hnotNull : (Ptr.ref (C.MemRef.mem bmem) 0 == .null) = false := rfl
    rw [C.run_bind, halloc]
    simp only [hnotNull, Bool.false_eq_true, ↓reduceIte]
    have hgetmemA : C.Space.get haHeap (C.MemRef.mem bmem) = some #[default] := by
      simp [haHeap, C.Space.get, upd_same]
    have hszmemA : 0 < (#[default] : Array C.JpegMemMgr).size := by decide
    have hro_memA : C.Space.ro haHeap (C.MemRef.mem bmem) = false := rfl
    let memInit : C.JpegMemMgr := {
      allocSmall := .fn "alloc_small"
      freePool := .fn "free_pool"
      selfDestruct := .fn "self_destruct"
      maxAllocChunk := MAX_ALLOC_CHUNK
      maxMemoryToUse := 0
      totalSpaceAllocated := 192
      livePools := #[true, true]
      poolAllocs := #[{}, {}]
    }
    let h1a := C.Space.put haHeap (C.MemRef.mem bmem) (#[default].set! 0 memInit)
    rw [Ptr.store_bind haHeap (C.MemRef.mem bmem) 0 memInit #[default] _ hgetmemA hro_memA hszmemA]
    have hgetdc1a : C.Space.get h1a (C.DecompRef.decomp bdc) = some dcs0 := hgetdc0
    rw [Ptr.load_bind h1a _ 0 dcs0 _ hgetdc1a hsz0_pos]
    have hdc0_0 : dcs0[0] = dc0 := by simp [dcs0, Array.set!_eq_setIfInBounds]
    rw [hdc0_0]
    have hro_dc1a : C.Space.ro h1a (C.DecompRef.decomp bdc) = false := rfl
    let dc1 := { dc0 with mem := .ref (.mem bmem) 0 }
    let dcs1 := dcs0.set! 0 dc1
    let hfin := C.Space.put h1a (C.DecompRef.decomp bdc) dcs1
    rw [Ptr.store_bind h1a (C.DecompRef.decomp bdc) 0 dc1 dcs0 _ hgetdc1a hro_dc1a hsz0_pos]
    have hgetdcFin : C.Space.get hfin (C.DecompRef.decomp bdc) = some dcs1 := by simp [hfin, C.Space.get, C.Space.put]
    have hdc1_bang : dc1 = dcs1[0]! := by
      have hsz1 : 0 < dcs1.size := by simp [dcs1, hsz0_pos]
      rw [getElem!_pos _ 0 hsz1]; simp [dcs1, Array.set!_eq_setIfInBounds]
    have hgeterrFin : C.Space.get hfin rerr = some errs := by cases rerr; exact hgeterr0
    have hgetmemFin : C.Space.get hfin (C.MemRef.mem bmem) = some (#[default].set! 0 memInit) := by
      simp [hfin, C.Space.get, C.Space.put, h1a]
    refine ⟨.ok (), hfin, dcs1, dc1, rfl, hgetdcFin, by simp [dcs1, hsz0], hdc1_bang,
      herrp, ⟨errs, hgeterrFin, hszerr⟩, (by simp [hfin, h1a, haHeap, C.Space.put]; omega), rfl, ?_⟩
    refine ⟨bmem, #[default].set! 0 memInit, rfl, hbase, hgetmemFin, (by decide),
      rfl, rfl, (fun _ => rfl), ?_⟩
    intro k hk
    obtain ⟨hb, hi, hco, hs, hmk, hic, hms, hmm⟩ := hcover k hk
    refine ⟨hb, hi, hco, hs, hmk, hic, hms, fun hne => ?_⟩
    by_cases hkb : k = bmem
    · exact congrArg some hkb
    · exfalso; apply hne
      have hmnone : h.mems k = none := by
        cases hm : h.mems k with
        | none => rfl
        | some v =>
          have h1 : h.mems k ≠ none := by simp [hm]
          cases hmm h1
      change (upd (upd h.mems bmem (some #[default])) bmem (some (#[default].set! 0 memInit))) k = none
      rw [upd_ne _ _ _ _ hkb, upd_ne _ _ _ _ hkb, hmnone]
  · have haF : h0.allocOk h0.nalloc = false := Bool.eq_false_iff.mpr ha
    let haHeap : C.Heap := { h0 with nalloc := h0.nalloc + 1 }
    have hallocF : C.run allocMemMgr h0 = .ok (.null, haHeap) := by
      simp [C.run, allocMemMgr, haF, haHeap]
    rw [C.run_bind, hallocF]
    simp only [beq_self_eq_true, ↓reduceIte, herrp]
    have hgeterrA : C.Space.get haHeap rerr = some errs := hgeterr0
    rw [Ptr.load_bind haHeap rerr 0 errs _ hgeterrA hszerr]
    have hro_errA : C.Space.ro haHeap rerr = false := by cases rerr; rfl
    let err1 := { errs[0] with msgCode := JERR_OUT_OF_MEMORY, msgParmI := errs[0].msgParmI.set! 0 0 }
    let errs1 := errs.set! 0 err1
    let hfin := C.Space.put haHeap rerr errs1
    rw [Ptr.store_bind haHeap rerr 0 err1 errs _ hgeterrA hro_errA hszerr]
    have hgetdcFin : C.Space.get hfin (C.DecompRef.decomp bdc) = some dcs0 := by
      cases rerr; exact hgetdc0
    have hdc0_bang : dc0 = dcs0[0]! := by
      rw [getElem!_pos _ 0 hsz0_pos]; simp [dcs0, Array.set!_eq_setIfInBounds]
    have hgeterrFin : C.Space.get hfin rerr = some errs1 := by
      cases rerr; simp [hfin, C.Space.get, C.Space.put]
    have hszerr1 : 0 < errs1.size := by simp [errs1, hszerr]
    refine ⟨.errExit JERR_OUT_OF_MEMORY, hfin, dcs0, dc0, rfl, hgetdcFin, hsz0, hdc0_bang,
      herrp, ⟨errs1, hgeterrFin, hszerr1⟩, hbase, rfl, rfl, ?_, fun hall => ha (hall h.nalloc)⟩
    cases rerr
    exact hcover

private def CreateSubBase (base bdc bmem : Nat) (rerr : C.ErrRef)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct)
    (mems : Array C.JpegMemMgr) (h : C.Heap) : Prop :=
  C.Space.get h (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
  dc.err = .ref rerr 0 ∧ (∃ errs, C.Space.get h rerr = some errs ∧ 0 < errs.size) ∧
  dc.mem = .ref (.mem bmem) 0 ∧ C.Space.get h (C.MemRef.mem bmem) = some mems ∧ 0 < mems.size ∧
  mems[0]!.poolAllocs.size = 2 ∧ mems[0]!.poolAllocs[1]! = {} ∧
  base ≤ h.nextBlk ∧ PoolsCoverSince base h (some bmem) mems[0]!.poolAllocs[0]! {}

private theorem createSubBase_errup {base bdc bmem : Nat} {rerr : C.ErrRef}
    {dcs : Array C.JpegDecompressStruct} {dc : C.JpegDecompressStruct}
    {mems : Array C.JpegMemMgr} {h : C.Heap} (hs : CreateSubBase base bdc bmem rerr dcs dc mems h)
    {errs' : Array C.JpegErrorMgr} (hsz' : 0 < errs'.size) (na' : Nat) :
    let h' := { C.Space.put h rerr errs' with nalloc := na' }
    CreateSubBase base bdc bmem rerr dcs dc mems h' := by
  obtain ⟨hgetdc, hszdc, hdc, herrp, _, hmem, hgetmem, hszmem, hpsz, hp1, hbase, hcov⟩ := hs
  cases rerr with | err berr =>
  refine ⟨hgetdc, hszdc, hdc, herrp, ⟨errs', by simp [C.Space.get, C.Space.put], hsz'⟩,
    hmem, hgetmem, hszmem, hpsz, hp1, hbase, hcov⟩

private theorem alloc_small_pool0_outcome {R : Type} [DecidableEq R]
    (h : C.Heap) (base bdc bmem : Nat) (rerr : C.ErrRef) (sz : UInt64)
    (allocFn : M (C.Ptr R)) (recordFn : C.PoolAllocs → C.Ptr R → C.PoolAllocs)
    (InvExtra : C.Heap → Prop) (PostAlloc : C.Ptr R → C.Heap → Prop)
    (hszOk1 : (sz > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false)
    (hszOk2 : (sizeof_small_pool_hdr + round_up_pow2 sz ALIGN_SIZE + ALIGN_SIZE - 1 >
      MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (mems : Array C.JpegMemMgr)
    (hs : CreateSubBase base bdc bmem rerr dcs dc mems h)
    (hex : InvExtra h)
    (hstep : ∀ h1 dcs1 dc1 mems1, CreateSubBase base bdc bmem rerr dcs1 dc1 mems1 h1 → InvExtra h1 →
      (¬ (∀ n, h1.allocOk n = true) ∧
        ∃ h_fail, C.run allocFn h1 = .ok (.null, h_fail) ∧
          CreateSubBase base bdc bmem rerr dcs1 dc1 mems1 h_fail ∧ InvExtra h_fail ∧ h_fail.allocOk = h1.allocOk) ∨
      (∃ p h_ok mems_new, p ≠ .null ∧ C.run allocFn h1 = .ok (p, h_ok) ∧
        PostAlloc p h_ok ∧ InvExtra h_ok ∧ h_ok.allocOk = h1.allocOk ∧
        C.Space.get h_ok (C.DecompRef.decomp bdc) = some dcs1 ∧ 0 < dcs1.size ∧ dc1 = dcs1[0]! ∧
        dc1.err = .ref rerr 0 ∧ (∃ errs1, C.Space.get h_ok rerr = some errs1 ∧ 0 < errs1.size) ∧
        dc1.mem = .ref (.mem bmem) 0 ∧ C.Space.get h_ok (C.MemRef.mem bmem) = some mems1 ∧ 0 < mems1.size ∧
        mems1[0]!.poolAllocs.size = 2 ∧ mems1[0]!.poolAllocs[1]! = {} ∧
        base ≤ h_ok.nextBlk ∧
        mems_new = {
          mems1[0]! with
          poolAllocs := mems1[0]!.poolAllocs.set! 0 (recordFn mems1[0]!.poolAllocs[0]! p)
          totalSpaceAllocated := mems1[0]!.totalSpaceAllocated + round_up_pow2 sz ALIGN_SIZE
        } ∧
        PoolsCoverSince base h_ok (some bmem) (recordFn mems1[0]!.poolAllocs[0]! p) {}))
    (hfailPres : ∀ h1, InvExtra h1 → ∀ errs1 na1,
      InvExtra { C.Space.put h1 rerr errs1 with nalloc := na1 })
    (hmemPres : ∀ (_p : C.Ptr R) (h1 : C.Heap) (m' : Array C.JpegMemMgr),
      InvExtra h1 → InvExtra (C.Space.put h1 (C.MemRef.mem bmem) m'))
    (hpostMemPres : ∀ (p : C.Ptr R) (h1 : C.Heap) (m' : Array C.JpegMemMgr),
      PostAlloc p h1 → PostAlloc p (C.Space.put h1 (C.MemRef.mem bmem) m')) :
    ∃ res h_out mems',
      C.run (allocSmallCore (.ref (.decomp bdc) 0) JPOOL_PERMANENT sz allocFn recordFn) h = .ok (res, h_out) ∧
      CreateSubBase base bdc bmem rerr dcs dc mems' h_out ∧ InvExtra h_out ∧ h_out.allocOk = h.allocOk ∧
      match res with
      | .errExit code => code = JERR_OUT_OF_MEMORY ∧ ¬ (∀ n, h.allocOk n = true)
      | .ok p => p ≠ .null ∧ PostAlloc p h_out := by
  obtain ⟨hgetdc, hszdc, hdc, herrp, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz, hp1, hbase, hcov⟩ := hs
  unfold allocSmallCore
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have h3 : (JPOOL_PERMANENT < 0 || JPOOL_PERMANENT ≥ JPOOL_NUMPOOLS) = false := by decide
  simp only [hszOk1, hszOk2, h3, Bool.false_eq_true, ↓reduceIte, hmem]
  have hgetmem' : C.Space.get h (C.MemRef.mem bmem) = some mems := hgetmem
  rw [Ptr.load_bind h (C.MemRef.mem bmem) 0 mems _ hgetmem' hszmem]
  have hpid0 : JPOOL_PERMANENT.toInt.toNat = 0 := rfl
  let slop0 :=
    if first_pool_slop[JPOOL_PERMANENT.toInt.toNat]! >
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64 -
          (sizeof_small_pool_hdr + round_up_pow2 sz ALIGN_SIZE + ALIGN_SIZE - 1) then
      MAX_ALLOC_CHUNK.toInt.toNat.toUInt64 -
        (sizeof_small_pool_hdr + round_up_pow2 sz ALIGN_SIZE + ALIGN_SIZE - 1)
    else first_pool_slop[JPOOL_PERMANENT.toInt.toNat]!
  have finishOk : ∀ p h_ok mems_new,
      p ≠ .null → PostAlloc p h_ok → InvExtra h_ok → h_ok.allocOk = h.allocOk →
      C.Space.get h_ok (C.DecompRef.decomp bdc) = some dcs → 0 < dcs.size → dc = dcs[0]! →
      dc.err = .ref rerr 0 → (∃ errs1, C.Space.get h_ok rerr = some errs1 ∧ 0 < errs1.size) →
      dc.mem = .ref (.mem bmem) 0 → C.Space.get h_ok (C.MemRef.mem bmem) = some mems → 0 < mems.size →
      mems[0]!.poolAllocs.size = 2 → mems[0]!.poolAllocs[1]! = {} → base ≤ h_ok.nextBlk →
      mems_new = {
        mems[0]! with
        poolAllocs := mems[0]!.poolAllocs.set! 0 (recordFn mems[0]!.poolAllocs[0]! p)
        totalSpaceAllocated := mems[0]!.totalSpaceAllocated + round_up_pow2 sz ALIGN_SIZE
      } →
      PoolsCoverSince base h_ok (some bmem) (recordFn mems[0]!.poolAllocs[0]! p) {} →
      C.run (allocSlopRetry (.ref (.decomp bdc) 0) allocFn 16 slop0) h = .ok (.ok p, h_ok) →
      ∃ res h_out mems',
        C.run (do
          let __do_lift ← allocSlopRetry (.ref (.decomp bdc) 0) allocFn 16 slop0
          match __do_lift with
          | JpegRes.errExit code => pure (JpegRes.errExit code)
          | JpegRes.ok p => do
            let dc2 ← Ptr.load (Ptr.ref (C.DecompRef.decomp bdc) 0)
            let mem2 ← Ptr.load dc2.mem
            let allocs2 := recordFn mem2.poolAllocs[JPOOL_PERMANENT.toInt.toNat]! p
            Ptr.store dc2.mem {
              mem2 with
              poolAllocs := mem2.poolAllocs.set! JPOOL_PERMANENT.toInt.toNat allocs2
              totalSpaceAllocated := mem2.totalSpaceAllocated + round_up_pow2 sz ALIGN_SIZE
            }
            pure (JpegRes.ok p)) h = .ok (res, h_out) ∧
        CreateSubBase base bdc bmem rerr dcs dc mems' h_out ∧ InvExtra h_out ∧ h_out.allocOk = h.allocOk ∧
        match res with
        | .errExit code => code = JERR_OUT_OF_MEMORY ∧ ¬ (∀ n, h.allocOk n = true)
        | .ok p => p ≠ .null ∧ PostAlloc p h_out := by
    intro p h_ok mems_new hpne hpa hex_ok hok_ok hgetdc2 hszdc2 hdc2 herrp2 herrLive2
      hmem2 hgetmem2 hszmem2 hpsz2 hp1_2 hbase2 hmemNewEq hcov2 hok_run
    have hdc2_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc2]; exact hdc2.symm
    have hro_mem2 : C.Space.ro h_ok (C.MemRef.mem bmem) = false := rfl
    let mems' := mems.set! 0 mems_new
    let h_fin := C.Space.put h_ok (C.MemRef.mem bmem) mems'
    have hszm' : 0 < mems'.size := by simp [mems', hszmem2]
    have hm'0 : mems'[0]! = mems_new := by
      simp [mems', Array.set!_eq_setIfInBounds, hszmem2]
    have hpsz' : mems'[0]!.poolAllocs.size = 2 := by rw [hm'0, hmemNewEq]; simpa [Array.size_set!] using hpsz2
    have hp0' : mems'[0]!.poolAllocs[0]! = recordFn mems[0]!.poolAllocs[0]! p := by
      rw [hm'0, hmemNewEq]; simp [Array.set!_eq_setIfInBounds, hpsz2]
    have hp1_2' : mems[0]!.poolAllocs[1] = {} := by rw [← getElem!_pos _ 1 (by omega)]; exact hp1_2
    have hp1' : mems'[0]!.poolAllocs[1]! = {} := by
      rw [hm'0, hmemNewEq]; simp [Array.set!_eq_setIfInBounds, hpsz2, hp1_2']
    have hgetdcF : C.Space.get h_fin (C.DecompRef.decomp bdc) = some dcs := hgetdc2
    obtain ⟨errs2, hgeterr2, hszerr2⟩ := herrLive2
    have hgeterrF : C.Space.get h_fin rerr = some errs2 := by cases rerr; exact hgeterr2
    have hgetmemF : C.Space.get h_fin (C.MemRef.mem bmem) = some mems' := by simp [h_fin, C.Space.get, C.Space.put]
    have hcovF : PoolsCoverSince base h_fin (some bmem) mems'[0]!.poolAllocs[0]! {} := by
      rw [hp0']; exact poolsCoverSince_put_mem_same hcov2 mems'
    refine ⟨.ok p, h_fin, mems', ?_,
      ⟨hgetdcF, hszdc2, hdc2, herrp2, ⟨errs2, hgeterrF, hszerr2⟩, hmem2, hgetmemF, hszm', hpsz', hp1', hbase2, hcovF⟩,
      hmemPres p h_ok mems' hex_ok, hok_ok, hpne, hpostMemPres p h_ok mems' hpa⟩
    rw [C.run_bind, hok_run]
    dsimp only
    rw [Ptr.load_bind h_ok _ 0 dcs _ hgetdc2 hszdc2, hdc2_0, hmem2]
    rw [Ptr.load_bind h_ok (C.MemRef.mem bmem) 0 mems _ hgetmem2 hszmem2]
    have hm0 : mems[0] = mems[0]! := by rw [← getElem!_pos mems 0 hszmem2]
    rw [hm0, hpid0]
    rw [Ptr.store_bind h_ok (C.MemRef.mem bmem) 0 _ mems _ hgetmem2 hro_mem2 hszmem2]
    simp only [hmemNewEq.symm]
    rfl
  by_cases hall : ∀ n, h.allocOk n = true
  · rcases hstep h dcs dc mems ⟨hgetdc, hszdc, hdc, herrp, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz, hp1, hbase, hcov⟩ hex with
      ⟨hnall, _⟩ |
      ⟨p, h_ok, mems_new, hpne, hok_run, hpa, hex_ok, hok_ok,
        hgetdc2, hszdc2, hdc2, herrp2, herrLive2, hmem2, hgetmem2, hszmem2,
        hpsz2, hp1_2, hbase2, hmemNewEq, hcov2⟩
    · exact False.elim (hnall hall)
    · have hretry1 : C.run (allocSlopRetry (.ref (.decomp bdc) 0) allocFn 16 slop0) h = .ok (.ok p, h_ok) := by
        unfold allocSlopRetry
        rw [C.run_bind, hok_run]
        dsimp only
        have hne : (p != .null) = true := by simp [bne, hpne]
        simp only [hne, ↓reduceIte]
        rfl
      exact finishOk p h_ok mems_new hpne hpa hex_ok hok_ok
        hgetdc2 hszdc2 hdc2 herrp2 herrLive2 hmem2 hgetmem2 hszmem2
        hpsz2 hp1_2 hbase2 hmemNewEq hcov2 hretry1
  · have hretry := allocSlopRetry_ok (R := R) (.ref (.decomp bdc) 0) allocFn
      (fun hx => CreateSubBase base bdc bmem rerr dcs dc mems hx ∧ InvExtra hx ∧ hx.allocOk = h.allocOk)
      (fun hx => CreateSubBase base bdc bmem rerr dcs dc mems hx ∧ InvExtra hx ∧ hx.allocOk = h.allocOk)
      (fun p hx => ∃ mems_new, p ≠ .null ∧ PostAlloc p hx ∧ InvExtra hx ∧ hx.allocOk = h.allocOk ∧
        C.Space.get hx (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
        dc.err = .ref rerr 0 ∧ (∃ errs1, C.Space.get hx rerr = some errs1 ∧ 0 < errs1.size) ∧
        dc.mem = .ref (.mem bmem) 0 ∧ C.Space.get hx (C.MemRef.mem bmem) = some mems ∧ 0 < mems.size ∧
        mems[0]!.poolAllocs.size = 2 ∧ mems[0]!.poolAllocs[1]! = {} ∧
        base ≤ hx.nextBlk ∧
        mems_new = {
          mems[0]! with
          poolAllocs := mems[0]!.poolAllocs.set! 0 (recordFn mems[0]!.poolAllocs[0]! p)
          totalSpaceAllocated := mems[0]!.totalSpaceAllocated + round_up_pow2 sz ALIGN_SIZE
        } ∧
        PoolsCoverSince base hx (some bmem) (recordFn mems[0]!.poolAllocs[0]! p) {})
      (fun h1 ⟨hs1, hex1, hok1⟩ => by
        obtain ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, _⟩ := id hs1
        unfold out_of_memory errexit1
        have hdc1_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc1]; exact hdc1.symm
        rw [Ptr.load_bind h1 _ 0 dcs _ hgetdc1 hszdc1, hdc1_0, herrp1]
        rw [Ptr.load_bind h1 rerr 0 errs1 _ hgeterr1 hszerr1]
        have hro_err : C.Space.ro h1 rerr = false := by cases rerr; rfl
        let err' := { errs1[0] with msgCode := JERR_OUT_OF_MEMORY, msgParmI := errs1[0].msgParmI.set! 0 2 }
        rw [Ptr.store_bind h1 rerr 0 err' errs1 _ hgeterr1 hro_err hszerr1]
        have hsz1 : 0 < (errs1.set! 0 err').size := by simp [hszerr1]
        have hs' := createSubBase_errup hs1 hsz1 h1.nalloc
        have hex' := hfailPres h1 hex1 (errs1.set! 0 err') h1.nalloc
        exact ⟨_, rfl, hs', hex', by cases rerr; exact hok1⟩)
      (fun h1 ⟨hs1, hex1, hok1⟩ => by
        rcases hstep h1 dcs dc mems hs1 hex1 with
          ⟨_, h_fail, hfail_run, hs', hex', hok'⟩ |
          ⟨p, h_ok, mems_new, hpne, hok_run, hpa, hex', hok', h2⟩
        · left; exact ⟨h_fail, hfail_run, hs', hex', hok'.trans hok1⟩
        · right; exact ⟨p, h_ok, hpne, hok_run, mems_new, hpne, hpa, hex', hok'.trans hok1, h2⟩)
      16 slop0 h ⟨⟨hgetdc, hszdc, hdc, herrp, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz, hp1, hbase, hcov⟩, hex, rfl⟩
    rcases hretry with ⟨h_err, herr_run, hs_err, hex_err, hok_err⟩ |
      ⟨p, h_ok, hpne, hok_run, mems_new, _, hpa, hex_ok, hok_ok,
        hgetdc2, hszdc2, hdc2, herrp2, herrLive2, hmem2, hgetmem2, hszmem2,
        hpsz2, hp1_2, hbase2, hmemNewEq, hcov2⟩
    · refine ⟨.errExit JERR_OUT_OF_MEMORY, h_err, mems, ?_, hs_err, hex_err, hok_err, rfl, hall⟩
      rw [C.run_bind, herr_run]; rfl
    · exact finishOk p h_ok mems_new hpne hpa hex_ok hok_ok
        hgetdc2 hszdc2 hdc2 herrp2 herrLive2 hmem2 hgetmem2 hszmem2
        hpsz2 hp1_2 hbase2 hmemNewEq hcov2 hok_run

private theorem jinit_marker_reader_outcome (h : C.Heap) (base bdc bmem : Nat) (rerr : C.ErrRef)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (mems : Array C.JpegMemMgr)
    (hs : CreateSubBase base bdc bmem rerr dcs dc mems h) :
    ∃ res h1 dcs1 dc1 mems1,
      C.run (jinit_marker_reader (.ref (.decomp bdc) 0)) h = .ok (res, h1) ∧
      CreateSubBase base bdc bmem rerr dcs1 dc1 mems1 h1 ∧ h1.allocOk = h.allocOk ∧
      (match res with
      | .errExit _ => ¬ (∀ n, h.allocOk n = true)
      | .ok () =>
        dc1.src = dc.src ∧
        ∃ bmrk mrks1, dc1.marker = .ref (.marker bmrk) 0 ∧
          C.Space.get h1 (C.MarkerRef.marker bmrk) = some mrks1 ∧ 0 < mrks1.size) := by
  unfold jinit_marker_reader alloc_small_marker
  obtain ⟨res, h_out, mems', hrun, hs_out, _, hok_out, hres⟩ :=
    alloc_small_pool0_outcome (R := C.MarkerRef) h base bdc bmem rerr sizeof_my_marker_reader
      allocMarker (fun pa p => match p with | .ref (.marker b) _ => { pa with markers := pa.markers.push b } | .null => pa)
      (fun _ => True)
      (fun p hx => ∃ bmk mrks, p = .ref (.marker bmk) 0 ∧ base ≤ bmk ∧ C.Space.get hx (C.MarkerRef.marker bmk) = some mrks ∧ 0 < mrks.size)
      (by decide) (by decide) dcs dc mems hs trivial
      (fun h1 dcs1 dc1 mems1 hs1 _ => by
        obtain ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩ := hs1
        by_cases ha : h1.allocOk h1.nalloc = true
        · right
          let bmk := h1.nextBlk
          let h_ok : C.Heap := { h1 with markers := upd h1.markers bmk (some #[default]), nextBlk := bmk + 1, nalloc := h1.nalloc + 1 }
          refine ⟨.ref (.marker bmk) 0, h_ok, _, by simp, by simp [C.run, allocMarker, ha, bmk, h_ok],
            ⟨bmk, #[default], rfl, hbase1, by simp [h_ok, C.Space.get, upd_same], by decide⟩,
            trivial, rfl, hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1,
            (by simp [h_ok]; omega), rfl, ?_⟩
          intro k hk
          obtain ⟨hb, hi, hco, hs, hmk, hic, hms, hmm⟩ := hcov1 k hk
          refine ⟨hb, hi, hco, hs, fun hne => ?_, hic, hms, hmm⟩
          by_cases hkb : k = bmk
          · left; rw [hkb]; simp [Array.mem_push]
          · rw [show h_ok.markers k = h1.markers k from upd_ne _ _ _ _ hkb] at hne
            rcases hmk hne with hm0 | hm1
            · left; exact Array.mem_push.mpr (Or.inl hm0)
            · right; exact hm1
        · left
          have hna : ¬ (∀ n, h1.allocOk n = true) := fun hall => ha (hall h1.nalloc)
          have haF : h1.allocOk h1.nalloc = false := Bool.eq_false_iff.mpr ha
          let h_fail : C.Heap := { h1 with nalloc := h1.nalloc + 1 }
          refine ⟨hna, h_fail, by simp [C.run, allocMarker, haF, h_fail],
            ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩,
            trivial, rfl⟩)
      (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial)
      (fun p h1 _ hp => hp)
  cases res with
  | errExit code =>
    obtain ⟨_, hnall⟩ := hres
    refine ⟨.errExit code, h_out, dcs, dc, mems', ?_, hs_out, hok_out, hnall⟩
    rw [C.run_bind]; erw [hrun]; rfl
  | ok p =>
    obtain ⟨_, bmrk, mrks, hpEq, hbasemk, hgetmk, hszmk⟩ := hres
    subst hpEq
    obtain ⟨hgetdc2, hszdc2, hdc2, herrp2, ⟨errs2, hgeterr2, hszerr2⟩, hmem2, hgetmem2, hszmem2, hpsz2, hp1_2, hbase2, hcov2⟩ := hs_out
    have hdc2_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc2]; exact hdc2.symm
    have hro_dc2 : C.Space.ro h_out (C.DecompRef.decomp bdc) = false := rfl
    let dc2 := { dc with marker := .ref (.marker bmrk) 0 }
    let dcs2 := dcs.set! 0 dc2
    let h2 := C.Space.put h_out (C.DecompRef.decomp bdc) dcs2
    have hgetdc2' : C.Space.get h2 (C.DecompRef.decomp bdc) = some dcs2 := by simp [h2, C.Space.get, C.Space.put]
    have hszdc2' : 0 < dcs2.size := by simp [dcs2, hszdc2]
    have hgetmk2 : C.Space.get h2 (C.MarkerRef.marker bmrk) = some mrks := hgetmk
    have hro_mk2 : C.Space.ro h2 (C.MarkerRef.marker bmrk) = false := rfl
    let mrk1 : C.JpegMarkerReader := {
      resetMarkerReader := .fn "reset_marker_reader"
      readMarkers := .fn "read_markers"
      readRestartMarker := .fn "read_restart_marker"
      processCOM := .fn "skip_variable"
      lengthLimitCOM := 0
      processAPPn := ((Array.replicate 16 (.fn "skip_variable")).set! 0 (.fn "get_interesting_appn")).set! 14 (.fn "get_interesting_appn")
      lengthLimitAPPn := Array.replicate 16 0
    }
    let mrks3 := mrks.set! 0 mrk1
    let h3 := C.Space.put h2 (C.MarkerRef.marker bmrk) mrks3
    -- `reset_marker_reader` updates `cinfo` and `marker`:
    have hgetdc3 : C.Space.get h3 (C.DecompRef.decomp bdc) = some dcs2 := hgetdc2'
    have hro_dc3 : C.Space.ro h3 (C.DecompRef.decomp bdc) = false := rfl
    let dc4 := { dc2 with compInfo := .null, inputScanNumber := 0, unreadMarker := 0 }
    let dcs4 := dcs2.set! 0 dc4
    let h4 := C.Space.put h3 (C.DecompRef.decomp bdc) dcs4
    have hgetdc4 : C.Space.get h4 (C.DecompRef.decomp bdc) = some dcs4 := by simp [h4, C.Space.get, C.Space.put]
    have hgetmk4 : C.Space.get h4 (C.MarkerRef.marker bmrk) = some mrks3 := by simp [h4, h3, C.Space.get, C.Space.put]
    have hszmk4 : 0 < mrks3.size := by simp [mrks3, hszmk]
    have hro_mk4 : C.Space.ro h4 (C.MarkerRef.marker bmrk) = false := rfl
    let mrk4 := { mrks3[0] with sawSOI := FALSE, sawSOF := FALSE, discardedBytes := 0, curMarker := .null }
    let mrks5 := mrks3.set! 0 mrk4
    let h5 := C.Space.put h4 (C.MarkerRef.marker bmrk) mrks5
    have hgetdc5 : C.Space.get h5 (C.DecompRef.decomp bdc) = some dcs4 := hgetdc4
    have hgetmk5 : C.Space.get h5 (C.MarkerRef.marker bmrk) = some mrks5 := by simp [h5, C.Space.get, C.Space.put]
    have hszmk5 : 0 < mrks5.size := by simp [mrks5, hszmk4]
    have hdc4_bang : dc4 = dcs4[0]! := by rw [getElem!_pos _ 0 (by simp [dcs4, hszdc2'])]; simp [dcs4, Array.set!_eq_setIfInBounds]
    have hgeterr5 : C.Space.get h5 rerr = some errs2 := by cases rerr; exact hgeterr2
    have hcov5 : PoolsCoverSince base h5 (some bmem) mems'[0]!.poolAllocs[0]! {} := by
      have hmkne : h_out.markers bmrk ≠ none := by
        change C.Space.get h_out (C.MarkerRef.marker bmrk) ≠ none
        rw [hgetmk]; simp
      have hinbmrk := (hcov2 bmrk hbasemk).2.2.2.2.1 hmkne
      exact poolsCoverSince_put_marker_mem
        (poolsCoverSince_put_marker_mem hcov2 hinbmrk mrks3) hinbmrk mrks5
    have hs5 : CreateSubBase base bdc bmem rerr dcs4 dc4 mems' h5 :=
      ⟨hgetdc5, by simp [dcs4, hszdc2'], hdc4_bang, herrp2, ⟨errs2, hgeterr5, hszerr2⟩,
       hmem2, hgetmem2, hszmem2, hpsz2, hp1_2, hbase2, hcov5⟩
    refine ⟨.ok (), h5, dcs4, dc4, mems', ?_, hs5, hok_out, rfl, bmrk, mrks5, rfl, hgetmk5, hszmk5⟩
    rw [C.run_bind]; erw [hrun]
    dsimp only
    rw [Ptr.load_bind h_out _ 0 dcs _ hgetdc2 hszdc2, hdc2_0]
    rw [Ptr.store_bind h_out (C.DecompRef.decomp bdc) 0 dc2 dcs _ hgetdc2 hro_dc2 hszdc2]
    rw [Ptr.store_bind h2 (C.MarkerRef.marker bmrk) 0 mrk1 mrks _ hgetmk2 hro_mk2 hszmk]
    unfold reset_marker_reader
    simp only [bind_assoc_m]
    rw [Ptr.load_bind h3 _ 0 dcs2 _ hgetdc3 hszdc2']
    have hdc2_step : dcs2[0] = dc2 := by simp [dcs2, Array.set!_eq_setIfInBounds]
    rw [hdc2_step]
    rw [Ptr.store_bind h3 (C.DecompRef.decomp bdc) 0 dc4 dcs2 _ hgetdc3 hro_dc3 hszdc2']
    rw [Ptr.load_bind h4 (C.MarkerRef.marker bmrk) 0 mrks3 _ hgetmk4 hszmk4]
    rw [Ptr.store_bind h4 (C.MarkerRef.marker bmrk) 0 mrk4 mrks3 _ hgetmk4 hro_mk4 hszmk4]
    rfl

private theorem jinit_input_controller_outcome (h : C.Heap) (base bdc bmem bmrk : Nat) (rerr : C.ErrRef)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct)
    (mems : Array C.JpegMemMgr) (mrks : Array C.JpegMarkerReader)
    (hs : CreateSubBase base bdc bmem rerr dcs dc mems h)
    (hmrk : dc.marker = .ref (.marker bmrk) 0)
    (hgetmrk : C.Space.get h (C.MarkerRef.marker bmrk) = some mrks) (hszmrk : 0 < mrks.size) :
    ∃ res h1 dcs1 dc1 mems1,
      C.run (jinit_input_controller (.ref (.decomp bdc) 0)) h = .ok (res, h1) ∧
      CreateSubBase base bdc bmem rerr dcs1 dc1 mems1 h1 ∧ h1.allocOk = h.allocOk ∧
      (match res with
      | .errExit _ => ¬ (∀ n, h.allocOk n = true)
      | .ok () =>
        dc1.src = dc.src ∧
        ∃ bic ics1, dc1.marker = .ref (.marker bmrk) 0 ∧
          C.Space.get h1 (C.MarkerRef.marker bmrk) = some mrks ∧ 0 < mrks.size ∧
          dc1.inputctl = .ref (.inputctl bic) 0 ∧
          C.Space.get h1 (C.InputCtlRef.inputctl bic) = some ics1 ∧ 0 < ics1.size) := by
  unfold jinit_input_controller alloc_small_inputctl
  obtain ⟨res, h_out, mems', hrun, hs_out, hmrk_out, hok_out, hres⟩ :=
    alloc_small_pool0_outcome (R := C.InputCtlRef) h base bdc bmem rerr 48
      allocInputCtl (fun pa p => match p with | .ref (.inputctl b) _ => { pa with inputctls := pa.inputctls.push b } | .null => pa)
      (fun hx => C.Space.get hx (C.MarkerRef.marker bmrk) = some mrks)
      (fun p hx => ∃ bic ics, p = .ref (.inputctl bic) 0 ∧ base ≤ bic ∧ C.Space.get hx (C.InputCtlRef.inputctl bic) = some ics ∧ 0 < ics.size)
      (by decide) (by decide) dcs dc mems hs hgetmrk
      (fun h1 dcs1 dc1 mems1 hs1 hex1 => by
        obtain ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩ := hs1
        by_cases ha : h1.allocOk h1.nalloc = true
        · right
          let bic := h1.nextBlk
          let h_ok : C.Heap := { h1 with inputctls := upd h1.inputctls bic (some #[default]), nextBlk := bic + 1, nalloc := h1.nalloc + 1 }
          refine ⟨.ref (.inputctl bic) 0, h_ok, _, by simp, by simp [C.run, allocInputCtl, ha, bic, h_ok],
            ⟨bic, #[default], rfl, hbase1, by simp [h_ok, C.Space.get, upd_same], by decide⟩,
            hex1, rfl, hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1,
            (by simp [h_ok]; omega), rfl, ?_⟩
          intro k hk
          obtain ⟨hb, hi, hco, hs, hmk, hic, hms, hmm⟩ := hcov1 k hk
          refine ⟨hb, hi, hco, hs, hmk, fun hne => ?_, hms, hmm⟩
          by_cases hkb : k = bic
          · left; rw [hkb]; simp [Array.mem_push]
          · rw [show h_ok.inputctls k = h1.inputctls k from upd_ne _ _ _ _ hkb] at hne
            rcases hic hne with hi0 | hi1
            · left; exact Array.mem_push.mpr (Or.inl hi0)
            · right; exact hi1
        · left
          have hna : ¬ (∀ n, h1.allocOk n = true) := fun hall => ha (hall h1.nalloc)
          have haF : h1.allocOk h1.nalloc = false := Bool.eq_false_iff.mpr ha
          let h_fail : C.Heap := { h1 with nalloc := h1.nalloc + 1 }
          refine ⟨hna, h_fail, by simp [C.run, allocInputCtl, haF, h_fail],
            ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩,
            hex1, rfl⟩)
      (fun _ hx _ _ => hx)
      (fun _ _ _ hx => hx)
      (fun p _ _ hp => hp)
  cases res with
  | errExit code =>
    obtain ⟨_, hnall⟩ := hres
    refine ⟨.errExit code, h_out, dcs, dc, mems', ?_, hs_out, hok_out, hnall⟩
    rw [C.run_bind]; erw [hrun]; rfl
  | ok p =>
    obtain ⟨_, bic, ics, hpEq, hbaseic, hgetic, hszic⟩ := hres
    subst hpEq
    obtain ⟨hgetdc2, hszdc2, hdc2, herrp2, ⟨errs2, hgeterr2, hszerr2⟩, hmem2, hgetmem2, hszmem2, hpsz2, hp1_2, hbase2, hcov2⟩ := hs_out
    have hdc2_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc2]; exact hdc2.symm
    have hro_dc2 : C.Space.ro h_out (C.DecompRef.decomp bdc) = false := rfl
    let dc2 := { dc with inputctl := .ref (.inputctl bic) 0 }
    let dcs2 := dcs.set! 0 dc2
    let h2 := C.Space.put h_out (C.DecompRef.decomp bdc) dcs2
    have hgetic2 : C.Space.get h2 (C.InputCtlRef.inputctl bic) = some ics := hgetic
    have hro_ic2 : C.Space.ro h2 (C.InputCtlRef.inputctl bic) = false := rfl
    let ic1 : C.JpegInputController := {
      consumeInput := .fn "consume_markers"
      resetInputController := .fn "reset_input_controller"
      startInputPass := .fn "start_input_pass"
      finishInputPass := .fn "finish_input_pass"
      hasMultipleScans := FALSE
      eoiReached := FALSE
      inheaders := TRUE
    }
    let ics3 := ics.set! 0 ic1
    let h3 := C.Space.put h2 (C.InputCtlRef.inputctl bic) ics3
    have hgetdc3 : C.Space.get h3 (C.DecompRef.decomp bdc) = some dcs2 := by simp [h3, h2, C.Space.get, C.Space.put]
    have hszdc3 : 0 < dcs2.size := by simp [dcs2, hszdc2]
    have hdc2_bang : dc2 = dcs2[0]! := by rw [getElem!_pos _ 0 hszdc3]; simp [dcs2, Array.set!_eq_setIfInBounds]
    have hgeterr3 : C.Space.get h3 rerr = some errs2 := by cases rerr; exact hgeterr2
    have hcov3 : PoolsCoverSince base h3 (some bmem) mems'[0]!.poolAllocs[0]! {} := by
      have hicne : h_out.inputctls bic ≠ none := by
        change C.Space.get h_out (C.InputCtlRef.inputctl bic) ≠ none
        rw [hgetic]; simp
      have hinbic := (hcov2 bic hbaseic).2.2.2.2.2.1 hicne
      exact poolsCoverSince_put_inputctl_mem hcov2 hinbic ics3
    have hs3 : CreateSubBase base bdc bmem rerr dcs2 dc2 mems' h3 :=
      ⟨hgetdc3, hszdc3, hdc2_bang, herrp2, ⟨errs2, hgeterr3, hszerr2⟩,
       hmem2, hgetmem2, hszmem2, hpsz2, hp1_2, hbase2, hcov3⟩
    refine ⟨.ok (), h3, dcs2, dc2, mems', ?_, hs3, hok_out, rfl, bic, ics3, hmrk, hmrk_out, hszmrk, rfl,
      by simp [h3, C.Space.get, C.Space.put], by simp [ics3, hszic]⟩
    rw [C.run_bind]; erw [hrun]
    dsimp only
    rw [Ptr.load_bind h_out _ 0 dcs _ hgetdc2 hszdc2, hdc2_0]
    rw [Ptr.store_bind h_out (C.DecompRef.decomp bdc) 0 dc2 dcs _ hgetdc2 hro_dc2 hszdc2]
    rw [Ptr.store_bind h2 (C.InputCtlRef.inputctl bic) 0 ic1 ics _ hgetic2 hro_ic2 hszic]
    rfl

private theorem alloc_small_master_outcome (h : C.Heap) (base bdc bmem bmrk bic : Nat) (rerr : C.ErrRef)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct)
    (mems : Array C.JpegMemMgr) (mrks : Array C.JpegMarkerReader) (ics : Array C.JpegInputController)
    (hs : CreateSubBase base bdc bmem rerr dcs dc mems h)
    (hgetmrk : C.Space.get h (C.MarkerRef.marker bmrk) = some mrks) (_hszmrk : 0 < mrks.size)
    (hgetic : C.Space.get h (C.InputCtlRef.inputctl bic) = some ics) (_hszic : 0 < ics.size) :
    ∃ res h1 mems1,
      C.run (alloc_small_master (.ref (.decomp bdc) 0) JPOOL_PERMANENT sizeof_my_decomp_master) h = .ok (res, h1) ∧
      CreateSubBase base bdc bmem rerr dcs dc mems1 h1 ∧ h1.allocOk = h.allocOk ∧
      (match res with
      | .errExit _ => ¬ (∀ n, h.allocOk n = true)
      | .ok mstPtr =>
        ∃ bmas masters1, mstPtr = .ref (.master bmas) 0 ∧ base ≤ bmas ∧
          C.Space.get h1 (C.MasterRef.master bmas) = some masters1 ∧ 0 < masters1.size ∧
          C.Space.get h1 (C.MarkerRef.marker bmrk) = some mrks ∧
          C.Space.get h1 (C.InputCtlRef.inputctl bic) = some ics) := by
  unfold alloc_small_master
  obtain ⟨res, h_out, mems', hrun, hs_out, ⟨hmk_o, hic_o⟩, hok_out, hres⟩ :=
    alloc_small_pool0_outcome (R := C.MasterRef) h base bdc bmem rerr sizeof_my_decomp_master
      allocMaster (fun pa p => match p with | .ref (.master b) _ => { pa with masters := pa.masters.push b } | .null => pa)
      (fun hx => C.Space.get hx (C.MarkerRef.marker bmrk) = some mrks ∧ C.Space.get hx (C.InputCtlRef.inputctl bic) = some ics)
      (fun p hx => ∃ bmas masters, p = .ref (.master bmas) 0 ∧ base ≤ bmas ∧ C.Space.get hx (C.MasterRef.master bmas) = some masters ∧ 0 < masters.size)
      (by decide) (by decide) dcs dc mems hs ⟨hgetmrk, hgetic⟩
      (fun h1 dcs1 dc1 mems1 hs1 ⟨hmk1, hic1⟩ => by
        obtain ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩ := hs1
        by_cases ha : h1.allocOk h1.nalloc = true
        · right
          let bms := h1.nextBlk
          let h_ok : C.Heap := { h1 with masters := upd h1.masters bms (some #[default]), nextBlk := bms + 1, nalloc := h1.nalloc + 1 }
          refine ⟨.ref (.master bms) 0, h_ok, _, by simp, by simp [C.run, allocMaster, ha, bms, h_ok],
            ⟨bms, #[default], rfl, hbase1, by simp [h_ok, C.Space.get, upd_same], by decide⟩,
            ⟨hmk1, hic1⟩, rfl, hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1,
            (by simp [h_ok]; omega), rfl, ?_⟩
          intro k hk
          obtain ⟨hb, hi, hco, hs, hmk, hic, hms, hmm⟩ := hcov1 k hk
          refine ⟨hb, hi, hco, hs, hmk, hic, fun hne => ?_, hmm⟩
          by_cases hkb : k = bms
          · left; rw [hkb]; simp [Array.mem_push]
          · rw [show h_ok.masters k = h1.masters k from upd_ne _ _ _ _ hkb] at hne
            rcases hms hne with hma0 | hma1
            · left; exact Array.mem_push.mpr (Or.inl hma0)
            · right; exact hma1
        · left
          have hna : ¬ (∀ n, h1.allocOk n = true) := fun hall => ha (hall h1.nalloc)
          have haF : h1.allocOk h1.nalloc = false := Bool.eq_false_iff.mpr ha
          let h_fail : C.Heap := { h1 with nalloc := h1.nalloc + 1 }
          refine ⟨hna, h_fail, by simp [C.run, allocMaster, haF, h_fail],
            ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, hmem1, hgetmem1, hszmem1, hpsz1, hp1_1, hbase1, hcov1⟩,
            ⟨hmk1, hic1⟩, rfl⟩)
      (fun _ hx _ _ => hx)
      (fun _ _ _ hx => hx)
      (fun p _ _ hp => hp)
  cases res with
  | errExit code =>
    obtain ⟨_, hnall⟩ := hres
    exact ⟨.errExit code, h_out, mems', hrun, hs_out, hok_out, hnall⟩
  | ok p =>
    obtain ⟨_, bmas, masters, hpEq, hbasema, hgetma, hszma⟩ := hres
    exact ⟨.ok p, h_out, mems', hrun, hs_out, hok_out, bmas, masters, hpEq, hbasema, hgetma, hszma, hmk_o, hic_o⟩

private theorem jpeg_CreateDecompress_outcome (h : C.Heap) (cinfo : C.DecompPtr)
    (version : Int32) (structsize : UInt64) (hinit : FreshDecompInit h cinfo) :
    ∃ res h1 rc dcs1 dc1,
      cinfo = .ref rc 0 ∧
      C.run (jpeg_CreateDecompress cinfo version structsize) h = .ok (res, h1) ∧
      C.Space.get h1 rc = some dcs1 ∧ 0 < dcs1.size ∧ dc1 = dcs1[0]! ∧
      ValidErrMgr h1 dc1.err ∧
      (match dc1.mem with
      | .null => PoolsCoverSince h.nextBlk h1 none {} {} ∧
          (version = JPEG_LIB_VERSION → structsize = sizeof_jpeg_decompress_struct → ¬ (∀ n, h.allocOk n = true))
      | .ref (.mem bmem) 0 =>
        ∃ mems1, C.Space.get h1 (C.MemRef.mem bmem) = some mems1 ∧ 0 < mems1.size ∧
          mems1[0]!.poolAllocs.size = 2 ∧ mems1[0]!.poolAllocs[1]! = {} ∧
          PoolsCoverSince h.nextBlk h1 (some bmem) mems1[0]!.poolAllocs[0]! {} ∧
          (match res with
          | .errExit _ => ¬ (∀ n, h.allocOk n = true)
          | .ok () =>
            ∃ rmas masters ric ics rmrk mrks,
              dc1.master = .ref rmas 0 ∧ C.Space.get h1 rmas = some masters ∧ 0 < masters.size ∧
              dc1.inputctl = .ref ric 0 ∧ C.Space.get h1 ric = some ics ∧ 0 < ics.size ∧
              dc1.marker = .ref rmrk 0 ∧ C.Space.get h1 rmrk = some mrks ∧ 0 < mrks.size ∧
              dc1.globalState = DSTATE_START ∧ dc1.dataPrecision = 8 ∧ dc1.src = .null)
      | .ref (.mem _) (_ + 1) => False) := by
  obtain ⟨rc, dcs, dc, hc, hgetdc, hszdc, hdc, herrValid, hfresh⟩ := hinit
  obtain ⟨rerr, errs, herrp, hgeterr, hszerr⟩ := herrValid
  subst hc
  cases rc with | decomp bdc =>
  unfold jpeg_CreateDecompress errexit2
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have hro_dc : C.Space.ro h (C.DecompRef.decomp bdc) = false := rfl
  let dcA := { dc with mem := .null }
  let dcsA := dcs.set! 0 dcA
  let hA := C.Space.put h (C.DecompRef.decomp bdc) dcsA
  rw [Ptr.store_bind h (C.DecompRef.decomp bdc) 0 dcA dcs _ hgetdc hro_dc hszdc]
  have hszA : 0 < dcsA.size := by simp [dcsA, hszdc]
  have hgetdcA : C.Space.get hA (C.DecompRef.decomp bdc) = some dcsA := by simp [hA, C.Space.get, C.Space.put]
  have hgeterrA : C.Space.get hA rerr = some errs := by cases rerr; exact hgeterr
  have hcovA : PoolsCoverSince h.nextBlk hA none {} {} := poolsCoverSince_of_fresh hfresh
  by_cases hbadV : (version != JPEG_LIB_VERSION) = true
  · simp only [hbadV, ↓reduceIte, herrp, bind_assoc_m]
    rw [Ptr.load_bind hA rerr 0 errs _ hgeterrA hszerr]
    have hro_errA : C.Space.ro hA rerr = false := by cases rerr; rfl
    rw [Ptr.store_bind hA rerr 0 _ errs _ hgeterrA hro_errA hszerr]
    have hneV : version ≠ JPEG_LIB_VERSION := fun heq => by simp [heq] at hbadV
    let err' := { errs[0] with msgCode := JERR_BAD_LIB_VERSION, msgParmI := (errs[0].msgParmI.set! 0 JPEG_LIB_VERSION).set! 1 version }
    let h1 := C.Space.put hA rerr (errs.set! 0 err')
    have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcsA := by cases rerr; exact hgetdcA
    have hdcA_bang : dcA = dcsA[0]! := by rw [getElem!_pos _ 0 hszA]; simp [dcsA, Array.set!_eq_setIfInBounds]
    have hgeterr1 : C.Space.get h1 rerr = some (errs.set! 0 err') := by cases rerr; simp [h1, C.Space.get, C.Space.put]
    refine ⟨.errExit JERR_BAD_LIB_VERSION, h1, .decomp bdc, dcsA, dcA, rfl, rfl, hgetdc1, hszA, hdcA_bang,
      ⟨rerr, errs.set! 0 err', herrp, hgeterr1, by simp [hszerr]⟩, ?_⟩
    simp only [dcA]
    exact ⟨by cases rerr; exact hcovA, fun hv => False.elim (hneV hv)⟩
  · have hgoodV : (version != JPEG_LIB_VERSION) = false := Bool.eq_false_iff.mpr hbadV
    simp only [hgoodV, Bool.false_eq_true, ↓reduceIte]
    by_cases hbadS : (structsize != sizeof_jpeg_decompress_struct) = true
    · simp only [hbadS, ↓reduceIte, herrp, bind_assoc_m]
      rw [Ptr.load_bind hA rerr 0 errs _ hgeterrA hszerr]
      have hro_errA : C.Space.ro hA rerr = false := by cases rerr; rfl
      rw [Ptr.store_bind hA rerr 0 _ errs _ hgeterrA hro_errA hszerr]
      have hneS : structsize ≠ sizeof_jpeg_decompress_struct := fun heq => by simp [heq] at hbadS
      let err' := { errs[0] with
        msgCode := JERR_BAD_STRUCT_SIZE
        msgParmI := (errs[0].msgParmI.set! 0 (Int32.ofNat sizeof_jpeg_decompress_struct.toNat)).set! 1 (Int32.ofNat structsize.toNat) }
      let h1 := C.Space.put hA rerr (errs.set! 0 err')
      have hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcsA := by cases rerr; exact hgetdcA
      have hdcA_bang : dcA = dcsA[0]! := by rw [getElem!_pos _ 0 hszA]; simp [dcsA, Array.set!_eq_setIfInBounds]
      have hgeterr1 : C.Space.get h1 rerr = some (errs.set! 0 err') := by cases rerr; simp [h1, C.Space.get, C.Space.put]
      refine ⟨.errExit JERR_BAD_STRUCT_SIZE, h1, .decomp bdc, dcsA, dcA, rfl, rfl, hgetdc1, hszA, hdcA_bang,
        ⟨rerr, errs.set! 0 err', herrp, hgeterr1, by simp [hszerr]⟩, ?_⟩
      simp only [dcA]
      exact ⟨by cases rerr; exact hcovA, fun _ hs => False.elim (hneS hs)⟩
    · have hgoodS : (structsize != sizeof_jpeg_decompress_struct) = false := Bool.eq_false_iff.mpr hbadS
      simp only [hgoodS, Bool.false_eq_true, ↓reduceIte]
      rw [Ptr.load_bind hA _ 0 dcsA _ hgetdcA hszA]
      have hdcA_0 : dcsA[0] = dcA := by simp [dcsA, Array.set!_eq_setIfInBounds]
      rw [hdcA_0]
      have hmemZ : C.run (memsetZeroDecomp (Ptr.ref (C.DecompRef.decomp bdc) 0)) hA =
          .ok ((), C.Space.put hA (C.DecompRef.decomp bdc) (dcsA.set! 0 C.JpegDecompressStruct.zeroed)) := by
        simp [C.run, memsetZeroDecomp, hgetdcA, hszA, C.Space.modify_eq hA _ dcsA _ hgetdcA]
      rw [C.run_bind, hmemZ]
      dsimp only
      let dcsB := dcsA.set! 0 C.JpegDecompressStruct.zeroed
      let hB := C.Space.put hA (C.DecompRef.decomp bdc) dcsB
      have hgetdcB : C.Space.get hB (C.DecompRef.decomp bdc) = some dcsB := by simp [hB, C.Space.get, C.Space.put]
      have hszB : 0 < dcsB.size := by simp [dcsB, hszA]
      rw [Ptr.load_bind hB _ 0 dcsB _ hgetdcB hszB]
      have hdcB_0 : dcsB[0] = C.JpegDecompressStruct.zeroed := by simp [dcsB, Array.set!_eq_setIfInBounds]
      rw [hdcB_0]
      have hro_dcB : C.Space.ro hB (C.DecompRef.decomp bdc) = false := rfl
      let dcC := { C.JpegDecompressStruct.zeroed with err := dcA.err, clientData := dcA.clientData, isDecompressor := TRUE }
      let dcsC := dcsB.set! 0 dcC
      let hC := C.Space.put hB (C.DecompRef.decomp bdc) dcsC
      rw [Ptr.store_bind hB (C.DecompRef.decomp bdc) 0 dcC dcsB _ hgetdcB hro_dcB hszB]
      have hgetdcC : C.Space.get hC (C.DecompRef.decomp bdc) = some dcsC := by simp [hC, C.Space.get, C.Space.put]
      have hszC : 0 < dcsC.size := by simp [dcsC, hszB]
      have hdcC_bang : dcC = dcsC[0]! := by rw [getElem!_pos _ 0 hszC]; simp [dcsC, Array.set!_eq_setIfInBounds]
      have herrC : dcC.err = .ref rerr 0 := herrp
      have herrLiveC : ∃ errs, C.Space.get hC rerr = some errs ∧ 0 < errs.size := ⟨errs, by cases rerr; exact hgeterrA, hszerr⟩
      have hnextC : h.nextBlk ≤ hC.nextBlk := by simp [hC, hB, hA, C.Space.put]
      have hcovC : PoolsCoverSince h.nextBlk hC none {} {} := hcovA
      obtain ⟨resM, hD, dcsD, dcD, hrunM, hgetdcD, hszDC, hdcD, herrD, ⟨errsD, hgeterrD, hszerrD⟩, hnextD, hokD, hmCase⟩ :=
        jinit_memory_mgr_outcome hC bdc h.nextBlk dcsC dcC rerr hgetdcC hszC hdcC_bang herrC herrLiveC hnextC hcovC
      have hszD : 0 < dcsD.size := by rw [hszDC]; exact hszC
      rw [C.run_bind, hrunM]
      dsimp only
      cases resM with
      | errExit code =>
        obtain ⟨hmemNull, hcovD, hnall⟩ := hmCase
        refine ⟨.errExit code, hD, .decomp bdc, dcsD, dcD, rfl, rfl, hgetdcD, hszD, hdcD,
          ⟨rerr, errsD, herrD, hgeterrD, hszerrD⟩, ?_⟩
        rw [hmemNull]
        exact ⟨hcovD, fun _ _ => hnall⟩
      | ok _ =>
        obtain ⟨bmem, memsD, hmemD, _hbmem, hgetmemD, hszmemD, hpD, _hlpD, _, hcovD⟩ := hmCase
        rw [Ptr.load_bind hD _ 0 dcsD _ hgetdcD hszD]
        have hdcD_0 : dcsD[0] = dcD := by rw [← getElem!_pos dcsD 0 hszD]; exact hdcD.symm
        rw [hdcD_0]
        have hro_dcD : C.Space.ro hD (C.DecompRef.decomp bdc) = false := rfl
        let dcE := {
          dcD with
          progress := .null
          src := .null
          quantTblPtrs := Array.replicate 4 .null
          dcHuffTblPtrs := Array.replicate 4 .null
          acHuffTblPtrs := Array.replicate 4 .null
          markerList := .null
        }
        let dcsE := dcsD.set! 0 dcE
        let hE := C.Space.put hD (C.DecompRef.decomp bdc) dcsE
        rw [Ptr.store_bind hD (C.DecompRef.decomp bdc) 0 dcE dcsD _ hgetdcD hro_dcD hszD]
        have hgetdcE : C.Space.get hE (C.DecompRef.decomp bdc) = some dcsE := by simp [hE, C.Space.get, C.Space.put]
        have hszE : 0 < dcsE.size := by simp [dcsE, hszD]
        have hdcE_bang : dcE = dcsE[0]! := by rw [getElem!_pos _ 0 hszE]; simp [dcsE, Array.set!_eq_setIfInBounds]
        have hgeterrE : C.Space.get hE rerr = some errsD := by cases rerr; exact hgeterrD
        have hgetmemE : C.Space.get hE (C.MemRef.mem bmem) = some memsD := hgetmemD
        have hpD0 : memsD[0]!.poolAllocs[0]! = {} := by rw [hpD]; decide
        have hcovE : PoolsCoverSince h.nextBlk hE (some bmem) memsD[0]!.poolAllocs[0]! {} := by
          rw [hpD0]; exact hcovD
        have hsE : CreateSubBase h.nextBlk bdc bmem rerr dcsE dcE memsD hE :=
          ⟨hgetdcE, hszE, hdcE_bang, herrD, ⟨errsD, hgeterrE, hszerrD⟩, hmemD, hgetmemE, hszmemD,
           (by rw [hpD]; decide), (by rw [hpD]; rfl), hnextD, hcovE⟩
        obtain ⟨resMk, hF, dcsF, dcF, memsF, hrunMk, hsF, hokF, hmMk⟩ :=
          jinit_marker_reader_outcome hE h.nextBlk bdc bmem rerr dcsE dcE memsD hsE
        rw [C.run_bind, hrunMk]
        dsimp only
        cases resMk with
        | errExit code =>
          obtain ⟨hgetdcF, hszdcF, hdcF, herrpF, ⟨errsF, hgeterrF, hszerrF⟩, hmemF, hgetmemF, hszmemF, hpszF, hp1F, _, hcovF⟩ := hsF
          refine ⟨.errExit code, hF, .decomp bdc, dcsF, dcF, rfl, rfl, hgetdcF, hszdcF, hdcF,
            ⟨rerr, errsF, herrpF, hgeterrF, hszerrF⟩, ?_⟩
          rw [hmemF]
          refine ⟨memsF, hgetmemF, hszmemF, hpszF, hp1F, hcovF, ?_⟩
          change ¬ (∀ n, hD.allocOk n = true) at hmMk
          rw [hokD] at hmMk
          exact hmMk
        | ok _ =>
          obtain ⟨hsrcF, bmrk, mrksF, hmrkF, hgetmkF, hszmkF⟩ := hmMk
          obtain ⟨resIc, hG, dcsG, dcG, memsG, hrunIc, hsG, hokG, hmIc⟩ :=
            jinit_input_controller_outcome hF h.nextBlk bdc bmem bmrk rerr dcsF dcF memsF mrksF hsF hmrkF hgetmkF hszmkF
          rw [C.run_bind, hrunIc]
          dsimp only
          cases resIc with
          | errExit code =>
            obtain ⟨hgetdcG, hszdcG, hdcG, herrpG, ⟨errsG, hgeterrG, hszerrG⟩, hmemG, hgetmemG, hszmemG, hpszG, hp1G, _, hcovG⟩ := hsG
            refine ⟨.errExit code, hG, .decomp bdc, dcsG, dcG, rfl, rfl, hgetdcG, hszdcG, hdcG,
              ⟨rerr, errsG, herrpG, hgeterrG, hszerrG⟩, ?_⟩
            rw [hmemG]
            refine ⟨memsG, hgetmemG, hszmemG, hpszG, hp1G, hcovG, ?_⟩
            rw [hokF] at hmIc
            change ¬ (∀ n, hD.allocOk n = true) at hmIc
            rw [hokD] at hmIc
            exact hmIc
          | ok _ =>
            obtain ⟨hsrcG, bic, icsG, hmrkG, hgetmkG, hszmkG, hicG, hgeticG, hszicG⟩ := hmIc
            obtain ⟨hgetdcG, hszdcG, hdcG, herrpG, ⟨errsG, hgeterrG, hszerrG⟩, hmemG, hgetmemG, hszmemG, hpszG, hp1G, hnextG, hcovG⟩ := hsG
            rw [Ptr.load_bind hG _ 0 dcsG _ hgetdcG hszdcG]
            have hdcG_0 : dcsG[0] = dcG := by rw [← getElem!_pos dcsG 0 hszdcG]; exact hdcG.symm
            rw [hdcG_0]
            have hro_dcG : C.Space.ro hG (C.DecompRef.decomp bdc) = false := rfl
            let dcH := { dcG with dataPrecision := 8, globalState := DSTATE_START }
            let dcsH := dcsG.set! 0 dcH
            let hH := C.Space.put hG (C.DecompRef.decomp bdc) dcsH
            rw [Ptr.store_bind hG (C.DecompRef.decomp bdc) 0 dcH dcsG _ hgetdcG hro_dcG hszdcG]
            have hgetdcH : C.Space.get hH (C.DecompRef.decomp bdc) = some dcsH := by simp [hH, C.Space.get, C.Space.put]
            have hszH : 0 < dcsH.size := by simp [dcsH, hszdcG]
            have hdcH_bang : dcH = dcsH[0]! := by rw [getElem!_pos _ 0 hszH]; simp [dcsH, Array.set!_eq_setIfInBounds]
            have hgeterrH : C.Space.get hH rerr = some errsG := by cases rerr; exact hgeterrG
            have hsH : CreateSubBase h.nextBlk bdc bmem rerr dcsH dcH memsG hH :=
              ⟨hgetdcH, hszH, hdcH_bang, herrpG, ⟨errsG, hgeterrH, hszerrG⟩, hmemG, hgetmemG, hszmemG, hpszG, hp1G, hnextG, hcovG⟩
            obtain ⟨resMa, hI, memsI, hrunMa, hsI, hokI, hmMa⟩ :=
              alloc_small_master_outcome hH h.nextBlk bdc bmem bmrk bic rerr dcsH dcH memsG mrksF icsG hsH hgetmkG hszmkG hgeticG hszicG
            rw [C.run_bind, hrunMa]
            dsimp only
            cases resMa with
            | errExit code =>
              obtain ⟨hgetdcI, hszdcI, hdcI, herrpI, ⟨errsI, hgeterrI, hszerrI⟩, hmemI, hgetmemI, hszmemI, hpszI, hp1I, _, hcovI⟩ := hsI
              refine ⟨.errExit code, hI, .decomp bdc, dcsH, dcH, rfl, rfl, hgetdcI, hszdcI, hdcI,
                ⟨rerr, errsI, herrpI, hgeterrI, hszerrI⟩, ?_⟩
              rw [hmemI]
              refine ⟨memsI, hgetmemI, hszmemI, hpszI, hp1I, hcovI, ?_⟩
              change ¬ (∀ n, hG.allocOk n = true) at hmMa
              rw [hokG, hokF] at hmMa
              change ¬ (∀ n, hD.allocOk n = true) at hmMa
              rw [hokD] at hmMa
              exact hmMa
            | ok mstPtr =>
              obtain ⟨bmas, mastersI, hmstEq, hbasema, hgetmaI, hszmaI, hgetmkI, hgeticI⟩ := hmMa
              subst hmstEq
              obtain ⟨hgetdcI, hszdcI, hdcI, herrpI, ⟨errsI, hgeterrI, hszerrI⟩, hmemI, hgetmemI, hszmemI, hpszI, hp1I, _, hcovI⟩ := hsI
              rw [Ptr.load_bind hI _ 0 dcsH _ hgetdcI hszdcI]
              have hdcI_0 : dcsH[0] = dcH := by rw [← getElem!_pos dcsH 0 hszdcI]; exact hdcI.symm
              rw [hdcI_0]
              have hro_dcI : C.Space.ro hI (C.DecompRef.decomp bdc) = false := rfl
              let dcJ := { dcH with master := .ref (.master bmas) 0 }
              let dcsJ := dcsH.set! 0 dcJ
              let hJ := C.Space.put hI (C.DecompRef.decomp bdc) dcsJ
              rw [Ptr.store_bind hI (C.DecompRef.decomp bdc) 0 dcJ dcsH _ hgetdcI hro_dcI hszdcI]
              have hro_maI : C.Space.ro hJ (C.MasterRef.master bmas) = false := rfl
              have hgetmaJ : C.Space.get hJ (C.MasterRef.master bmas) = some mastersI := hgetmaI
              let mastersK := mastersI.set! 0 C.JpegDecompMaster.zeroed
              let hK := C.Space.put hJ (C.MasterRef.master bmas) mastersK
              have hmemZ_ma : C.run (memsetZeroMaster (.ref (.master bmas) 0)) hJ = .ok ((), hK) := by
                simp [C.run, memsetZeroMaster, hgetmaJ, hro_maI, hszmaI, C.Space.modify_eq hJ _ mastersI _ hgetmaJ, hK, mastersK]
              rw [C.run_bind, hmemZ_ma]
              dsimp only
              have hgetdcK : C.Space.get hK (C.DecompRef.decomp bdc) = some dcsJ := by simp [hK, hJ, C.Space.get, C.Space.put]
              have hszdcK : 0 < dcsJ.size := by simp [dcsJ, hszdcI]
              have hdcJ_bang : dcJ = dcsJ[0]! := by rw [getElem!_pos _ 0 hszdcK]; simp [dcsJ, Array.set!_eq_setIfInBounds]
              have hgeterrK : C.Space.get hK rerr = some errsI := by cases rerr; exact hgeterrI
              have hgetmemK : C.Space.get hK (C.MemRef.mem bmem) = some memsI := hgetmemI
              have hgetmaK : C.Space.get hK (C.MasterRef.master bmas) = some mastersK := by simp [hK, C.Space.get, C.Space.put]
              have hgetmkK : C.Space.get hK (C.MarkerRef.marker bmrk) = some mrksF := hgetmkI
              have hgeticK : C.Space.get hK (C.InputCtlRef.inputctl bic) = some icsG := hgeticI
              have hmane : hI.masters bmas ≠ none := by
                change C.Space.get hI (C.MasterRef.master bmas) ≠ none
                rw [hgetmaI]; simp
              have hinbmas := (hcovI bmas hbasema).2.2.2.2.2.2.1 hmane
              have hcovK : PoolsCoverSince h.nextBlk hK (some bmem) memsI[0]!.poolAllocs[0]! {} :=
                poolsCoverSince_put_master_mem hcovI hinbmas mastersK
              refine ⟨.ok (), hK, .decomp bdc, dcsJ, dcJ, rfl, rfl, hgetdcK, hszdcK, hdcJ_bang,
                ⟨rerr, errsI, herrpI, hgeterrK, hszerrI⟩, ?_⟩
              rw [hmemI]
              refine ⟨memsI, hgetmemK, hszmemI, hpszI, hp1I, hcovK,
                .master bmas, mastersK, .inputctl bic, icsG, .marker bmrk, mrksF,
                rfl, hgetmaK, (by simp [mastersK, hszmaI]),
                hicG, hgeticK, hszicG,
                hmrkG, hgetmkK, hszmkF,
                rfl, rfl, ?_⟩
              dsimp [dcJ, dcH]
              rw [hsrcG, hsrcF]

theorem jpeg_CreateDecompress_safety : Goal.jpeg_CreateDecompress_safety := by
  intro h cinfo version structsize hinit
  obtain ⟨res, h1, _, _, _, _, hrun, _⟩ := jpeg_CreateDecompress_outcome h cinfo version structsize hinit
  exact ⟨res, h1, hrun⟩

theorem jpeg_CreateDecompress_establishes_valid : Goal.jpeg_CreateDecompress_establishes_valid := by
  intro h cinfo hinit hallOk
  obtain ⟨res, h1, rc, dcs1, dc1, hc, hrun, hgetdc1, hszdc1, hdc1, herrValid1, hmemCase⟩ :=
    jpeg_CreateDecompress_outcome h cinfo JPEG_LIB_VERSION sizeof_jpeg_decompress_struct hinit
  cases hmem : dc1.mem with
  | null =>
    rw [hmem] at hmemCase
    exact False.elim (hmemCase.2 rfl rfl hallOk)
  | ref rm off =>
    cases rm with | mem bmem =>
    cases off with
    | succ k =>
      rw [hmem] at hmemCase
      exact False.elim hmemCase
    | zero =>
      rw [hmem] at hmemCase
      obtain ⟨mems1, hgetmem1, hszmem1, hpsz1, hp1_1, _, hresCase⟩ := hmemCase
      cases res with
      | errExit code =>
        exact False.elim (hresCase hallOk)
      | ok _ =>
        obtain ⟨rmas, masters, ric, ics, rmrk, mrks, hmas, hgetmas, hszmas,
          hic, hgetic, hszic, hmrk, hgetmrk, hszmrk, hgs, hdp, hsrc⟩ := hresCase
        have hcore : ValidDecompCore h1 cinfo := by
          refine ⟨rc, dcs1, dc1, .mem bmem, mems1, rmas, masters, ric, ics, rmrk, mrks,
            hc, hgetdc1, hszdc1, hdc1, herrValid1, hmem, hgetmem1, hszmem1,
            hmas, hgetmas, hszmas, hic, hgetic, hszic, hmrk, hgetmrk, hszmrk,
            by omega, fun bmas _ => by rw [hp1_1]; simp⟩
        have hvmem : ValidDecompMem h1 cinfo := by
          refine ⟨rc, dcs1, dc1, .mem bmem, mems1, hc, hgetdc1, hszdc1, hdc1, herrValid1,
            hmem, hgetmem1, hszmem1, by omega, Or.inl hsrc⟩
        exact ⟨h1, rc, dcs1, hc, hrun, hcore, hvmem, hgetdc1, hszdc1, by rw [← hdc1]; exact hgs,
          by rw [← hdc1]; exact hdp, by rw [← hdc1]; exact hsrc⟩

private theorem poolAllocs0_set1_eq (mems : Array C.JpegMemMgr)
    (h0 : 0 < mems.size) (h0p : 0 < mems[0]!.poolAllocs.size) :
    ((mems.set! 0 {
      mems[0]! with
      livePools := mems[0]!.livePools.set! 1 false
      poolAllocs := mems[0]!.poolAllocs.set! 1 {}
    })[0]!).poolAllocs[0]! = mems[0]!.poolAllocs[0]! := by
  let m : C.JpegMemMgr := {
    mems[0]! with
    livePools := mems[0]!.livePools.set! 1 false
    poolAllocs := mems[0]!.poolAllocs.set! 1 {}
  }
  have h1 : 0 < (mems.set! 0 m).size := by simp [h0]
  have houter : (mems.set! 0 m)[0]! = m := by
    rw [getElem!_pos (mems.set! 0 m) 0 h1]
    simp
  change (mems.set! 0 m)[0]!.poolAllocs[0]! = mems[0]!.poolAllocs[0]!
  rw [houter]
  dsimp only [m]
  have h2 : 0 < (mems[0]!.poolAllocs.set! 1 {}).size := by simp [h0p]
  rw [getElem!_pos _ 0 h2, getElem!_pos (mems[0]!.poolAllocs) 0 h0p]
  simp [h0p]

private theorem self_destruct_destroy_freshNextBlk
    (h1 : C.Heap) (base bdc bmem : Nat) (dcs1 : Array C.JpegDecompressStruct) (dc1 : C.JpegDecompressStruct)
    (mems1 : Array C.JpegMemMgr)
    (hgetdc1 : C.Space.get h1 (C.DecompRef.decomp bdc) = some dcs1) (hszdc1 : 0 < dcs1.size)
    (hdc1 : dc1 = dcs1[0]!) (hmem : dc1.mem = .ref (.mem bmem) 0)
    (hgetmem1 : C.Space.get h1 (C.MemRef.mem bmem) = some mems1) (hszmem1 : 0 < mems1.size)
    (hpsz1 : mems1[0]!.poolAllocs.size = 2) (_hp1_1 : mems1[0]!.poolAllocs[1]! = {})
    (hcov : PoolsCoverSince base h1 (some bmem) mems1[0]!.poolAllocs[0]! {}) :
    ∃ h6,
      C.run (jpeg_destroy_decompress (.ref (.decomp bdc) 0)) h1 = .ok ((), h6) ∧
      ∀ k, base ≤ k →
        h6.bytes k = none ∧ h6.i32s k = none ∧ h6.mems k = none ∧
        h6.masters k = none ∧ h6.markers k = none ∧ h6.inputctls k = none ∧
        h6.srcs k = none ∧ h6.comps k = none := by
  have hdc1_0 : dcs1[0] = dc1 := by rw [← getElem!_pos dcs1 0 hszdc1]; exact hdc1.symm
  have hfp1 := free_pool_ok h1 bdc bmem 1 dcs1 dc1 mems1 hgetdc1 hszdc1 hdc1 hmem hgetmem1 hszmem1
    (by decide) (by decide)
  dsimp only at hfp1
  let pa1 := (mems1[0]!).poolAllocs[(1 : Int32).toInt.toNat]!
  let h2_f := freePoolAllocs pa1 h1
  let mem2 := { mems1[0]! with livePools := mems1[0]!.livePools.set! (1 : Int32).toInt.toNat false,
                               poolAllocs := mems1[0]!.poolAllocs.set! (1 : Int32).toInt.toNat {} }
  let h2 := C.Space.put h2_f (C.MemRef.mem bmem) (mems1.set! 0 mem2)
  have hgetdc2 : C.Space.get h2 (C.DecompRef.decomp bdc) = some dcs1 := hgetdc1
  have hgetmem2 : C.Space.get h2 (C.MemRef.mem bmem) = some (mems1.set! 0 mem2) := by
    simp [h2, C.Space.get, C.Space.put]
  have hszmem2 : 0 < (mems1.set! 0 mem2).size := by rw [Array.size_set!]; exact hszmem1
  have hfp0 := free_pool_ok h2 bdc bmem 0 dcs1 dc1 (mems1.set! 0 mem2) hgetdc2 hszdc1 hdc1 hmem hgetmem2 hszmem2
    (by decide) (by decide)
  dsimp only at hfp0
  let mems2 := mems1.set! 0 mem2
  let pa0 := (mems2[0]!).poolAllocs[(0 : Int32).toInt.toNat]!
  let h3_f := freePoolAllocs pa0 h2
  let mem3 := { mems2[0]! with livePools := mems2[0]!.livePools.set! (0 : Int32).toInt.toNat false,
                               poolAllocs := mems2[0]!.poolAllocs.set! (0 : Int32).toInt.toNat {} }
  let h3 := C.Space.put h3_f (C.MemRef.mem bmem) (mems2.set! 0 mem3)
  have hgetmem3 : h3.mems bmem = some (mems2.set! 0 mem3) := by
    simp [h3, C.Space.put, h3_f, freePoolAllocs]
  let h4 : C.Heap := { h3 with mems := upd h3.mems bmem none }
  have hfree_mem : C.run (freeMemMgr (Ptr.ref (C.MemRef.mem bmem) 0)) h3 = .ok ((), h4) := by
    simp [C.run, freeMemMgr, hgetmem3]; rfl
  have hgetdc4 : C.Space.get h4 (C.DecompRef.decomp bdc) = some dcs1 := hgetdc2
  have hro_dc4 : C.Space.ro h4 (C.DecompRef.decomp bdc) = false := rfl
  let dc4 := { dc1 with mem := .null }
  let h5 := C.Space.put h4 (C.DecompRef.decomp bdc) (dcs1.set! 0 dc4)
  have hgetdc5 : C.Space.get h5 (C.DecompRef.decomp bdc) = some (dcs1.set! 0 dc4) := by
    simp [h5, C.Space.get, C.Space.put]
  have hszdc5 : 0 < (dcs1.set! 0 dc4).size := by rw [Array.size_set!]; exact hszdc1
  have hro_dc5 : C.Space.ro h5 (C.DecompRef.decomp bdc) = false := rfl
  let h6 := C.Space.put h5 (C.DecompRef.decomp bdc) ((dcs1.set! 0 dc4).set! 0 { dc4 with globalState := 0 })
  refine ⟨h6, ?_, fun k hk => ?_⟩
  · unfold jpeg_destroy_decompress jpeg_destroy Mozjpeg.Jmemmgr.self_destruct jpeg_free_small_mem jpeg_mem_term
    rw [Ptr.load_bind h1 _ 0 dcs1 _ hgetdc1 hszdc1, hdc1_0]
    have hmemne : (Ptr.ref (C.MemRef.mem bmem) 0 != Ptr.null) = true := rfl
    simp only [hmem, hmemne, ↓reduceIte, bind_assoc_m]
    rw [C.run_bind, hfp1]; dsimp only
    rw [C.run_bind, hfp0]; dsimp only
    rw [Ptr.load_bind h3 _ 0 dcs1 _ hgetdc2 hszdc1, hdc1_0, hmem]
    rw [C.run_bind, hfree_mem]; dsimp only
    rw [Ptr.load_bind h4 _ 0 dcs1 _ hgetdc4 hszdc1, hdc1_0]
    rw [Ptr.store_bind h4 _ 0 dc4 dcs1 _ hgetdc4 hro_dc4 hszdc1]
    simp only [pure_bind_m]
    rw [Ptr.load_bind h5 _ 0 (dcs1.set! 0 dc4) _ hgetdc5 hszdc5]
    have hdc4_0 : (dcs1.set! 0 dc4)[0] = dc4 := by simp [Array.set!_eq_setIfInBounds]
    rw [hdc4_0]
    simp only [C.run, Ptr.store, hgetdc5, hro_dc5, hszdc5, ↓reduceIte]
    rw [C.Space.modify_eq h5 (C.DecompRef.decomp bdc) (dcs1.set! 0 dc4) _ hgetdc5]
    rfl
  · obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hcov k hk
    have h0p : 0 < mems1[0]!.poolAllocs.size := by omega
    have hpa0_eq : pa0 = mems1[0]!.poolAllocs[0]! :=
      poolAllocs0_set1_eq mems1 hszmem1 h0p
    have hmnone_k : h6.mems k = none := by
      by_cases hkb : k = bmem
      · subst hkb; simp [h6, h5, h4, C.Space.put, upd_same]
      · have : h1.mems k = none := by
          cases hm : h1.mems k with
          | none => rfl
          | some _ => exact False.elim (hkb (Option.some.inj (hmm (by simp [hm]))))
        simp [h6, h5, h4, h3, h3_f, h2, h2_f, C.Space.put, freePoolAllocs, upd_ne _ _ _ _ hkb, this]
    have clearConst : ∀ {α : Type} (sel : PoolAllocs → Array Nat)
        (getT : C.Heap → Tbl (Option α))
        (hput3 : getT h3_f = (sel pa0).foldl (fun t b => upd t b none) (getT h2))
        (hput2 : getT h2_f = (sel pa1).foldl (fun t b => upd t b none) (getT h1))
        (hsame6 : getT h6 = getT h3_f)
        (hsame2 : getT h2 k = getT h2_f k)
        (hk1 : getT h1 k = none),
        getT h6 k = none := by
      intro α sel getT hput3 hput2 hsame6 hsame2 hk1
      rw [hsame6, hput3]
      apply foldl_upd_none_eq_none_of
      right; rw [hsame2, hput2]
      exact foldl_upd_none_eq_none_of _ _ _ (Or.inr hk1)
    have clearTbl : ∀ {α : Type} (sel : PoolAllocs → Array Nat)
        (getT : C.Heap → Tbl (Option α))
        (hselEmpty : sel {} = #[])
        (hput3 : getT h3_f = (sel pa0).foldl (fun t b => upd t b none) (getT h2))
        (hput2 : getT h2_f = (sel pa1).foldl (fun t b => upd t b none) (getT h1))
        (hsame6 : getT h6 = getT h3_f)
        (hsame2 : getT h2 k = getT h2_f k)
        (hcovT : getT h1 k ≠ none → k ∈ (sel (mems1[0]!.poolAllocs[0]!)) ∨ k ∈ (sel {})),
        getT h6 k = none := by
      intro α sel getT hselEmpty hput3 hput2 hsame6 hsame2 hcovT
      rw [hsame6, hput3]
      apply foldl_upd_none_eq_none_of
      by_cases hnone : getT h2 k = none
      · right; exact hnone
      · left
        rw [hpa0_eq]
        have h1ne : getT h1 k ≠ none := by
          intro h1n
          apply hnone
          rw [hsame2, hput2]
          exact foldl_upd_none_eq_none_of _ _ _ (Or.inr h1n)
        rcases hcovT h1ne with h0 | h1m
        · exact h0
        · exfalso; rw [hselEmpty] at h1m; simp at h1m
    have hb6 : h6.bytes k = none := clearConst (fun p => p.bytes) C.Heap.bytes
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hb
    have hi6 : h6.i32s k = none := clearConst (fun p => p.i32s) C.Heap.i32s
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hi
    have hco6 : h6.comps k = none := clearConst (fun p => p.comps) C.Heap.comps
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hco
    have hsrc_none : h6.srcs k = none := clearTbl (fun p => p.srcs) C.Heap.srcs rfl
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hsrc
    have hmk_none : h6.markers k = none := clearTbl (fun p => p.markers) C.Heap.markers rfl
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hmk
    have hic_none : h6.inputctls k = none := clearTbl (fun p => p.inputctls) C.Heap.inputctls rfl
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hic
    have hms_none : h6.masters k = none := clearTbl (fun p => p.masters) C.Heap.masters rfl
        (by simp only [h3_f, freePoolAllocs]) (by simp only [h2_f, freePoolAllocs])
        (by simp only [h6, h5, h4, h3, C.Space.put]) (by simp only [h2, C.Space.put]) hms
    exact ⟨hb6, hi6, hmnone_k, hms_none, hmk_none, hic_none, hsrc_none, hco6⟩

theorem jpeg_CreateDecompress_destroy_no_leak : Goal.jpeg_CreateDecompress_destroy_no_leak := by
  intro h cinfo version structsize hinit
  obtain ⟨res, h1, rc, dcs1, dc1, hc, hrun1, hgetdc1, hszdc1, hdc1, _, hmemCase⟩ :=
    jpeg_CreateDecompress_outcome h cinfo version structsize hinit
  subst hc
  cases rc with | decomp bdc =>
  have hdc1_0 : dcs1[0] = dc1 := by rw [← getElem!_pos dcs1 0 hszdc1]; exact hdc1.symm
  cases hmem : dc1.mem with
  | null =>
    rw [hmem] at hmemCase
    obtain ⟨hcov, _⟩ := hmemCase
    let dc1' := { dc1 with globalState := 0 }
    let h2 := C.Space.put h1 (C.DecompRef.decomp bdc) (dcs1.set! 0 dc1')
    refine ⟨res, h1, h2, hrun1, ?_, fun k hk => ?_⟩
    · unfold jpeg_destroy_decompress jpeg_destroy
      have hnullne : (Ptr.null (R := C.MemRef) != Ptr.null) = false := rfl
      rw [Ptr.load_bind h1 _ 0 dcs1 _ hgetdc1 hszdc1, hdc1_0, hmem]
      simp only [hnullne, Bool.false_eq_true, ↓reduceIte]
      rw [Ptr.load_bind h1 _ 0 dcs1 _ hgetdc1 hszdc1, hdc1_0]
      have hro_dc1 : C.Space.ro h1 (C.DecompRef.decomp bdc) = false := rfl
      simp [C.run, Ptr.store, hgetdc1, hro_dc1, hszdc1, C.Space.modify_eq h1 _ dcs1 _ hgetdc1, hmem, h2, dc1']
    · obtain ⟨hb, hi, hco, hsrc, hmk, hic, hms, hmm⟩ := hcov k hk
      refine ⟨hb, hi, ?_, ?_, ?_, ?_, ?_, hco⟩
      · exact Classical.byContradiction fun hne => by cases hmm hne
      · exact Classical.byContradiction fun hne => by rcases hms hne with hm | hm <;> simp at hm
      · exact Classical.byContradiction fun hne => by rcases hmk hne with hm | hm <;> simp at hm
      · exact Classical.byContradiction fun hne => by rcases hic hne with hm | hm <;> simp at hm
      · exact Classical.byContradiction fun hne => by rcases hsrc hne with hm | hm <;> simp at hm
  | ref rm off =>
    cases rm with | mem bmem =>
    cases off with
    | succ k =>
      rw [hmem] at hmemCase
      exact False.elim hmemCase
    | zero =>
      rw [hmem] at hmemCase
      obtain ⟨mems1, hgetmem1, hszmem1, hpsz1, hp1_1, hcov, _⟩ := hmemCase
      obtain ⟨h6, hrun2, hcov6⟩ :=
        self_destruct_destroy_freshNextBlk h1 h.nextBlk bdc bmem dcs1 dc1 mems1
          hgetdc1 hszdc1 hdc1 hmem hgetmem1 hszmem1 hpsz1 hp1_1 hcov
      exact ⟨res, h1, h6, hrun1, hrun2, hcov6⟩

end MozjpegF.Proof.Jdapimin
