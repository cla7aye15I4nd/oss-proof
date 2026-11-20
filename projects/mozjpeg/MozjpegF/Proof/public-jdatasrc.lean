import MozjpegF.Spec.Safety.Goals
import MozjpegF.Spec.Functional.Goals
import MozjpegF.Proof.«jmemmgr.c.helpers»

/-!
# Proofs of `jdatasrc.c` safety and functional specifications (`MozjpegF`)
-/

set_option autoImplicit false

namespace MozjpegF.Proof.Jdatasrc
open C MozjpegF.Spec MozjpegF.Spec.Safety MozjpegF.Spec.Functional MozjpegF.Proof.JmemmgrHelpers
open Mozjpeg.Jdatasrc Mozjpeg.Jmemmgr Mozjpeg.JpeglibH Mozjpeg.JerrorH

private def SrcMemPres (bdc bmem : Nat) (dcs : Array JpegDecompressStruct)
    (dc : JpegDecompressStruct) (mems : Array JpegMemMgr) (rerr : ErrRef) (h : C.Heap) : Prop :=
  C.Space.get h (C.DecompRef.decomp bdc) = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
  dc.err = .ref rerr 0 ∧ (∃ errs, C.Space.get h rerr = some errs ∧ 0 < errs.size) ∧
  dc.mem = .ref (.mem bmem) 0 ∧ C.Space.get h (C.MemRef.mem bmem) = some mems ∧ 0 < mems.size ∧
  2 ≤ (mems[0]!).poolAllocs.size

private theorem alloc_small_src_ok (h : C.Heap) (bdc bmem : Nat)
    (dcs : Array C.JpegDecompressStruct) (dc : C.JpegDecompressStruct) (mems : Array C.JpegMemMgr)
    (rerr : C.ErrRef)
    (hp : SrcMemPres bdc bmem dcs dc mems rerr h) :
    (∃ h_err, C.run (alloc_small_src (.ref (.decomp bdc) 0) JPOOL_PERMANENT sizeof_jpeg_source_mgr) h =
      .ok (.errExit JERR_OUT_OF_MEMORY, h_err)) ∨
    (∃ (bsrc : Nat) (h_ok : C.Heap) (srcs : Array C.JpegSourceMgr),
      C.run (alloc_small_src (.ref (.decomp bdc) 0) JPOOL_PERMANENT sizeof_jpeg_source_mgr) h =
        .ok (.ok (.ref (.src bsrc) 0), h_ok) ∧
      C.Space.get h_ok (C.DecompRef.decomp bdc) = some dcs ∧
      C.Space.get h_ok (C.SrcRef.src bsrc) = some srcs ∧ 0 < srcs.size) := by
  obtain ⟨hgetdc, hszdc, hdc, herrp, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz⟩ := hp
  unfold alloc_small_src allocSmallCore
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  have h1 : (sizeof_jpeg_source_mgr > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false := by decide
  have h2 : (sizeof_small_pool_hdr + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE + ALIGN_SIZE - 1 >
      MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false := by decide
  have h3 : (JPOOL_PERMANENT < 0 || JPOOL_PERMANENT ≥ JPOOL_NUMPOOLS) = false := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, hmem]
  have hgetmem' : C.Space.get h (C.MemRef.mem bmem) = some mems := hgetmem
  rw [Ptr.load_bind h (C.MemRef.mem bmem) 0 mems _ hgetmem' hszmem]
  have hretry := allocSlopRetry_ok (R := C.SrcRef) (.ref (.decomp bdc) 0) allocSrc
    (fun hx => SrcMemPres bdc bmem dcs dc mems rerr hx ∧ hx.allocOk = h.allocOk)
    (fun _ => True)
    (fun p hx => ∃ bsrc srcs, p = .ref (.src bsrc) 0 ∧
      SrcMemPres bdc bmem dcs dc mems rerr hx ∧
      C.Space.get hx (C.SrcRef.src bsrc) = some srcs ∧ 0 < srcs.size)
    (fun h1 ⟨hp1, _⟩ => by
      obtain ⟨hgetdc1, hszdc1, hdc1, herrp1, ⟨errs1, hgeterr1, hszerr1⟩, _⟩ := hp1
      unfold out_of_memory errexit1
      have hdc1_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc1]; exact hdc1.symm
      rw [Ptr.load_bind h1 _ 0 dcs _ hgetdc1 hszdc1, hdc1_0, herrp1]
      rw [Ptr.load_bind h1 rerr 0 errs1 _ hgeterr1 hszerr1]
      have hro_err : C.Space.ro h1 rerr = false := by cases rerr; rfl
      rw [Ptr.store_bind h1 rerr 0 _ errs1 _ hgeterr1 hro_err hszerr1]
      exact ⟨_, rfl, trivial⟩)
    (fun h1 ⟨hp1, hokEq⟩ => by
      by_cases ha : h1.allocOk h1.nalloc = true
      · right
        refine ⟨.ref (.src h1.nextBlk) 0, { h1 with
          srcs := upd h1.srcs h1.nextBlk (some #[default]),
          nextBlk := h1.nextBlk + 1,
          nalloc := h1.nalloc + 1 }, ?_, ?_, ?_⟩
        · simp
        · simp [C.run, allocSrc, ha]
        · refine ⟨h1.nextBlk, #[default], rfl, ⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1, hp1.2.2.2.2.1,
            hp1.2.2.2.2.2.1, hp1.2.2.2.2.2.2.1, hp1.2.2.2.2.2.2.2.1, hp1.2.2.2.2.2.2.2.2⟩,
            by simp [C.Space.get, upd_same], by decide⟩
      · left
        have haF : h1.allocOk h1.nalloc = false := Bool.eq_false_iff.mpr ha
        refine ⟨{ h1 with nalloc := h1.nalloc + 1 }, by simp [C.run, allocSrc, haF], ?_⟩
        exact ⟨⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1, hp1.2.2.2.2.1,
          hp1.2.2.2.2.2.1, hp1.2.2.2.2.2.2.1, hp1.2.2.2.2.2.2.2.1, hp1.2.2.2.2.2.2.2.2⟩, hokEq⟩)
    16
      (if first_pool_slop[JPOOL_PERMANENT.toInt.toNat]! >
          MAX_ALLOC_CHUNK.toInt.toNat.toUInt64 -
            (sizeof_small_pool_hdr + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE + ALIGN_SIZE - 1) then
        MAX_ALLOC_CHUNK.toInt.toNat.toUInt64 -
          (sizeof_small_pool_hdr + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE + ALIGN_SIZE - 1)
      else first_pool_slop[JPOOL_PERMANENT.toInt.toNat]!)
    h ⟨⟨hgetdc, hszdc, hdc, herrp, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz⟩, rfl⟩
  rcases hretry with ⟨h_err, herr_run, _⟩ | ⟨p, h_ok, _hpne, hok_run, bsrc, srcs, hp_eq, hp_ok, hgetsrc, hszsrc⟩
  · left
    refine ⟨h_err, ?_⟩
    rw [C.run_bind, herr_run]
    rfl
  · right
    subst hp_eq
    obtain ⟨hgetdc2, hszdc2, hdc2, _, _, hmem2, hgetmem2, hszmem2, _⟩ := hp_ok
    have hdc2_0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc2]; exact hdc2.symm
    have hro_mem2 : C.Space.ro h_ok (C.MemRef.mem bmem) = false := rfl
    let pid := JPOOL_PERMANENT.toInt.toNat
    let mem2 := {
      mems[0] with
      poolAllocs := mems[0].poolAllocs.set! pid
        { mems[0].poolAllocs[pid]! with srcs := mems[0].poolAllocs[pid]!.srcs.push bsrc }
      totalSpaceAllocated := mems[0].totalSpaceAllocated + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE
    }
    let h_out := C.Space.put h_ok (C.MemRef.mem bmem) (mems.set! 0 mem2)
    refine ⟨bsrc, h_out, srcs, ?_, hgetdc2, hgetsrc, hszsrc⟩
    rw [C.run_bind, hok_run]
    dsimp only
    rw [Ptr.load_bind h_ok _ 0 dcs _ hgetdc2 hszdc2, hdc2_0, hmem2]
    rw [Ptr.load_bind h_ok (C.MemRef.mem bmem) 0 mems _ hgetmem2 hszmem2]
    rw [Ptr.store_bind h_ok (C.MemRef.mem bmem) 0 mem2 mems _ hgetmem2 hro_mem2 hszmem2]
    rfl

theorem jpeg_mem_src_safety : Goal.jpeg_mem_src_safety := by
  intro h cinfo inbuffer insize hvalid
  obtain ⟨rc, dcs, dc, rm, mems, hc, hgetdc, hszdc, hdc, herrValid, hmem, hgetmem, hszmem, hpsz, hsrc⟩ := hvalid
  obtain ⟨rerr, errs, herr, hgeterr, hszerr⟩ := herrValid
  subst hc
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  unfold jpeg_mem_src errexit
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  by_cases hempty : (inbuffer == .null || insize == 0) = true
  · simp only [hempty, ↓reduceIte, herr, bind_assoc_m]
    rw [Ptr.load_bind h rerr 0 errs _ hgeterr hszerr]
    have hro_err : C.Space.ro h rerr = false := by cases rerr; rfl
    rw [Ptr.store_bind h rerr 0 _ errs _ hgeterr hro_err hszerr]
    exact ⟨_, _, rfl⟩
  · have hemptyF : (inbuffer == .null || insize == 0) = false := Bool.eq_false_iff.mpr hempty
    simp only [hemptyF, Bool.false_eq_true, ↓reduceIte]
    rcases hsrc with hsrcNull | ⟨rs, srcs, hsrcRef, hgetsrc, hszsrc⟩
    · simp only [hsrcNull, beq_self_eq_true, ↓reduceIte]
      have hp : SrcMemPres bdc bmem dcs dc mems rerr h :=
        ⟨hgetdc, hszdc, hdc, herr, ⟨errs, hgeterr, hszerr⟩, hmem, hgetmem, hszmem, hpsz⟩
      rcases alloc_small_src_ok h bdc bmem dcs dc mems rerr hp with
        ⟨h_err, herr_run⟩ | ⟨bsrc, h_ok, srcs, hok_run, hgetdc2, hgetsrc2, hszsrc2⟩
      · rw [C.run_bind, herr_run]
        exact ⟨_, _, rfl⟩
      · rw [C.run_bind, hok_run]
        dsimp only
        rw [Ptr.load_bind h_ok _ 0 dcs _ hgetdc2 hszdc, hdc0]
        have hro_dc2 : C.Space.ro h_ok (C.DecompRef.decomp bdc) = false := rfl
        rw [Ptr.store_bind h_ok (C.DecompRef.decomp bdc) 0 _ dcs _ hgetdc2 hro_dc2 hszdc]
        let dc2 := { dc with src := Ptr.ref (C.SrcRef.src bsrc) 0 }
        let h2 := C.Space.put h_ok (C.DecompRef.decomp bdc) (dcs.set! 0 dc2)
        have hgetdc2' : C.Space.get h2 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc2) := by
          simp [h2, C.Space.get, C.Space.put]
        have hszdc2' : 0 < (dcs.set! 0 dc2).size := by rw [Array.size_set!]; exact hszdc
        rw [Ptr.load_bind h2 _ 0 (dcs.set! 0 dc2) _ hgetdc2' hszdc2']
        have hdc2_0 : (dcs.set! 0 dc2)[0] = dc2 := by simp [Array.set!_eq_setIfInBounds]
        rw [hdc2_0]
        have hgetsrc2' : C.Space.get h2 (C.SrcRef.src bsrc) = some srcs := hgetsrc2
        rw [Ptr.load_bind h2 (C.SrcRef.src bsrc) 0 srcs _ hgetsrc2' hszsrc2]
        have hro_src2 : C.Space.ro h2 (C.SrcRef.src bsrc) = false := rfl
        rw [Ptr.store_bind h2 (C.SrcRef.src bsrc) 0 _ srcs _ hgetsrc2' hro_src2 hszsrc2]
        exact ⟨_, _, rfl⟩
    · cases rs with | src bsrc =>
      have hne : (Ptr.ref (C.SrcRef.src bsrc) 0 == Ptr.null) = false := rfl
      simp only [hsrcRef, hne, Bool.false_eq_true, ↓reduceIte]
      have hgetsrc' : C.Space.get h (C.SrcRef.src bsrc) = some srcs := hgetsrc
      rw [Ptr.load_bind h (C.SrcRef.src bsrc) 0 srcs _ hgetsrc' hszsrc]
      by_cases hbadInit : (srcs[0].initSource != .fn "init_mem_source") = true
      · simp only [hbadInit, ↓reduceIte, herr, bind_assoc_m]
        rw [Ptr.load_bind h rerr 0 errs _ hgeterr hszerr]
        have hro_err : C.Space.ro h rerr = false := by cases rerr; rfl
        rw [Ptr.store_bind h rerr 0 _ errs _ hgeterr hro_err hszerr]
        exact ⟨_, _, rfl⟩
      · have hgoodInit : (srcs[0].initSource != .fn "init_mem_source") = false := Bool.eq_false_iff.mpr hbadInit
        simp only [hgoodInit, Bool.false_eq_true, ↓reduceIte]
        rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hsrcRef]
        rw [Ptr.load_bind h (C.SrcRef.src bsrc) 0 srcs _ hgetsrc' hszsrc]
        have hro_src : C.Space.ro h (C.SrcRef.src bsrc) = false := rfl
        rw [Ptr.store_bind h (C.SrcRef.src bsrc) 0 _ srcs _ hgetsrc' hro_src hszsrc]
        exact ⟨_, _, rfl⟩

theorem jpeg_mem_src_functional : Goal.jpeg_mem_src_functional := by
  intro h cinfo inbuffer insize hvalid hfresh hallOk hsrcNull hbufNe hszNe
  obtain ⟨rc, dcs, dc, rm, mems, hc, hgetdc, hszdc, hdc, herrValid, hmem, hgetmem, hszmem, hpsz, _⟩ := hvalid
  subst hc
  cases rc with | decomp bdc =>
  cases rm with | mem bmem =>
  have hdc_src : dc.src = .null := by rw [hdc]; exact hsrcNull (.decomp bdc) dcs rfl hgetdc hszdc
  unfold jpeg_mem_src alloc_small_src allocSmallCore allocSlopRetry
  have hdc0 : dcs[0] = dc := by rw [← getElem!_pos dcs 0 hszdc]; exact hdc.symm
  have hempty : (inbuffer == .null || insize == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro hor
    rcases Bool.or_eq_true _ _ |>.mp hor with hb | hs
    · exact hbufNe (beq_iff_eq.mp hb)
    · exact hszNe (beq_iff_eq.mp hs)
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0]
  simp only [hempty, Bool.false_eq_true, ↓reduceIte, hdc_src, beq_self_eq_true]
  have h1 : (sizeof_jpeg_source_mgr > MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false := by decide
  have h2 : (sizeof_small_pool_hdr + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE + ALIGN_SIZE - 1 >
      MAX_ALLOC_CHUNK.toInt.toNat.toUInt64) = false := by decide
  have h3 : (JPOOL_PERMANENT < 0 || JPOOL_PERMANENT ≥ JPOOL_NUMPOOLS) = false := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, bind_assoc_m]
  rw [Ptr.load_bind h _ 0 dcs _ hgetdc hszdc, hdc0, hmem]
  have hgetmem' : C.Space.get h (C.MemRef.mem bmem) = some mems := hgetmem
  rw [Ptr.load_bind h (C.MemRef.mem bmem) 0 mems _ hgetmem' hszmem]
  have ha : h.allocOk h.nalloc = true := hallOk h.nalloc
  let bsrc := h.nextBlk
  let h1a : C.Heap := { h with srcs := upd h.srcs bsrc (some #[default]), nextBlk := bsrc + 1, nalloc := h.nalloc + 1 }
  have halloc_m : C.run allocSrc h = .ok (Ptr.ref (C.SrcRef.src bsrc) 0, h1a) := by
    simp [C.run, allocSrc, ha, bsrc, h1a]
  have hnotNull : (Ptr.ref (C.SrcRef.src bsrc) 0 != .null) = true := rfl
  rw [C.run_bind, halloc_m]
  simp only [hnotNull, ↓reduceIte, pure_bind_m, bind_assoc_m]
  have hgetdc1a : C.Space.get h1a (C.DecompRef.decomp bdc) = some dcs := hgetdc
  rw [Ptr.load_bind h1a _ 0 dcs _ hgetdc1a hszdc, hdc0, hmem]
  have hgetmem1a : C.Space.get h1a (C.MemRef.mem bmem) = some mems := hgetmem
  rw [Ptr.load_bind h1a (C.MemRef.mem bmem) 0 mems _ hgetmem1a hszmem]
  have hro_mem1a : C.Space.ro h1a (C.MemRef.mem bmem) = false := rfl
  rw [Ptr.store_bind h1a (C.MemRef.mem bmem) 0 _ mems _ hgetmem1a hro_mem1a hszmem]
  let pid := JPOOL_PERMANENT.toInt.toNat
  let mem2 := {
    mems[0] with
    poolAllocs := mems[0].poolAllocs.set! pid { mems[0].poolAllocs[pid]! with srcs := mems[0].poolAllocs[pid]!.srcs.push bsrc }
    totalSpaceAllocated := mems[0].totalSpaceAllocated + round_up_pow2 sizeof_jpeg_source_mgr ALIGN_SIZE
  }
  let h1b := C.Space.put h1a (C.MemRef.mem bmem) (mems.set! 0 mem2)
  have hgetdc1b : C.Space.get h1b (C.DecompRef.decomp bdc) = some dcs := hgetdc1a
  rw [Ptr.load_bind h1b _ 0 dcs _ hgetdc1b hszdc, hdc0]
  have hro_dc1b : C.Space.ro h1b (C.DecompRef.decomp bdc) = false := rfl
  let dc2 := { dc with src := Ptr.ref (C.SrcRef.src bsrc) 0 }
  rw [Ptr.store_bind h1b (C.DecompRef.decomp bdc) 0 dc2 dcs _ hgetdc1b hro_dc1b hszdc]
  let h2 := C.Space.put h1b (C.DecompRef.decomp bdc) (dcs.set! 0 dc2)
  have hgetdc2 : C.Space.get h2 (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc2) := by
    simp [h2, C.Space.get, C.Space.put]
  have hszdc2 : 0 < (dcs.set! 0 dc2).size := by rw [Array.size_set!]; exact hszdc
  rw [Ptr.load_bind h2 _ 0 (dcs.set! 0 dc2) _ hgetdc2 hszdc2]
  have hdc2_0 : (dcs.set! 0 dc2)[0] = dc2 := by simp [Array.set!_eq_setIfInBounds]
  rw [hdc2_0]
  have hgetsrc2 : C.Space.get h2 (C.SrcRef.src bsrc) = some #[default] := by
    simp [h2, h1b, h1a, C.Space.get, C.Space.put, upd_same]
  have hszsrc2 : 0 < (#[default] : Array JpegSourceMgr).size := by decide
  rw [Ptr.load_bind h2 (C.SrcRef.src bsrc) 0 #[default] _ hgetsrc2 hszsrc2]
  have hro_src2 : C.Space.ro h2 (C.SrcRef.src bsrc) = false := rfl
  let srcFin : JpegSourceMgr := {
    initSource := .fn "init_mem_source"
    fillInputBuffer := .fn "fill_mem_input_buffer"
    skipInputData := .fn "skip_input_data"
    resyncToRestart := .fn "jpeg_resync_to_restart"
    termSource := .fn "term_source"
    bytesInBuffer := insize
    nextInputByte := inbuffer
  }
  let hfin := C.Space.put h2 (C.SrcRef.src bsrc) (#[default].set! 0 srcFin)
  rw [Ptr.store_bind h2 (C.SrcRef.src bsrc) 0 srcFin #[default] _ hgetsrc2 hro_src2 hszsrc2]
  have hgetdc_fin : C.Space.get hfin (C.DecompRef.decomp bdc) = some (dcs.set! 0 dc2) := hgetdc2
  have hgetsrc_fin : C.Space.get hfin (C.SrcRef.src bsrc) = some (#[default].set! 0 srcFin) := by
    simp [hfin, C.Space.get, C.Space.put]
  have hdc2_bang : (dcs.set! 0 dc2)[0]! = dc2 := by
    rw [getElem!_pos _ 0 hszdc2]; simp [Array.set!_eq_setIfInBounds]
  refine ⟨hfin, .decomp bdc, dcs.set! 0 dc2, .src bsrc, #[default].set! 0 srcFin,
    rfl, rfl, hgetdc_fin, hszdc2, ?_, hgetsrc_fin, (by simp), rfl, rfl, rfl, rfl⟩
  rw [hdc2_bang]

end MozjpegF.Proof.Jdatasrc
