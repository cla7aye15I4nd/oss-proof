import ZlibNgF.Proof.«gzread.c.load»
import ZlibNgF.Proof.«gzread.c.close»

/-!
# `gz_buffer_alloc` and `gz_read_init` on a read handle (`ZlibNgF`)

`zng_alloc_aligned(3 * want, 64)`: one fresh block of `8 + 3 * want + 64` bytes, the returned pointer `off` bytes into
it (`8 ≤ off < 72`, aligned to 64), and the block's own pointer saved in the 8 bytes before it.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## `zng_alloc_aligned` -/

/-- `ALIGN_DIFF(ptr, 64)` of a block at address `a`. -/
def alD (a : UInt64) : UInt64 :=
  ((64 : UInt32).toUInt64 - ((a + UInt64.ofNat 0) &&& ((64 : UInt32) - 1).toUInt64)) &&& ((64 : UInt32) - 1).toUInt64

/-- The offset of the pointer `zng_alloc_aligned(size, 64)` returns into a block at address `a`. -/
def alOff (a : UInt64) : Nat := if alD a < 8 then (alD a).toNat + (64 : UInt32).toNat else (alD a).toNat

theorem alD_lt (a : UInt64) : (alD a).toNat < 64 := by
  unfold alD
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem alOff_bounds (a : UInt64) : 8 ≤ alOff a ∧ alOff a < 72 := by
  have h1 := alD_lt a
  have h64 : (64 : UInt32).toNat = 64 := rfl
  have hq : alD a < 8 ↔ (alD a).toNat < 8 := UInt64.lt_iff_toNat_lt
  by_cases hd : alD a < 8
  · have e : alOff a = (alD a).toNat + 64 := by simp only [alOff, hd, ite_true]; rfl
    rw [e]; have := hq.mp hd; omega
  · have e : alOff a = (alD a).toNat := by simp only [alOff, hd, ite_false]
    rw [e]; have := mt hq.mpr hd; omega

/-- The heap after a successful `zng_alloc_aligned(size, 64)`. -/
def alH (h : Heap) (n : Nat) (off : Nat) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
           savedPtrs := upd h.savedPtrs h.nextBlk (some (off - 8, .ref (.heap h.nextBlk) 0)),
           nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }

theorem alloc_aligned_ok {h : Heap} (size : UInt32) (hw : 8 + size.toNat + 64 < 2 ^ 32)
    (hok : h.allocOk h.nalloc = true) :
    ZlibNg.Zutil.zng_alloc_aligned size 64 h =
      .ok (.ref (.heap h.nextBlk) (alOff (h.baseAddr (.heap h.nextBlk))),
        alH h (8 + size.toNat + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) := by
  have hsz : ((8 : UInt64) + size.toUInt64 + (64 : UInt32).toUInt64).toUInt32.toNat = 8 + size.toNat + 64 := by
    have h1 : ((8 : UInt64) + size.toUInt64 + (64 : UInt32).toUInt64).toNat = 8 + size.toNat + 64 := by
      simp [UInt64.toNat_add]; omega
    rw [UInt64.toNat_toUInt32, h1]; omega
  let A : Array UInt8 := Array.ofFn (n := 8 + size.toNat + 64) fun i => Junk.of (h.garbage h.nalloc i.val)
  have hA : A.size = 8 + size.toNat + 64 := Array.size_ofFn
  obtain ⟨H1, hH1⟩ : ∃ H1 : Heap, H1 = { h with bytes := upd h.bytes h.nextBlk (some A), savedPtrs := upd h.savedPtrs h.nextBlk none, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 } := ⟨_, rfl⟩
  have e1 : allocB ((8 : UInt64) + size.toUInt64 + (64 : UInt32).toUInt64).toUInt32.toNat h =
      .ok (.ref (.heap h.nextBlk) 0, H1) := by
    rw [hsz, hH1]; simp only [allocB, hok, ite_true]; rfl
  have hg1 : Space.get H1 (BRef.heap h.nextBlk) = some A := by rw [hH1]; simp [Space.get, Heap.getBytes, upd_same]
  have hb1 : H1.bytes h.nextBlk = some A := by rw [hH1]; simp [upd_same]
  generalize hD : alD (h.baseAddr (.heap h.nextBlk)) = d
  have hd64 : d.toNat < 64 := by rw [← hD]; exact alD_lt _
  have e2 : ZlibNg.Zutil.ALIGN_DIFF (.ref (.heap h.nextBlk) 0) 64 H1 = .ok (d, H1) := by
    rw [← hD, hH1]; rfl
  have e3 : Ptr.add (.ref (.heap h.nextBlk) 0 : BPtr) (Int.ofNat d.toNat) H1 = .ok (.ref (.heap h.nextBlk) d.toNat, H1) := by
    have hk : Int.ofNat d.toNat = (d.toNat : Int) := rfl
    rw [hk, Inftrees.add_ok hg1 (by omega) (by omega) (by rw [hA]; omega)]; congr 3; try omega
  have h64 : (64 : UInt32).toNat = 64 := rfl
  unfold ZlibNg.Zutil.zng_alloc_aligned
  simp only [bind_app, e1, e2, e3]
  have hn : ((Ptr.ref (BRef.heap h.nextBlk) 0 : BPtr) == .null) = false := rfl
  simp only [hn, Bool.false_eq_true, ite_false, bind_app, e2, e3]
  by_cases h8 : d < 8
  · have h8' : d.toNat < 8 := UInt64.lt_iff_toNat_lt.mp h8
    have e4 : Ptr.add (.ref (.heap h.nextBlk) d.toNat : BPtr) (Int.ofNat (64 : UInt32).toNat) H1 =
        .ok (.ref (.heap h.nextBlk) (d.toNat + 64), H1) := by
      have h64' : Int.ofNat (64 : UInt32).toNat = 64 := rfl
      rw [h64', Inftrees.add_ok hg1 (by omega) (by omega) (by rw [hA]; omega)]; congr 3; try omega
    have e5 : Ptr.add (.ref (.heap h.nextBlk) (d.toNat + 64) : BPtr) (-8) H1 = .ok (.ref (.heap h.nextBlk) (d.toNat + 56), H1) := by
      rw [Inftrees.add_ok hg1 (by omega) (by omega) (by rw [hA]; omega)]; congr 3; try omega
    simp only [h8, ite_true, bind_app, e4, e5, storePtrSlot, hb1, show d.toNat + 56 + 8 ≤ A.size by omega,
      ite_true, pure_app]
    have hO : alOff (h.baseAddr (.heap h.nextBlk)) = d.toNat + 64 := by
      unfold alOff; rw [hD]; simp only [h8, ite_true, h64]
    rw [hO]
    rw [hH1]; simp only [alH, InflateInv.upd_upd, A, show d.toNat + 64 - 8 = d.toNat + 56 by omega]
  · have h8' : ¬ d.toNat < 8 := fun e => h8 (UInt64.lt_iff_toNat_lt.mpr e)
    have e5 : Ptr.add (.ref (.heap h.nextBlk) d.toNat : BPtr) (-8) H1 = .ok (.ref (.heap h.nextBlk) (d.toNat - 8), H1) := by
      rw [Inftrees.add_ok hg1 (by omega) (by omega) (by rw [hA]; omega)]; congr 3; try omega
    simp only [h8, ite_false, bind_app, pure_app, e5, storePtrSlot, hb1,
      show d.toNat - 8 + 8 ≤ A.size by omega, ite_true]
    have hO : alOff (h.baseAddr (.heap h.nextBlk)) = d.toNat := by
      unfold alOff; rw [hD]; simp only [h8, ite_false]
    rw [hO]
    rw [hH1]; simp only [alH, InflateInv.upd_upd, A]

/-! ## `inflateInit2(strm, 31)` on the stream of a read handle -/

section Init
open ZlibNgF.Proof.InflateAlloc ZlibNgF.Proof.InflateReset ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Live setZS upd_upd)

theorem reset2_31 {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    ∃ H, inflateReset2 (some i) 31 h = .ok (Z_OK, H) := by
  have h1 : ¬ (31 : Int32) < 0 := by decide
  have h2 : (31 : Int32) < 48 := by decide
  have h3 : ¬ (((31 : Int32) &&& MAX_WBITS) != 0 && (decide (((31 : Int32) &&& MAX_WBITS) < MIN_WBITS) ||
      decide (((31 : Int32) &&& MAX_WBITS) > MAX_WBITS))) = true := by decide
  simp only [inflateReset2, bind_app, L.check, L.stateOf, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, wrap_ok,
    pure_app]
  exact ⟨_, reset2_tail L _ _⟩

/-- `inflateInit2(strm, 31)` when the allocation fails: `Z_MEM_ERROR`, the stream gets the default allocator and
nothing else changes. -/
theorem init2_31_fail {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hok : h.allocOk h.nalloc = false) :
    inflateInit2 (some i) 31 h =
      .ok (Z_MEM_ERROR, { h with streams := upd h.streams i (some (initZ z)), nalloc := h.nalloc + 1 }) := by
  rw [init2_pre hz hza hzf 31]
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  simp only [bind_app, alloc_fail hza0 hok]; rfl

/-- `inflateInit2(strm, 31)` when the allocation succeeds returns `Z_OK`. -/
theorem init2_31_ok {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z)
    (hza : z.zalloc = .null ∨ z.zalloc = .zcalloc) (hzf : z.zfree = .null ∨ z.zfree = .zcfree)
    (hfs : h.istates h.nextBlk = none) (hfa : h.iallocs h.nextBlk = none) (hok : h.allocOk h.nalloc = true) :
    ∃ h', inflateInit2 (some i) 31 h = .ok (Z_OK, h') := by
  obtain ⟨r, h', e, -⟩ := init2_ok hz hza hzf hfs hfa 31
  refine ⟨h', ?_⟩
  rw [e]
  suffices r = Z_OK by rw [this]
  rw [init2_pre hz hza hzf 31] at e
  have hza0 : (({ h with streams := upd h.streams i (some (initZ z)) } : Heap).streams i).map ZStream.zalloc =
      some .zcalloc := by simp [initZ]
  simp only [bind_app, alloc_ok hza0 hfs hfa hok] at e
  let H0 : Heap := { h with streams := upd h.streams i (some (initZ z)) }
  let b := h.nextBlk
  let p := (PADSZ (h.baseAddr (.heap b)) 64).toNat
  let z2 : ZStream := { initZ z with state := some b }
  let st2 := initS (h.garbage (2 ^ 40 + b)) i b p
  let H2 := setZS (allocHeap H0 .zcfree) i z2 b st2
  have L2 : Live H2 i z2 b st2 := by
    refine ⟨by simp [H2, setZS], rfl, ⟨allocBytes H0, by simp [H2, setZS, H0, b]⟩, by simp [H2, setZS],
      by simp [z2, initZ], by simp [z2, initZ], ⟨b, rfl⟩, rfl, by show HEAD ≤ HEAD; decide, by show HEAD ≤ SYNC; decide⟩
  obtain ⟨H, eH⟩ := reset2_31 L2
  simp [-Nat.reducePow, H2, setZS, z2, st2, initS, H0, b, p, upd_upd, initZ] at eH
  simp [-Nat.reducePow, ldAllocs, Heap.iallocsOf, Ival.get, wrS, ldState, stState, Heap.istate, wrZ, ldStream,
    stStream, upd_upd, initZ, eH, Z_OK] at e
  exact e.1.symm

end Init

/-! ## `gz_buffer_alloc` on a read handle -/

/-- The state after a successful `gz_buffer_alloc` into the block `c` at offset `o`. -/
def baSt (s : GzState) (c o : Nat) : GzState :=
  { s with buffers := .val (.ref (.heap c) o), «in» := .val (.ref (.heap c) o),
           out := .val (.ref (.heap c) (o + s.want.toNat)), size := s.want }

theorem want3 {s : GzState} (hw : s.want.toNat ≤ 2 ^ 30) : (s.want + s.want * 2).toNat = 3 * s.want.toNat := by
  rw [UInt32.toNat_add, UInt32.toNat_mul]; simp; omega

theorem gz_buffer_alloc_ok {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hr : s.mode = GZ_READ) (hlo : 8 ≤ s.want.toNat) (hw : s.want.toNat ≤ 2 ^ 30)
    (hfr : h.bytes h.nextBlk = none) (hok : h.allocOk h.nalloc = true) :
    gz_buffer_alloc (some b) w h =
      .ok ((0, { w with gzs := upd w.gzs b (some (baSt s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk))))) }),
        alH h (8 + 3 * s.want.toNat + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) := by
  obtain ⟨d, hd⟩ := gz_live hs
  have hbn : b ≠ h.nextBlk := fun e => by rw [e, hfr] at hd; cases hd
  have h3 := want3 hw
  have hal := alloc_aligned_ok (h := h) (s.want + s.want * 2) (by rw [h3]; omega) hok
  rw [h3] at hal
  generalize hO : alOff (h.baseAddr (.heap h.nextBlk)) = o at hal ⊢
  have ho := alOff_bounds (h.baseAddr (.heap h.nextBlk))
  rw [hO] at ho
  generalize hH : alH h (8 + 3 * s.want.toNat + 64) o = H at hal ⊢
  have hdA : H.bytes b = some d := by rw [← hH]; simp [alH, upd_ne _ _ _ _ hbn, hd]
  have hcA : H.bytes h.nextBlk = some (Array.ofFn (n := 8 + 3 * s.want.toNat + 64)
      fun i => Junk.of (h.garbage h.nalloc i.val)) := by rw [← hH]; simp [alH]
  have hsA : w.gz H b = some s := by
    unfold World.gz at hs ⊢; rw [hdA]; rw [hd] at hs; exact hs
  have hadd : Ptr.add (.ref (.heap h.nextBlk) o : BPtr) (s.want.toNat : Int) H =
      .ok (.ref (.heap h.nextBlk) (o + s.want.toNat), H) := by
    have hg : Space.get H (BRef.heap h.nextBlk) = some (Array.ofFn (n := 8 + 3 * s.want.toNat + 64)
        fun i => Junk.of (h.garbage h.nalloc i.val)) := hcA
    have := Inftrees.add_ok (r := BRef.heap h.nextBlk) (off := o) (k := (s.want.toNat : Int)) (h := H) hg
      (by rw [Array.size_ofFn]; omega) (by omega) (by rw [Array.size_ofFn]; omega)
    rw [this]; congr 3; try omega
  have hm2 : ¬ (s.want * 2 = 0) := by
    intro e; have := congrArg UInt32.toNat e; rw [UInt32.toNat_mul] at this; simp at this; omega
  simp [gz_buffer_alloc, rdG_app' hs, hr, GZ_READ, GZ_WRITE, hal, wrG_app hsA, ldGz_upd hdA, wrG_upd hdA,
    rdG_upd hdA, Ival.get, liftM, monadLift, MonadLift.monadLift, hadd, hm2, InflateInv.upd_upd, baSt]

end ZlibNgF.Proof.GzMode
