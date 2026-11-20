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

/-- The offset of the pointer `zng_alloc_aligned(size, 64)` returns into a block at address `a`. -/
def alOff (a : UInt64) : Nat :=
  let d : UInt64 := ((64 : UInt32).toUInt64 - (a &&& ((64 : UInt32) - 1).toUInt64)) &&& ((64 : UInt32) - 1).toUInt64
  if d < 8 then d.toNat + 64 else d.toNat

theorem alOff_bounds (a : UInt64) : 8 ≤ alOff a ∧ alOff a < 72 := by
  unfold alOff
  have hm : ((64 : UInt32) - 1).toUInt64 = 63 := by decide
  rw [hm]
  generalize ((64 : UInt32).toUInt64 - (a &&& 63)) = x
  have : (x &&& 63).toNat < 64 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  split
  · omega
  · next hn =>
    have : ¬ (x &&& 63).toNat < 8 := fun e => hn (UInt64.lt_iff_toNat_lt.mpr (by simpa using e))
    omega

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
  obtain ⟨hlo, hhi⟩ := alOff_bounds (h.baseAddr (.heap h.nextBlk))
  unfold alOff at hlo hhi
  simp only [ZlibNg.Zutil.zng_alloc_aligned, bind_app, allocB, hok, ite_true, hsz]
  simp only [ZlibNg.Zutil.ALIGN_DIFF, bind_app, addrOf, pure_app]
  generalize hd : ((64 : UInt32).toUInt64 - ((h.baseAddr (BRef.heap h.nextBlk) + UInt64.ofNat 0) &&&
    ((64 : UInt32) - 1).toUInt64)) &&& ((64 : UInt32) - 1).toUInt64 = d
  have hd' : ((64 : UInt32).toUInt64 - (h.baseAddr (BRef.heap h.nextBlk) &&&
      ((64 : UInt32) - 1).toUInt64)) &&& ((64 : UInt32) - 1).toUInt64 = d := by simpa using hd
  rw [hd'] at hlo hhi
  have hd64 : d.toNat < 64 := by
    rw [← hd', UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  simp [alOff, hd', alH, Ptr.add, Space.get, Heap.getBytes, upd_same, storePtrSlot]
  by_cases h8 : d < 8
  · have h8' : d.toNat < 8 := UInt64.lt_iff_toNat_lt.mp h8
    simp [h8, Ptr.add, Space.get, Heap.getBytes, storePtrSlot]
    refine ⟨by omega, ?_⟩
    simp [show (d.toNat : Int) + 64 + -8 = ((d.toNat + 64 - 8 : Nat) : Int) by omega]
    constructor <;> (try omega)
  · have h8' : ¬ d.toNat < 8 := fun e => h8 (UInt64.lt_iff_toNat_lt.mpr e)
    simp [h8, Ptr.add, Space.get, Heap.getBytes, storePtrSlot]
    constructor <;> (try omega)

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
  have hadd : Ptr.add (.ref (.heap h.nextBlk) o : BPtr) (Int.ofNat s.want.toNat) H =
      .ok (.ref (.heap h.nextBlk) (o + s.want.toNat), H) := by
    have := Inftrees.add_ok (r := BRef.heap h.nextBlk) (off := o) (k := Int.ofNat s.want.toNat) (h := H) hcA
      (by simp; omega) (by omega) (by simp; omega)
    rw [this]; congr 3; omega
  have hm2 : ¬ (s.want * 2 = 0) := by
    intro e; have := congrArg UInt32.toNat e; rw [UInt32.toNat_mul] at this; simp at this; omega
  simp [gz_buffer_alloc, rdG_app' hs, hr, GZ_READ, GZ_WRITE, hal, wrG_app hsA, ldGz_upd hdA, wrG_upd hdA,
    rdG_upd hdA, Ival.get, liftM, monadLift, MonadLift.monadLift, hadd, hm2, InflateInv.upd_upd, baSt]

end ZlibNgF.Proof.GzMode
