import ZlibNgF.Proof.«gzwrite.c.zero»

/-!
# `gz_write` (`ZlibNgF`)

Helpers: a caller's buffer stays readable and outside the file across a step of the file (`callerBuf_step`);
`memcpy` from a caller's buffer into the buffer block of the file changes only that block (`memcpy_hbuf`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- A caller's buffer stays readable and outside the file's blocks across a step of the file. -/
theorem callerBuf_step {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) (hfr : FreshBlocks h)
    {p : BPtr} {n : Nat} (hr : ReadSlice h p n) (ho : OutsideGz w h (some b) p) :
    ReadSlice H p n ∧ OutsideGz W H (some b) p := by
  obtain ⟨r, off, d, ep, hd, hle⟩ := hr
  obtain ⟨⟨⟨fr, fd⟩, fc, -⟩, own, -⟩ := g
  have hget : Space.get H r = some d := by
    cases r with
    | heap c =>
      have hcl : c < h.nextBlk := live_lt hfr ⟨d, hd⟩
      have hno : c ∉ GzOwned w h (some b) := fun m => ho c m off ep
      have e2 : ({ H with consts := h.consts } : Heap).bytes c = h.bytes c := frame_bytes_eq fr hcl hno
      exact e2.trans hd
    | const k => exact fc k d hd
    | str k => exact hd
  refine ⟨⟨r, off, d, ep, hget, hle⟩, fun c hc off' e => ?_⟩
  rw [ep] at e; cases e
  by_cases hlt : c < h.nextBlk
  · exact ho c (own c hc hlt) off ep
  · exact hlt (live_lt hfr ⟨d, hd⟩)

/-- `memcpy` from another object into heap block `c`: only the range of block `c` changes. -/
theorem memcpy_hbuf {H : Heap} {c od : Nat} {rs : BRef} {os n : Nat} {a src : Array UInt8}
    (ha : H.bytes c = some a) (hs : Space.get H rs = some src) (hne : rs ≠ .heap c) (h1 : od + n ≤ a.size)
    (h2 : os + n ≤ src.size) :
    ∃ H', Ptr.memcpy (Ptr.ref (BRef.heap c) od : BPtr) (Ptr.ref rs os) n H = .ok ((), H') ∧ HBuf H H' c od (od + n) := by
  refine ⟨_, ZlibNgF.Proof.InflateDict.memcpy_heap ha hs hne h1 h2, ?_⟩
  refine ⟨upd H.bytes c (some (ZlibNgF.Proof.InflateDict.copyFold src od os (List.range' 0 n) a)), rfl, ?_, ?_, ?_⟩
  · intro c' hc'; exact upd_ne _ _ _ _ hc'
  · intro e; rw [ha] at e; cases e
  intro a' ha'
  rw [ha] at ha'; cases ha'
  exact ⟨_, upd_same _ _ _, ZlibNgF.Proof.InflateDict.copyFold_size _ _ _ _ _, fun j hj =>
    ZlibNgF.Proof.InflateDict.copyFold_get _ _ _ _ _ j (fun i hi => ChunkMem.mem_range'_bound hi hj)⟩

/-! ## The parts of `gz_write` (copied from the translation) -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the buffered path after `next_in` is set. -/
def wbMain (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  let e ← lm ((← lm (rdZ strm (·.next_in))).add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
  let d ← lm (Ptr.diff e (← (← ldGz state).«in».get))
  let hv : UInt32 := d.toUInt64.toUInt32
  let mut copy : UInt32 := (← rdG state (·.size)) - hv
  if copy.toUInt64 > s.len then
    copy := s.len.toUInt32
  lm (Ptr.memcpy (← lm ((← (← ldGz state).«in».get).add (Int.ofNat hv.toNat))) s.buf copy.toNat)
  lm (wrZ strm fun z => { z with avail_in := z.avail_in + copy })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + copy.toNat))
  wrG state fun st => { st with pos := np }
  let buf ← lm (s.buf.add (Int.ofNat copy.toNat))
  let len := s.len - copy.toUInt64
  if len != 0 then
    if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
      return { s with buf := buf, len := len, ctl := .ret }
  return { s with buf := buf, len := len }

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the buffered path. -/
def wbBody (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  wbMain state strm s

/-- The condition of both loops of `gz_write`. -/
def wCond (s : WriteLoop) : G (Bool × WriteLoop) := do
  if s.ctl != .go then return (false, s)
  return (s.len != 0, s)

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the direct path. -/
def wdBody (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  let mut n : UInt32 := 0xFFFFFFFF
  if n.toUInt64 > s.len then
    n := s.len.toUInt32
  lm (wrZ strm fun z => { z with avail_in := n })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
    return { s with ctl := .ret }
  return { s with len := s.len - n.toUInt64 }

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gz_write` after the buffers are made and the pending seek is done. -/
def wMid (state : GzPtr) (buf : BPtr) (len put : UInt64) : G UInt64 := do
  let room ← lm (chkI64 (GZ_OFF_MAX.toInt - (← rdG state (·.pos)).toInt))
  if len > room.toUInt64 then
    gz_error state ZlibNg.Inflate.Z_DATA_ERROR (← (gzLit "write position does not fit in z_off64_t"))
    return 0
  let strm ← strmOf state
  if len < (← rdG state (·.size)).toUInt64 then
    let lp ← gdoWhile (wbBody state strm) wCond ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
  else
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
        return 0
    lm (wrZ strm fun z => { z with next_in := buf })
    let lp ← gdoWhile (wdBody state strm) wCond ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  return put

theorem gz_write_eq (state : GzPtr) (buf : BPtr) (len : UInt64) : gz_write state buf len = (do
    if len == 0 then
      return 0
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return 0
    if (← rdG state (·.skip)) != 0 then
      if (← gz_zero state) == -1 then
        return 0
    wMid state buf len len) := rfl

/-! ## Pointer steps -/

theorem padd_ok {h : Heap} {r : BRef} {off : Nat} {a : Array UInt8} (hg : Space.get h r = some a) (k : Nat)
    (hk : off + k ≤ a.size) : Ptr.add (Ptr.ref r off : BPtr) (Int.ofNat k) h = .ok (Ptr.ref r (off + k), h) := by
  have e : ((off : Int) + (k : Int)).toNat = off + k := by omega
  simp only [Ptr.add, hg, Int.ofNat_eq_natCast]
  split
  · rw [e]
  · next hc => exact absurd ⟨by omega, by omega, by omega⟩ hc

theorem pdiff_ok {h : Heap} {c o1 o2 : Nat} {a : Array UInt8} (ha : h.bytes c = some a) (h1 : o1 ≤ a.size)
    (h2 : o2 ≤ o1) (h3 : o1 < 2 ^ 62) :
    Ptr.diff (Ptr.ref (BRef.heap c) o1 : BPtr) (Ptr.ref (BRef.heap c) o2) h = .ok (Int64.ofInt ((o1 : Int) - o2), h) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  simp only [Ptr.diff, hg]
  split
  · split
    · split
      · rfl
      · next hc => exact absurd ⟨by omega, by omega⟩ hc
    · next hc => exact absurd ⟨h1, by omega⟩ hc
  · next hc => exact absurd trivial hc

theorem diff_u32 (k : Nat) (hk : k < 2 ^ 31) : (Int64.ofInt (k : Int)).toUInt64.toUInt32.toNat = k := by
  have e : (Int64.ofInt (k : Int)).toInt = k := Int64.toInt_ofInt_of_le (by omega) (by omega)
  rw [UInt64.toNat_toUInt32, i64_toNat_toUInt64 _ (by omega), e]
  omega

end ZlibNgF.Proof.GzWrite
