import ZlibNgF.Spec.Safety.Inflate

/-!
# Structural invariant of an inflate stream (`ZlibNgF`)

`InflateInv h s`: the stream `s` holds a live state made by `inflateInit2_` with the default allocator, in the carve
layout of `alloc_inflate`, with its fields in range. Proofs use it only through the interface lemmas at the end of
this file, so that a clause can be added or changed without touching the per-function proofs.

The plan (see `Proof/public-inflate-*.lean`): for each public function, "invariant in → no fault, frame, invariant
out"; `InflateReachable h s → InflateInv h s` then follows by induction over `InflateReachable`, one constructor case
per function, and the registered goals follow from it.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateInv
open C ZlibNgF.Spec ZlibNg.Inflate

/-- A `code` pointer of the state: into the state's own `codes` (within `ENOUGH`), or the start of a fixed table. -/
def CodeTarget (b : Nat) (p : CodePtr) : Prop :=
  (∃ o, p = .ref (.codes b) o ∧ o ≤ ENOUGH) ∨ p = .ref .lenfix 0 ∨ p = .ref .distfix 0

/-- The fields of a state record that the invariant constrains. A store that changes only other fields leaves
`view` unchanged by definition, so the invariant carries over without a proof per field. -/
structure View where
  strm : Ival StreamPtr
  alloc_bufs : Ival AllocsPtr
  window : Ival BPtr
  wbufsize : UInt32
  mode : UInt32
  wbits : UInt32
  wsize : UInt32
  whave : UInt32
  wnext : UInt32
  bits : UInt32
  codes_size : Nat
  lens_size : Nat
  work_size : Nat
  lencode : Ival CodePtr
  distcode : Ival CodePtr
  next : Ival CodePtr
  ncode : UInt32
  nlen : UInt32
  ndist : UInt32
  have_ : UInt32
  head : Ival HeaderPtr

/-- The constrained fields of `st`. -/
def view (st : InflateState) : View :=
  ⟨st.strm, st.alloc_bufs, st.window, st.wbufsize, st.mode, st.wbits, st.wsize, st.whave, st.wnext, st.bits,
    st.codes.size, st.lens.size, st.work.size, st.lencode, st.distcode, st.next, st.ncode, st.nlen, st.ndist,
    st.«have», st.head⟩

/-- The clauses on the stream record `z`, the constrained state fields `st` and the allocation record `al` of block `b`. -/
structure Core (h : Heap) (s : StreamPtr) (z : ZStream) (b : Nat) (st : View) (al : InflateAllocs) :
    Prop where
  zalloc : z.zalloc = .zcalloc
  zfree : z.zfree = .zcfree
  strm : st.strm = .val s
  alloc_bufs : st.alloc_bufs = .val (some b)
  al_state : al.state = .val (some b)
  al_zfree : al.zfree = .val .zcfree
  al_buf : al.buf_start = .val (.ref (.heap b) 0)
  window : ∃ (woff : Nat) (data : Array UInt8), st.window = .val (.ref (.heap b) woff) ∧ al.window = st.window ∧
    h.bytes b = some data ∧ woff + st.wbufsize.toNat ≤ data.size
  wbufsize : st.wbufsize = ((1 : UInt32) <<< 15) + 64
  mode_lo : HEAD ≤ st.mode
  mode_hi : st.mode ≤ SYNC
  wbits : st.wbits ≤ 15
  wsize : st.wsize = 0 ∨ st.wsize = (1 : UInt32) <<< st.wbits
  whave : st.whave ≤ st.wsize
  wnext : st.wnext = 0 ∨ st.wnext < st.wsize
  bits : st.bits ≤ 64
  codes_size : st.codes_size = ENOUGH
  lens_size : st.lens_size = 320
  work_size : st.work_size = 288
  lencode : ∃ p, st.lencode = .val p ∧ CodeTarget b p
  distcode : ∃ p, st.distcode = .val p ∧ CodeTarget b p
  next : ∃ o, st.next = .val (.ref (.codes b) o) ∧ o ≤ ENOUGH
  ncode : st.ncode ≤ 19
  nlen : st.nlen ≤ 288
  ndist : st.ndist ≤ 32
  have_ : st.have_ ≤ 320
  head : st.head = .val none ∨ ∃ k g, st.head = .val (some k) ∧ h.gzheaders k = some g

/-- The clauses read the heap only through its byte blocks and its `gz_header` records. -/
theorem Core.of_heap {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : View} {al : InflateAllocs}
    (hb : h'.bytes = h.bytes) (hg : h'.gzheaders = h.gzheaders) (c : Core h s z b v al) : Core h' s z b v al := by
  refine ⟨c.zalloc, c.zfree, c.strm, c.alloc_bufs, c.al_state, c.al_zfree, c.al_buf, ?_, c.wbufsize, c.mode_lo,
    c.mode_hi, c.wbits, c.wsize, c.whave, c.wnext, c.bits, c.codes_size, c.lens_size, c.work_size, c.lencode,
    c.distcode, c.next, c.ncode, c.nlen, c.ndist, c.have_, ?_⟩
  · rw [hb]; exact c.window
  · rw [hg]; exact c.head

/-- The structural invariant of the inflate stream `s` in `h`. -/
def Inv (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.istate b = some st ∧
    h.iallocsOf b = some al ∧ Core h s z b (view st) al

/-! ## Interface lemmas -/

/-- `inflateStateCheck` of `Z_NULL` accepts nothing. -/
theorem stateCheck_none (h : Heap) : C.run (inflateStateCheck none) h = .ok (true, h) := rfl

/-- `ldStream` of a live stream. -/
theorem ldStream_app {h : Heap} {i : Nat} {z : ZStream} (hi : h.streams i = some z) :
    ldStream (some i) h = .ok (z, h) := by simp [ldStream, hi]

/-- `ldState` of a live state. -/
theorem ldState_app {h : Heap} {b : Nat} {st : InflateState} (hb : h.istate b = some st) :
    ldState (some b) h = .ok (st, h) := by simp [ldState, hb]

/-- `inflateStateCheck` of a stream with no state. -/
theorem stateCheck_closed (h : Heap) (s : StreamPtr) (z : ZStream) (hz : StreamAt h s z) (hs : z.state = none) :
    C.run (inflateStateCheck s) h = .ok (true, h) := by
  obtain ⟨i, rfl, hi⟩ := hz
  by_cases ha : z.zalloc = .null
  · simp [C.run, inflateStateCheck, bind_app, ldStream_app hi, ha]
  · by_cases hf : z.zfree = .null <;> simp [C.run, inflateStateCheck, bind_app, ldStream_app hi, hs, ha, hf]

/-- The stream record, state and allocation record of an invariant stream. -/
theorem parts {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.istate b = some st ∧
      h.iallocsOf b = some al ∧ Core h s z b (view st) al := hv

/-- `inflateStateCheck` of an invariant stream passes, without changing the heap. -/
theorem stateCheck {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    C.run (inflateStateCheck s) h = .ok (false, h) := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, c⟩ := hv
  have lo : HEAD ≤ st.mode := c.mode_lo
  have hi : st.mode ≤ SYNC := c.mode_hi
  have ca : st.alloc_bufs = .val (some b) := c.alloc_bufs
  have cs : st.strm = .val (some i) := c.strm
  have hm1 : ¬ st.mode < HEAD := fun hlt => absurd lo (UInt32.not_le.mpr hlt)
  have hm2 : ¬ st.mode > SYNC := fun hlt => absurd hi (UInt32.not_le.mpr hlt)
  simp [C.run, inflateStateCheck, bind_app, ldStream_app hz, ldState_app hst, hb, c.zalloc, c.zfree,
    ca, cs, Ival.get, hm1, hm2]

/-- `stateOf` of an invariant stream. -/
theorem stateOf {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ b st, C.run (ZlibNg.Inflate.stateOf s) h = .ok (some b, h) ∧ h.istate b = some st ∧
      C.run (ldState (some b)) h = .ok (st, h) := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, _, _⟩ := hv
  refine ⟨b, st, ?_, hst, ?_⟩
  · simp [ZlibNg.Inflate.stateOf, rdZ, C.run, bind_app, ldStream_app hz, hb]
  · simp [C.run, ldState_app hst]

/-- `wrS` of a function that keeps every clause preserves the invariant; it changes only the state record. -/
theorem wrS {h : Heap} {s : StreamPtr} (hv : Inv h s) {b : Nat} {st : InflateState} (f : InflateState → InflateState)
    (hb : ∃ z, StreamAt h s z ∧ z.state = some b) (hst : h.istate b = some st)
    (hkeep : ∀ (al : InflateAllocs) (z : ZStream), Core h s z b (view st) al → Core h s z b (view (f st)) al) :
    C.run (ZlibNg.Inflate.wrS (some b) f) h = .ok ((), { h with istates := upd h.istates b (some (f st)) }) ∧
      Inv { h with istates := upd h.istates b (some (f st)) } s := by
  obtain ⟨i, z, b0, st0, al, rfl, hz, hb0, hst0, hal, c⟩ := hv
  obtain ⟨z1, ⟨i1, hi1, hz1⟩, hb1⟩ := hb
  obtain rfl : i = i1 := Option.some.inj hi1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b0 = b := Option.some.inj (hb0.symm.trans hb1)
  obtain rfl : st0 = st := Option.some.inj (hst0.symm.trans hst)
  have hbytes : ∃ d, h.bytes b0 = some d := by
    unfold Heap.istate at hst0; split at hst0 <;> simp_all
  obtain ⟨d, hd⟩ := hbytes
  refine ⟨?_, ?_⟩
  · simp [ZlibNg.Inflate.wrS, C.run, bind_app, ldState_app hst0, C.stState, hst0]
  · exact ⟨i, z, b0, f st0, al, rfl, hz, hb0, by simp [Heap.istate, hd], by simpa [Heap.iallocsOf] using hal,
      Core.of_heap (h := h) rfl rfl (hkeep al z c)⟩

end ZlibNgF.Proof.InflateInv
