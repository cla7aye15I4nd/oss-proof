import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«public-inflate-init»

/-!
# Deflate entry points that only check, query or set state fields (`ZlibNgF`)

For `deflatePending`, `deflateUsed`, `deflateTune`, `deflateSetHeader` and `deflateEnd`: on `Z_NULL`, on a stream
with no state, and on a stream with the structural invariant `DInv`, the call does not fault, its result heap is
given exactly, and (except `deflateEnd`, which ends the stream) the invariant holds after it. The registered goals
of these functions follow once every deflate step is shown to keep the invariant (`Proof/deflate.c.reach.lean`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateControl
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.InflateInv (ldStream_app)

/-! ## `deflatePending`, `deflateUsed` -/

theorem deflatePending_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (hp hb : Bool) :
    ∃ r, C.run (deflatePending s hp hb) h = .ok (r, h) := by
  constructor
  simp only [C.run, deflatePending, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

theorem deflatePending_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hp hb : Bool) :
    ∃ r, C.run (deflatePending s hp hb) h = .ok (r, h) := by
  obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := live hv
  cases hp <;> cases hb <;>
    exact ⟨_, by simp [C.run, deflatePending, bind_app, L.check, L.stateOf, rdD_app L]; rfl⟩

theorem deflateUsed_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (hb : Bool) :
    ∃ r, C.run (deflateUsed s hb) h = .ok (r, h) := by
  constructor
  simp only [C.run, deflateUsed, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

theorem deflateUsed_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hb : Bool) :
    ∃ r, C.run (deflateUsed s hb) h = .ok (r, h) := by
  obtain ⟨i, z, b, st, al, rfl, L, _, _⟩ := live hv
  cases hb <;> exact ⟨_, by simp [C.run, deflateUsed, bind_app, L.check, L.stateOf, rdD_app L]; rfl⟩

/-! ## `deflateTune` -/

theorem deflateTune_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (g l n c : Int32) :
    C.run (deflateTune s g l n c) h = .ok (Z_STREAM_ERROR, h) := by
  simp only [C.run, deflateTune, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

/-- `deflateTune` stores four fields of the state, none of which the invariant reads. -/
theorem deflateTune_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (g l n c : Int32) :
    ∃ i z b st, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
      C.run (deflateTune s g l n c) h = .ok (Z_OK, { h with dstates := upd h.dstates b (some
        { st with good_match := g.toUInt32, max_lazy_match := l.toUInt32, nice_match := n,
                  max_chain_length := c.toUInt32 }) }) ∧
      DInv { h with dstates := upd h.dstates b (some
        { st with good_match := g.toUInt32, max_lazy_match := l.toUInt32, nice_match := n,
                  max_chain_length := c.toUInt32 }) } s := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, cr⟩ := live hv
  refine ⟨i, z, b, st, rfl, L.hz, L.hb, L.dstate, ?_, setD L hal _ cr⟩
  simp [C.run, deflateTune, bind_app, L.check, L.stateOf, wrD_app L]

/-! ## `deflateSetHeader` -/

theorem deflateSetHeader_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) (hp : HeaderPtr) :
    C.run (deflateSetHeader s hp) h = .ok (Z_STREAM_ERROR, h) := by
  simp only [C.run, deflateSetHeader, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

/-- `deflateSetHeader` rejects a non-gzip stream and otherwise stores the header pointer. -/
theorem deflateSetHeader_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) (hp : HeaderPtr) :
    C.run (deflateSetHeader s hp) h = .ok (Z_STREAM_ERROR, h) ∨
    ∃ i z b st, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
      C.run (deflateSetHeader s hp) h =
        .ok (Z_OK, { h with dstates := upd h.dstates b (some { st with gzhead := .val hp }) }) ∧
      DInv { h with dstates := upd h.dstates b (some { st with gzhead := .val hp }) } s := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, cr⟩ := live hv
  by_cases hw : st.wrap = 2
  · refine Or.inr ⟨i, z, b, st, rfl, L.hz, L.hb, L.dstate, ?_, setD L hal _ { cr with gzhead := ⟨hp, rfl⟩ }⟩
    simp [C.run, deflateSetHeader, bind_app, L.check, L.stateOf, rdD_app L, wrD_app L, hw]
  · refine Or.inl ?_
    simp [C.run, deflateSetHeader, bind_app, L.check, L.stateOf, rdD_app L, hw]

/-! ## `deflateEnd` -/

theorem deflateEnd_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    C.run (deflateEnd s) h = .ok (Z_STREAM_ERROR, h) := by
  simp only [C.run, deflateEnd, bind_app, stateCheck_noState hn, ↓reduceIte]
  rfl

/-- `deflateEnd` frees the stream's block and clears its `state` field. -/
theorem deflateEnd_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b r, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      C.run (deflateEnd s) h = .ok (r,
        { h with
          bytes := upd h.bytes b none
          savedPtrs := upd h.savedPtrs b none
          streams := upd h.streams i (some { z with state := none }) }) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, cr⟩ := live hv
  obtain ⟨d, hd⟩ := L.hd
  have hab : st.alloc_bufs = .val (some b) := cr.alloc_bufs
  have hal' : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨i, z, b, if st.status == BUSY_STATE then Z_DATA_ERROR else Z_OK, rfl, L.hz, L.hb, ?_⟩
  simp [C.run, deflateEnd, free_deflate, bind_app, L.check, L.stateOf, ldDState_app L.dstate, hab, Ival.get,
    ldDAllocs, Heap.dallocsOf, hd, hal', ldStream, cr.al_zfree, cr.al_buf, callZfree,
    ZlibNg.Zutil.zcfree, freeB, ZlibNg.Inflate.wrZ, stStream, L.hz]

end ZlibNgF.Proof.DeflateControl
