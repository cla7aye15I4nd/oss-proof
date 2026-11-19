import ZlibNgF.Spec.Safety.Deflate
import ZlibNgF.Proof.«inflate.c.invariant»

/-!
# Structural invariant of a deflate stream (`ZlibNgF`)

`DInv h s`: the stream `s` holds a live `deflate_state` made by `deflateInit2` with the default allocator, carved
from the block of `alloc_deflate` together with its `deflate_allocs` record, with the fields that the state check
and the entry points read in range. As on the inflate side (`Proof/inflate.c.invariant.lean`), the invariant reads
the state only through the view `dview`: a store that changes only fields outside the view keeps it by `rfl`. Proofs
use it through the interface lemmas at the end of this file.

Besides the fields of the state check, the clauses fix what `deflateInit2` and `deflateReset` set up and every
later call keeps: `pending_buf` is set, `head` lies in the plain bytes of the block (`CLEAR_HASH`), `level` is
0..9 (`lm_set_level`), the tree arrays have their C sizes (`zng_tr_init`); the sizes `w_size`, `window_size`,
`lit_bufsize`, `pending_buf_size`, `sym_end`; the layout of `alloc_deflate` (window, `prev`, `head`, `pending_buf`
in that order, `sym_buf` at `pending_buf + lit_bufsize + PENDING_BUF_PAD`) and the pending bytes within
`pending_buf`; whole symbols in `sym_buf` up to `sym_end`; at most 64 bits in `bi_buf`; `strstart + lookahead`
within the window; a valid `strategy`; both function pointers of `lm_set_level` set.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateInv
open C ZlibNgF.Spec ZlibNg.Deflate
open ZlibNgF.Proof.InflateInv (ldStream_app)

/-- The fields of a `deflate_state` that the invariant constrains. -/
structure DView where
  strm : Ival StreamPtr
  alloc_bufs : Ival DAllocsPtr
  status : Int32
  wrap : Int32
  gzhead : Ival HeaderPtr
  w_size : UInt32
  pending_buf : Ival BPtr
  head : Ival BPtr
  level : Int32
  lsize : Nat
  dsize : Nat
  bsize : Nat
  window : Ival BPtr
  prev : Ival BPtr
  window_size : UInt32
  lit_bufsize : UInt32
  pending_buf_size : UInt32
  sym_buf : Ival BPtr
  sym_end : UInt32
  sym_next : UInt32
  pending : UInt32
  pending_out : Ival BPtr
  bi_valid : Int32
  strstart : UInt32
  lookahead : UInt32
  strategy : Int32
  longest_match : Ival LongestMatchFn
  insert_batch : Ival InsertBatchFn

/-- The constrained fields of `st`. -/
def dview (st : DeflateState) : DView :=
  ⟨st.strm, st.alloc_bufs, st.status, st.wrap, st.gzhead, st.w_size, st.pending_buf, st.head, st.level,
    st.dyn_ltree.size, st.dyn_dtree.size, st.bl_tree.size, st.window, st.prev, st.window_size, st.lit_bufsize,
    st.pending_buf_size, st.sym_buf, st.sym_end, st.sym_next, st.pending, st.pending_out, st.bi_valid, st.strstart,
    st.lookahead, st.strategy, st.longest_match, st.insert_batch⟩

/-- The clauses on the stream record `z`, the constrained state fields `v` and the allocation record `al` of
block `b`. -/
structure DCore (h : Heap) (s : StreamPtr) (z : ZStream) (b : Nat) (v : DView) (al : DeflateAllocs) : Prop where
  zalloc : z.zalloc = .zcalloc
  zfree : z.zfree = .zcfree
  strm : v.strm = .val s
  alloc_bufs : v.alloc_bufs = .val (some b)
  al_state : al.state = .val (some b)
  al_zfree : al.zfree = .val .zcfree
  al_buf : al.buf_start = .val (.ref (.heap b) 0)
  status_lo : INIT_STATE ≤ v.status
  status_hi : v.status ≤ MAX_STATE
  wrap : v.wrap = 0 ∨ v.wrap = 1 ∨ v.wrap = 2
  gzhead : ∃ hp, v.gzhead = .val hp
  /-- `w_size = 1 << w_bits` is not zero (`W_BITS` takes its trailing zeros) -/
  w_size : v.w_size ≠ 0
  /-- `pending_buf` is set -/
  pbuf : ∃ pb, v.pending_buf = .val pb
  /-- `head` (`HASH_SIZE` two-byte entries) lies in the plain bytes of the block -/
  head : ∃ ho d, h.bytes b = some d ∧ v.head = .val (.ref (.heap b) ho) ∧ ho + 131072 ≤ d.size
  /-- `level` is a valid compression level (`lm_set_level` indexes `configuration_table` with it) -/
  level : 0 ≤ v.level ∧ v.level ≤ 9
  /-- the tree arrays have their C sizes -/
  trees : v.lsize = HEAP_SIZE ∧ v.dsize = 2 * 30 + 1 ∧ v.bsize = 2 * 19 + 1
  /-- the sizes that `deflateInit2` and `lm_init` set: `w_size = 1 << windowBits` (`windowBits` 9..15),
  `window_size = W_BUF_SIZE(w_size)`, `lit_bufsize = 1 << (memLevel + 6)`, `pending_buf_size = 4 * lit_bufsize`,
  `sym_end = (lit_bufsize - 1) * 3` -/
  sizes : 512 ≤ v.w_size.toNat ∧ v.w_size.toNat ≤ 32768 ∧ v.window_size = W_BUF_SIZE v.w_size ∧
    128 ≤ v.lit_bufsize.toNat ∧ v.lit_bufsize.toNat ≤ 32768 ∧ v.pending_buf_size.toNat = 4 * v.lit_bufsize.toNat ∧
    v.sym_end.toNat = 3 * (v.lit_bufsize.toNat - 1)
  /-- the layout of `alloc_deflate`: the window (`window_size` bytes), `prev` (`w_size` two-byte entries), `head`
  (`HASH_SIZE` two-byte entries) and `pending_buf` (`PENDING_BUF_SIZE` bytes, then padding to 64) lie in that order
  in the plain bytes of block `b`; `sym_buf` is `pending_buf + lit_bufsize + PENDING_BUF_PAD`; the pending bytes
  `[pending_out, pending_out + pending)` lie within `pending_buf` -/
  lay : ∃ d wo po ho pbo, h.bytes b = some d ∧ v.window = .val (.ref (.heap b) wo) ∧
    v.prev = .val (.ref (.heap b) po) ∧ v.head = .val (.ref (.heap b) ho) ∧
    v.pending_buf = .val (.ref (.heap b) pbo) ∧ wo + v.window_size.toNat ≤ po ∧ po + 2 * v.w_size.toNat ≤ ho ∧
    ho + 131072 ≤ pbo ∧ pbo + 4 * v.lit_bufsize.toNat + 64 ≤ d.size ∧
    v.sym_buf = .val (.ref (.heap b) (pbo + v.lit_bufsize.toNat + 8)) ∧
    ∃ poo, v.pending_out = .val (.ref (.heap b) poo) ∧ pbo ≤ poo ∧
      poo - pbo + v.pending.toNat ≤ 4 * v.lit_bufsize.toNat + 9
  /-- the symbol buffer holds whole three-byte symbols, at most `sym_end` bytes -/
  syms : v.sym_next ≤ v.sym_end ∧ v.sym_next.toNat % 3 = 0
  /-- the bit buffer holds at most `BIT_BUF_SIZE` bits -/
  bits : 0 ≤ v.bi_valid ∧ v.bi_valid ≤ 64
  /-- the window positions in use lie in the window -/
  look : v.strstart.toNat + v.lookahead.toNat ≤ v.window_size.toNat
  /-- `strategy` is one of the five strategies -/
  strategy : 0 ≤ v.strategy ∧ v.strategy ≤ 4
  /-- `lm_set_level` has set both function pointers -/
  fns : (∃ f, v.longest_match = .val f) ∧ (∃ f, v.insert_batch = .val f)

/-- The clauses read the heap only through block `b`. -/
theorem DCore.of_heap {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (hb : h'.bytes b = h.bytes b) (c : DCore h s z b v al) : DCore h' s z b v al :=
  { c with head := by rw [hb]; exact c.head, lay := by rw [hb]; exact c.lay }

/-- The structural invariant of the deflate stream `s` in `h`. -/
def DInv (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ DCore h s z b (dview st) al

/-! ## Interface lemmas -/

/-- `ldDState` of a live state. -/
theorem ldDState_app {h : Heap} {b : Nat} {st : DeflateState} (hb : h.dstate b = some st) :
    ldDState (some b) h = .ok (st, h) := by simp [ldDState, hb]

/-- A stream that the state check rejects: `Z_NULL`, or a live stream with no state. -/
def DNoState (h : Heap) (s : StreamPtr) : Prop := s = none ∨ ∃ z, StreamAt h s z ∧ z.state = none

/-- `deflateStateCheck` rejects a stream with no state, without changing the heap. -/
theorem stateCheck_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    deflateStateCheck s h = .ok (true, h) := by
  rcases hn with rfl | ⟨z, ⟨i, rfl, hi⟩, hs⟩
  · rfl
  · by_cases ha : z.zalloc = .null
    · simp [deflateStateCheck, bind_app, ldStream_app hi, ha]
    · by_cases hf : z.zfree = .null <;> simp [deflateStateCheck, bind_app, ldStream_app hi, hs, ha, hf]

/-- Stream `i` holds `z`, whose state is the live `st` of block `b`, and `deflateStateCheck` accepts it. -/
structure DLive (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) : Prop where
  hz : h.streams i = some z
  hb : z.state = some b
  hd : ∃ d, h.bytes b = some d
  hst : h.dstates b = some st
  za : z.zalloc ≠ .null
  zf : z.zfree ≠ .null
  ab : ∃ a, st.alloc_bufs = .val (some a)
  sm : st.strm = .val (some i)
  lo : INIT_STATE ≤ st.status
  hi : st.status ≤ MAX_STATE

theorem DLive.dstate {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (L : DLive h i z b st) :
    h.dstate b = some st := by
  obtain ⟨d, hd⟩ := L.hd; simp [Heap.dstate, hd, L.hst]

theorem DLive.check {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (L : DLive h i z b st) :
    deflateStateCheck (some i) h = .ok (false, h) := by
  obtain ⟨a, ha⟩ := L.ab
  have hm1 : ¬ st.status < INIT_STATE := fun hlt => absurd L.lo (Int32.not_le.mpr hlt)
  have hm2 : ¬ st.status > MAX_STATE := fun hlt => absurd L.hi (Int32.not_le.mpr hlt)
  simp [deflateStateCheck, bind_app, ldStream_app L.hz, ldDState_app L.dstate, L.hb, L.za, L.zf, ha, L.sm,
    Ival.get, hm1, hm2]

theorem DLive.stateOf {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (L : DLive h i z b st) :
    dstateOf (some i) h = .ok (some b, h) := by
  simp [dstateOf, ZlibNg.Inflate.rdZ, bind_app, ldStream_app L.hz, L.hb]

/-- An invariant stream is live. -/
theorem live {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b st al, s = some i ∧ DLive h i z b st ∧ h.dallocsOf b = some al ∧ DCore h s z b (dview st) al := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have hd : ∃ d, h.bytes b = some d := by
    unfold Heap.dstate at hst; split at hst <;> simp_all
  have hst' : h.dstates b = some st := by
    obtain ⟨d, hd⟩ := hd; simpa [Heap.dstate, hd] using hst
  refine ⟨i, z, b, st, al, rfl, ⟨hz, hb, hd, hst', ?_, ?_, ⟨b, c.alloc_bufs⟩, c.strm, c.status_lo, c.status_hi⟩,
    hal, c⟩
  · rw [c.zalloc]; decide
  · rw [c.zfree]; decide

/-- A store into the state record of an invariant stream that keeps every clause keeps the invariant. The result
heap differs from `h` only in the state of block `b`. -/
theorem setD {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (L : DLive h i z b st) (hal : h.dallocsOf b = some al) (st' : DeflateState)
    (c : DCore h (some i) z b (dview st') al) :
    DInv { h with dstates := upd h.dstates b (some st') } (some i) := by
  obtain ⟨d, hd⟩ := L.hd
  exact ⟨i, z, b, st', al, rfl, L.hz, L.hb, by simp [Heap.dstate, hd], by simpa [Heap.dallocsOf, hd] using hal,
    DCore.of_heap (h := h) rfl c⟩

/-- `wrD` on a live state. -/
theorem wrD_app {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (L : DLive h i z b st)
    (f : DeflateState → DeflateState) :
    wrD (some b) f h = .ok ((), { h with dstates := upd h.dstates b (some (f st)) }) := by
  simp [wrD, stDState, bind_app, ldDState_app L.dstate, L.dstate]

/-- `rdD` on a live state. -/
theorem rdD_app {α : Type} {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} (L : DLive h i z b st)
    (f : DeflateState → α) : rdD (some b) f h = .ok (f st, h) := by
  simp [rdD, bind_app, ldDState_app L.dstate]

end ZlibNgF.Proof.DeflateInv
