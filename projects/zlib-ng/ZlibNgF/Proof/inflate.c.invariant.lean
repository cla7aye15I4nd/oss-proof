import ZlibNgF.Proof.«inflate.c.tables»

/-!
# Structural invariant of an inflate stream (`ZlibNgF`)

`InflateInv h s`: the stream `s` holds a live state made by `inflateInit2_` with the default allocator, in the carve
layout of `alloc_inflate`, with its fields in range. Proofs use it only through the interface lemmas at the end of
this file, so that a clause can be added or changed without touching the per-function proofs.

## Plan of the final assembly

1. Per public function, "invariant in → no fault, exact result heap, invariant out" (`*_inv` lemmas), and the
   `Z_NULL` / no-state case (`*_noState`). Done: `inflateMark`, `inflateSyncPoint`, `inflateCodesUsed`,
   `inflateValidate`, `inflateGetHeader`, `inflateEnd`, `inflateResetKeep`, `inflateReset`, `inflateReset2`,
   `inflatePrime` (`Proof/public-inflate-control.lean`, `Proof/inflate.c.reset.lean`), `inflateGetDictionary`
   (`Proof/inflate.c.dict.lean`), `updatewindow` without a check value and `inflateSetDictionary`
   (`Proof/inflate.c.window.lean`, with the safety of `adler32_c` from `Proof/adler32_c.c.safety.lean`), `inflateSync` (`Proof/inflate.c.sync.lean`),
   `inflateCopy` (source kept, destination established on `Z_OK`, `Proof/inflate.c.copy.lean`); `inflateInit2`
   establishes the invariant on success (`InflateAlloc.init2_inv`, every heap).
2. `InflateReach.reach_inv (P : Pending) : InflateReachable h s → Inv h s` (`Proof/inflate.c.reach.lean`): the
   induction is written and every constructor case is proved (init, init2, caller step, the steps of 1) except the
   single field of `Pending`: preservation by `inflate`. Proving it closes the induction.
3. Frames: each `*_inv` lemma gives the result heap exactly (`setZS h i z b st` for the resets; `{ h with istates :=
   upd h.istates b _ }` for `inflatePrime`, `inflateValidate`; plus `gzheaders k` for `inflateGetHeader`; bytes and
   `savedPtrs` of `b` and stream `i` for `inflateEnd`), so `Frame h h' (streamIds s) (stateIds h s) ...` is a
   pointwise `upd_ne` argument; `InflateAlloc.Fr.frame` does it for the allocating calls.
4. Each registered goal `Goal.f_safety` then follows: `InflateHandle` splits into `Z_NULL` / no state (`*_noState`)
   and reachable (`reach_inv` → `*_inv` → frame); every function but `inflate` has its `*_safety_of`.
5. `inflate`: `Core` carries the mode-conditional clauses `ModeOK` (counts of a dynamic header, code lengths read so
   far, the decoding tables `TabAt` of `Proof/inflate.c.tables.lean`, extra bits, match distance) and `bits ≤ 39`.
   The callees proved in other files enter as the hypothesis structures `TableFacts` (`zng_inflate_table`),
   `FastFacts` (`inflate_fast_c` / `inflate_fast_safe_c`) and `CopyFacts` (`chunkmemset_safe_c`) of
   `Proof/inflate.c.facts.lean`; the loop of `inflate` is proved mode by mode from them, and `Pending` follows.
   `hold < 2 ^ bits` is not a clause: no mode of `inflate` needs it for safety.
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
  reqbits : UInt32
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
  head : Ival HeaderPtr
  lenbits : UInt32
  distbits : UInt32
  codes : Array Code
  lens : Array UInt16
  ncode : UInt32
  nlen : UInt32
  ndist : UInt32
  «have» : UInt32
  extra : UInt32
  offset : UInt32

/-- The constrained fields of `st`. -/
def view (st : InflateState) : View :=
  ⟨st.strm, st.alloc_bufs, st.window, st.wbufsize, st.mode, st.wbits, st.reqbits, st.wsize, st.whave, st.wnext,
    st.bits, st.codes.size, st.lens.size, st.work.size, st.lencode, st.distcode, st.next, st.head, st.lenbits,
    st.distbits, st.codes, st.lens, st.ncode, st.nlen, st.ndist, st.«have», st.extra, st.offset⟩

/-- The fields that the mode-conditional clauses read (`ModeOK`), so that a store into another field keeps them by
definition. -/
structure MView where
  mode : UInt32
  lencode : Ival CodePtr
  distcode : Ival CodePtr
  lenbits : UInt32
  distbits : UInt32
  codes : Array Code
  lens : Array UInt16
  ncode : UInt32
  nlen : UInt32
  ndist : UInt32
  «have» : UInt32
  extra : UInt32
  offset : UInt32

def View.m (v : View) : MView :=
  ⟨v.mode, v.lencode, v.distcode, v.lenbits, v.distbits, v.codes, v.lens, v.ncode, v.nlen, v.ndist, v.«have»,
    v.extra, v.offset⟩

/-- The modes that decode with the literal/length and distance tables (`LEN_` to `LIT`). -/
def DecodeMode (m : UInt32) : Prop :=
  m = LEN_ ∨ m = LEN ∨ m = LENEXT ∨ m = DIST ∨ m = DISTEXT ∨ m = MATCH ∨ m = LIT

open ZlibNgF.Proof.InflateTab (TabAt) in
/-- What the modes from `LENLENS` to `LIT` need of the state when the loop of `inflate` enters them: the counts of
a dynamic block header (`LENLENS`, `CODELENS`), the code lengths read so far (in range for `zng_inflate_table`), the
decoding tables (`TabAt`: entries read in bounds, bounded bit counts), the number of extra bits of a length or
distance, and a nonzero match distance. Each clause is conditional on the mode, so a store that sets another mode
keeps it. -/
structure ModeOK (b : Nat) (v : MView) : Prop where
  lenlens : v.mode = LENLENS → v.ncode ≤ 19 ∧ v.nlen ≤ 286 ∧ v.ndist ≤ 30 ∧
    ∀ j, j < v.«have».toNat → v.lens[(order[j]!).toNat]! ≤ 7
  codelens : v.mode = CODELENS → v.nlen ≤ 286 ∧ v.ndist ≤ 30 ∧ (∀ j, j < v.«have».toNat → v.lens[j]! ≤ 15) ∧
    TabAt b v.codes v.lencode v.lenbits 25 false
  decode : DecodeMode v.mode → TabAt b v.codes v.lencode v.lenbits 28 false ∧
    TabAt b v.codes v.distcode v.distbits 28 true
  extra : v.mode = LENEXT ∨ v.mode = DISTEXT → v.extra ≤ 31
  offset : v.mode = DISTEXT ∨ v.mode = MATCH → 1 ≤ v.offset.toNat ∧ (v.mode = DISTEXT → v.offset.toNat < 65536)

/-- A mode outside `LENLENS .. LIT` asks nothing. -/
theorem ModeOK.quiet (b : Nat) (v : MView) (hm : v.mode < LENLENS ∨ LIT < v.mode) : ModeOK b v := by
  have h1 : ∀ m : UInt32, (m < LENLENS ∨ LIT < m) → ¬ (LENLENS ≤ m ∧ m ≤ LIT) := by
    intro m h ⟨a, c⟩
    rcases h with h | h
    · exact absurd a (UInt32.not_le.mpr h)
    · exact absurd c (UInt32.not_le.mpr h)
  have h2 := h1 v.mode hm
  refine ⟨fun e => absurd ⟨?_, ?_⟩ h2, fun e => absurd ⟨?_, ?_⟩ h2, fun e => absurd ⟨?_, ?_⟩ h2,
    fun e => absurd ⟨?_, ?_⟩ h2, fun e => absurd ⟨?_, ?_⟩ h2⟩ <;>
  first
    | (rw [e]; decide)
    | (rcases e with e | e | e | e | e | e | e <;> rw [e] <;> decide)
    | (rcases e with e | e <;> rw [e] <;> decide)

open ZlibNgF.Proof.InflateTab (TabAt) in
/-- `inflateCopy` moves the table pointers from the source's `codes` to the copy's. -/
theorem ModeOK.rebase {b b' o2 : Nat} {v : MView} (hm : ModeOK b v) (hl : v.lencode = .val (.ref (.codes b) 0))
    (hd : v.distcode = .val (.ref (.codes b) o2)) :
    ModeOK b' { v with lencode := .val (.ref (.codes b') 0), distcode := .val (.ref (.codes b') o2) } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  refine ⟨h1, fun e => ?_, fun e => ?_, h4, h5⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 e
    rw [hl] at a4
    exact ⟨a1, a2, a3, a4.rebase⟩
  · obtain ⟨a1, a2⟩ := h3 e
    rw [hl] at a1; rw [hd] at a2
    exact ⟨a1.rebase, a2.rebase⟩

/-- With the fixed tables, a state's mode clauses hold for every block. -/
theorem ModeOK.fixed {b b' : Nat} {v : MView} (hm : ModeOK b v) (hl : v.lencode = .val (.ref .lenfix 0))
    (hd : v.distcode = .val (.ref .distfix 0)) : ModeOK b' v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  have nl : ∀ c o, v.lencode ≠ .val (.ref (.codes c) o) := by intro c o e; rw [hl] at e; cases e
  have nd : ∀ c o, v.distcode ≠ .val (.ref (.codes c) o) := by intro c o e; rw [hd] at e; cases e
  refine ⟨h1, fun e => ?_, fun e => ?_, h4, h5⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 e
    exact ⟨a1, a2, a3, a4.fixed nl⟩
  · obtain ⟨a1, a2⟩ := h3 e
    exact ⟨a1.fixed nl, a2.fixed nd⟩

/-- The clauses that `inflateInit2` establishes before it calls `inflateReset2`, and that no reset changes: the
stream record `z`, the allocation record `al` of block `b`, the carve layout, the mode range. -/
structure Shape (h : Heap) (s : StreamPtr) (z : ZStream) (b : Nat) (st : View) (al : InflateAllocs) : Prop where
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
  codes_size : st.codes_size = ENOUGH
  lens_size : st.lens_size = 320
  work_size : st.work_size = 288

/-- All clauses on the stream record `z`, the constrained state fields `st` and the allocation record `al` of block
`b`. -/
structure Core (h : Heap) (s : StreamPtr) (z : ZStream) (b : Nat) (st : View) (al : InflateAllocs) : Prop
    extends Shape h s z b st al where
  wbits : st.wbits ≤ 15
  reqbits : st.reqbits ≤ 15
  /-- the window size is at most 32768 (`updatewindow` sets it to `1 << wbits`; the zlib header may change `wbits`
  after) -/
  wsize : st.wsize ≤ 32768
  whave : st.whave ≤ st.wsize
  wnext : st.wnext = 0 ∨ st.wnext < st.wsize
  /-- the window is filled from 0: until it is full, `wnext = whave` (`inflateGetDictionary` copies `whave - wnext`
  bytes) -/
  wnext_le : st.wnext ≤ st.whave
  /-- until the window is full, the next write position is the end of the data (`updatewindow` adds `dist` to both) -/
  wnext_eq : st.whave < st.wsize → st.wnext = st.whave
  /-- at most 39 bits are held between calls (`inflateSync` moves the whole bytes of the bit buffer, at most 32 bits,
  into `buf[4]`). `inflatePrime` keeps 32; `inflate` can leave 39: `NEEDBITS(32)` in `CHECK` pulls a byte onto 31
  primed bits, and a failing check leaves through `BAD` with all of them. -/
  bits : st.bits ≤ 39
  lencode : ∃ p, st.lencode = .val p ∧ CodeTarget b p
  distcode : ∃ p, st.distcode = .val p ∧ CodeTarget b p
  next : ∃ o, st.next = .val (.ref (.codes b) o) ∧ o ≤ ENOUGH
  /-- `lencode` is the start of `codes` (with `distcode` inside `codes`), or the fixed tables: `inflateCopy` rebases
  `distcode` when `lencode == codes` -/
  tables : (st.lencode = .val (.ref (.codes b) 0) ∧ ∃ o, st.distcode = .val (.ref (.codes b) o) ∧ o ≤ ENOUGH) ∨
    (st.lencode = .val (.ref .lenfix 0) ∧ st.distcode = .val (.ref .distfix 0))
  head : st.head = .val none ∨ ∃ k g, st.head = .val (some k) ∧ h.gzheaders k = some g
  modes : ModeOK b st.m

/-- The shape clauses read the heap only through its byte blocks. -/
theorem Shape.of_heap {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : View} {al : InflateAllocs}
    (hb : h'.bytes b = h.bytes b) (c : Shape h s z b v al) : Shape h' s z b v al :=
  { c with window := by rw [hb]; exact c.window }

/-- The clauses read the heap only through block `b` and the `gz_header` records. -/
theorem Core.of_heap {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : View} {al : InflateAllocs}
    (hb : h'.bytes b = h.bytes b) (hg : h'.gzheaders = h.gzheaders) (c : Core h s z b v al) : Core h' s z b v al :=
  { c with toShape := c.toShape.of_heap hb, head := by rw [hg]; exact c.head }

/-- `1 << wbits` for `wbits ≤ 15` is at most 32768. -/
theorem shl_le (w : UInt32) (hw : w ≤ 15) : (1 : UInt32) <<< w ≤ 32768 := by
  rw [UInt32.le_iff_toNat_le] at hw ⊢
  have hw' : w.toNat ≤ 15 := hw
  rw [UInt32.toNat_shiftLeft]
  have e1 : (1 : UInt32).toNat = 1 := rfl
  have e2 : (32768 : UInt32).toNat = 32768 := rfl
  rw [e1, e2, Nat.mod_eq_of_lt (by omega : w.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul]
  have : 2 ^ w.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hw'
  have : 2 ^ w.toNat % 2 ^ 32 ≤ 2 ^ w.toNat := Nat.mod_le _ _
  omega

/-- The window size is at most 32768 bytes. -/
theorem Core.wsize_le {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : View} {al : InflateAllocs}
    (c : Core h s z b v al) : v.wsize ≤ 32768 := c.wsize

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

/-! ## Live states: what `inflateStateCheck` asks -/

theorem upd_upd {α : Type} [Inhabited α] (t : Tbl α) (k : Nat) (v w : α) : upd (upd t k v) k w = upd t k w := by
  unfold upd Tbl.set
  by_cases hk : k < t.arr.size
  · simp [hk, Array.set!_eq_setIfInBounds]
  · simp only [hk, ite_false, Array.size_append, Array.size_push, Array.size_replicate, Array.set!_eq_setIfInBounds]
    have hk' : t.arr.size + (k - t.arr.size) = k := by omega
    rw [hk']
    simp only [Nat.lt_add_one, ↓reduceIte]
    congr 1
    apply Array.ext_getElem?
    intro j
    simp only [Array.getElem?_setIfInBounds, Array.getElem?_append, Array.getElem?_push, Array.size_replicate,
      Array.size_append, Array.size_push, hk']
    by_cases e : k = j
    · subst e; simp
    · have e' : ¬ j = k := fun x => e x.symm
      simp [e, e']

/-- `h` with stream `i` set to `z` and the state of block `b` set to `st`. -/
def setZS (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : InflateState) : Heap :=
  { h with streams := upd h.streams i (some z), istates := upd h.istates b (some st) }

/-- Stream `i` holds `z`, whose state is the live `st` of block `b`, and `inflateStateCheck` accepts it. -/
structure Live (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : InflateState) : Prop where
  hz : h.streams i = some z
  hb : z.state = some b
  hd : ∃ d, h.bytes b = some d
  hst : h.istates b = some st
  za : z.zalloc ≠ .null
  zf : z.zfree ≠ .null
  ab : ∃ a, st.alloc_bufs = .val (some a)
  sm : st.strm = .val (some i)
  lo : HEAD ≤ st.mode
  hi : st.mode ≤ SYNC

theorem Live.istate {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    h.istate b = some st := by
  obtain ⟨d, hd⟩ := L.hd; simp [Heap.istate, hd, L.hst]

theorem Live.check {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    inflateStateCheck (some i) h = .ok (false, h) := by
  obtain ⟨a, ha⟩ := L.ab
  have hm1 : ¬ st.mode < HEAD := fun hlt => absurd L.lo (UInt32.not_le.mpr hlt)
  have hm2 : ¬ st.mode > SYNC := fun hlt => absurd L.hi (UInt32.not_le.mpr hlt)
  simp [inflateStateCheck, bind_app, ldStream_app L.hz, ldState_app L.istate, L.hb, L.za, L.zf, ha, L.sm, Ival.get,
    hm1, hm2]

theorem Live.stateOf {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st) :
    ZlibNg.Inflate.stateOf (some i) h = .ok (some b, h) := by
  simp [ZlibNg.Inflate.stateOf, rdZ, bind_app, ldStream_app L.hz, L.hb]

/-- A store into the state that keeps the fields the check reads. -/
theorem Live.setS {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st)
    (st' : InflateState) (e1 : st'.alloc_bufs = st.alloc_bufs) (e2 : st'.strm = st.strm) (lo : HEAD ≤ st'.mode)
    (hi : st'.mode ≤ SYNC) : Live { h with istates := upd h.istates b (some st') } i z b st' :=
  ⟨L.hz, L.hb, L.hd, by simp, L.za, L.zf, e1 ▸ L.ab, e2 ▸ L.sm, lo, hi⟩

/-- A store into the stream that keeps `state`, `zalloc`, `zfree`. -/
theorem Live.setZ {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} (L : Live h i z b st)
    (z' : ZStream) (e1 : z'.state = z.state) (e2 : z'.zalloc = z.zalloc) (e3 : z'.zfree = z.zfree) :
    Live { h with streams := upd h.streams i (some z') } i z' b st :=
  ⟨by simp, e1 ▸ L.hb, L.hd, L.hst, e2 ▸ L.za, e3 ▸ L.zf, L.ab, L.sm, L.lo, L.hi⟩

/-- A stream with the shape clauses is live. -/
theorem Shape.live {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : InflateState} {al : InflateAllocs}
    (hz : h.streams i = some z) (hb : z.state = some b) (hst : h.istate b = some st)
    (c : Shape h (some i) z b (view st) al) : Live h i z b st := by
  have hd : ∃ d, h.bytes b = some d := by
    unfold Heap.istate at hst; split at hst <;> simp_all
  have hst' : h.istates b = some st := by
    obtain ⟨d, hd⟩ := hd; simpa [Heap.istate, hd] using hst
  refine ⟨hz, hb, hd, hst', ?_, ?_, ⟨b, c.alloc_bufs⟩, c.strm, c.mode_lo, c.mode_hi⟩
  · rw [c.zalloc]; decide
  · rw [c.zfree]; decide

/-- An invariant stream is live. -/
theorem live {h : Heap} {s : StreamPtr} (hv : Inv h s) :
    ∃ i z b st al, s = some i ∧ Live h i z b st ∧ h.iallocsOf b = some al ∧ Core h s z b (view st) al := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  exact ⟨i, z, b, st, al, rfl, Shape.live hz hb hst c.toShape, hal, c⟩

end ZlibNgF.Proof.InflateInv
