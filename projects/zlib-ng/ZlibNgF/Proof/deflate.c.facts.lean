import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«deflate.c.init»

/-!
# Callee facts of `deflate` (`ZlibNgF`)

The safety of `deflate` and `deflateParams` is proved from two hypothesis structures, each field of which is a
theorem still to prove about the translated C code (no field is an assumption of a registered goal: a goal is
registered only once both structures are proved):

* `StrategyFacts`: the seven strategies (`deflate_stored`, `deflate_quick`, `deflate_fast`, `deflate_medium`,
  `deflate_medium_fizzle`, `deflate_slow`, `deflate_huff`, `deflate_rle`), in the state in which `deflate` calls
  them (`StratPre`), do not fault, keep the invariant and the stream's buffers valid, change only the stream record,
  the stream's block and the output buffer, and leave no pending bytes when they return `block_done` or
  `finish_done` (`StratPost`);
* `TreesFacts`: the block emitters that the strategies and `deflate` call (`zng_tr_flush_block`,
  `zng_tr_stored_block`, `zng_tr_align`, and the `zng_tr_emit_*` of `deflate_quick`), in the working state of a
  strategy (`DWork`: the invariant, except that up to 63 bits may wait in `bi_buf`), given room after the pending
  bytes (`PendRoom`), do not fault, keep the working state, change only the stream's block (within `pending_buf`) and
  the stream's `data_type`, keep the other state fields (`EmitKeeps`), and add a bounded number of pending bytes.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateFacts
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv

/-- The pending bytes of state `st` (block `b`) and `n` bytes more end at most `lim` bytes after `pending_buf`:
`pending_out - pending_buf + pending + n <= lim`. -/
def PendRoom (b : Nat) (st : DeflateState) (n lim : Nat) : Prop :=
  ∃ pbo poo, st.pending_buf = .val (.ref (.heap b) pbo) ∧ st.pending_out = .val (.ref (.heap b) poo) ∧
    poo - pbo + st.pending.toNat + n ≤ lim

/-- The working state of a strategy: the invariant's clauses, except that `bi_buf` holds up to 63 bits (the
clauses are those of `DCore` on the state with `bi_valid` cleared), and the complete bytes of `bi_buf` still fit
after the pending bytes: in `pending_buf` (`PENDING_BUF_SIZE = 4 * lit_bufsize + 9` bytes), and before `sym_buf`
while symbols wait there. -/
def DWork (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ 0 ≤ st.bi_valid ∧ st.bi_valid < 64 ∧
    DCore h s z b (dview { st with bi_valid := 0 }) al ∧
    PendRoom b st (st.bi_valid.toInt.toNat / 8) (4 * st.lit_bufsize.toNat + 9) ∧
    (st.sym_next ≠ 0 → PendRoom b st (st.bi_valid.toInt.toNat / 8) (st.lit_bufsize.toNat + 8))

/-- The state record of stream `s` in `h`: block `b`, record `st`. -/
def DStateIs (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) : Prop :=
  ∃ i z, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st

/-- What `deflate`'s argument check leaves: `next_out` is set, and `next_in` is set when `avail_in` is not zero. -/
def DBufsSet (h : Heap) (s : StreamPtr) : Prop :=
  ∃ z, StreamAt h s z ∧ z.next_out ≠ .null ∧ (z.avail_in ≠ 0 → z.next_in ≠ .null)

/-- The facts about the tallied symbols that hold between calls (kept by every public call, carried by the
reachability induction) and that a strategy needs on entry and gives back on exit: room for one more symbol
(`sym_next < sym_end`: every strategy flushes a full buffer before it returns); except at level 1 with `Z_FIXED`
(`deflate_quick` with `static_emit` keeps a block open across window slides), `strstart - block_start` bounded by
the tallied symbols (a tally covers at most `STD_MAX_MATCH` window bytes, `deflate_slow` keeps one literal pending,
`deflate_stored` and `fill_window` leave at most 65536 bytes); at level 0 (`deflate_stored`, which reads
`window + block_start` and writes `pending_buf` over `sym_buf`) `block_start` is not negative and there are no
symbols and no lookahead; at level 1 with `Z_FIXED` (`deflate_quick` with `static_emit`, which never tallies and
writes `pending_buf` over `sym_buf`) there are no symbols; with `block_start == strstart` there are no
symbols (every tallied symbol moved `strstart` past `block_start`, `FLUSH_BLOCK` resets both). -/
def SymsOk (st : DeflateState) : Prop :=
  st.sym_next < st.sym_end ∧
    (¬ (st.level = 1 ∧ st.strategy = Z_FIXED) →
      (st.strstart.toNat : Int) - st.block_start.toInt ≤ 258 * (st.sym_next.toNat / 3 + 2) + 65536) ∧
    (st.level = 0 → 0 ≤ st.block_start ∧ st.sym_next = 0 ∧ st.lookahead = 0) ∧
    (st.level = 1 → st.strategy = Z_FIXED → st.sym_next = 0) ∧
    ((st.strstart.toNat : Int) = st.block_start.toInt → st.sym_next = 0)

/-- The fields that a strategy reads back unchanged: it never writes them. -/
def StratKeeps (st st' : DeflateState) : Prop :=
  st'.status = st.status ∧ st'.wrap = st.wrap ∧ st'.gzhead = st.gzhead ∧ st'.gzindex = st.gzindex ∧
    st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.last_flush = st.last_flush

/-- The state in which `deflate` calls a strategy: the invariant, the CRC tables, valid and set buffers, a valid
`flush` (`Z_NO_FLUSH` .. `Z_BLOCK`), no pending bytes (`deflate` flushed them, or returned), the header written
(`status` is `BUSY_STATE` or `FINISH_STATE`, so the invariant allows tallied symbols), and `SymsOk`. -/
def StratPre (h : Heap) (s : StreamPtr) (flush : Int32) : Prop :=
  DInv h s ∧ CrcGlobals h ∧ DStreamIO h s ∧ DBufsSet h s ∧ 0 ≤ flush ∧ flush ≤ 5 ∧
    ∃ b st, DStateIs h s b st ∧ st.pending = 0 ∧ (st.status = BUSY_STATE ∨ st.status = FINISH_STATE) ∧ SymsOk st

/-- What a strategy call with `flush` leaves: the invariant, valid and set buffers, a change of the stream record, the
stream's block and the output buffer only, no pending bytes after `block_done` / `finish_done`; `SymsOk` again, the
fields of `StratKeeps` unchanged, no symbols after a call with a flush (every such return goes through `FLUSH_BLOCK`,
or the strategy never tallies), and no symbols and no lookahead after `finish_started` / `finish_done`. -/
def StratPost (h : Heap) (s : StreamPtr) (flush : Int32) (bs : BlockState) (h' : Heap) : Prop :=
  DInv h' s ∧ DStreamIO h' s ∧ DBufsSet h' s ∧ DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧
    (bs = .block_done ∨ bs = .finish_done → ∃ b st, DStateIs h' s b st ∧ st.pending = 0) ∧
    ∀ b st st', DStateIs h s b st → DStateIs h' s b st' → SymsOk st' ∧ StratKeeps st st' ∧
      (flush ≠ Z_NO_FLUSH → st'.sym_next = 0) ∧
      (bs = .finish_started ∨ bs = .finish_done → st'.sym_next = 0 ∧ st'.lookahead = 0)

/-- A strategy `f`: from `StratPre`, no fault and `StratPost`. -/
def StratOk (f : StatePtr → Int32 → M BlockState) : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (b : Nat) (flush : Int32), StratPre h s flush → StateBlock h s b →
    ∃ bs h', C.run (f (some b) flush) h = .ok (bs, h') ∧ StratPost h s flush bs h'

/-- A strategy `f` that `deflate` calls only at a level above 0: as `StratOk`, given `0 < level`. -/
def StratOkL (f : StatePtr → Int32 → M BlockState) : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (b : Nat) (flush : Int32), StratPre h s flush → StateBlock h s b →
    (∀ b' st, DStateIs h s b' st → 0 < st.level) →
    ∃ bs h', C.run (f (some b) flush) h = .ok (bs, h') ∧ StratPost h s flush bs h'

/-- The strategies, one field each (`deflate` calls `deflate_stored` for level 0, `deflate_huff` for
`Z_HUFFMAN_ONLY`, `deflate_rle` for `Z_RLE`, else the function of `configuration_table`; so every strategy but
`deflate_stored` runs at a level above 0). -/
structure StrategyFacts : Prop where
  stored : StratOk ZlibNg.DeflateStored.deflate_stored
  quick : StratOkL ZlibNg.DeflateQuick.deflate_quick
  fast : StratOkL ZlibNg.DeflateFast.deflate_fast
  medium : StratOkL ZlibNg.DeflateMedium.deflate_medium
  medium_fizzle : StratOkL ZlibNg.DeflateMedium.deflate_medium_fizzle
  slow : StratOkL ZlibNg.DeflateSlow.deflate_slow
  huff : StratOkL ZlibNg.DeflateHuff.deflate_huff
  rle : StratOkL ZlibNg.DeflateRle.deflate_rle

/-- Only `data_type` of the stream record of `s` changes (`zng_tr_flush_block` sets it). -/
def StreamKeep (h h' : Heap) (s : StreamPtr) : Prop :=
  ∃ i z z', s = some i ∧ h.streams i = some z ∧ h'.streams i = some z' ∧ z' = { z with data_type := z'.data_type }

/-- `st'` differs from `st` at most in the fields that the block emitters of `trees.c` / `trees_emit.h` write: the
bit buffer, the pending count, the symbol index, and the tree data. -/
def EmitKeeps (st st' : DeflateState) : Prop :=
  st' = { st with
    pending := st'.pending
    bi_buf := st'.bi_buf
    bi_valid := st'.bi_valid
    bi_used := st'.bi_used
    sym_next := st'.sym_next
    opt_len := st'.opt_len
    static_len := st'.static_len
    l_desc := st'.l_desc
    d_desc := st'.d_desc
    bl_desc := st'.bl_desc
    bl_count := st'.bl_count
    pq_leaves := st'.pq_leaves
    pq_scratch := st'.pq_scratch
    dyn_ltree := st'.dyn_ltree
    dyn_dtree := st'.dyn_dtree
    bl_tree := st'.bl_tree }

/-- The bytes of block `b` change only in `pending_buf` (`PENDING_BUF_SIZE` bytes from offset `pbo`). -/
def PbufOnly (h h' : Heap) (b pbo lim : Nat) : Prop :=
  ∃ d d', h.bytes b = some d ∧ h'.bytes b = some d' ∧ d'.size = d.size ∧
    ∀ j, (j < pbo ∨ pbo + lim ≤ j) → d'[j]! = d[j]!

/-- An emitter `m` on stream `s` (block `b`): from the working state with at least `room st` bytes left after the
pending bytes (in `pending_buf`, and before `sym_buf` while symbols wait there), no fault, the working state after,
only block `b` (its bytes within `pending_buf`) and the stream's `data_type` changed, the other state fields kept
(`EmitKeeps`), at most `grow st` more pending bytes, no more symbols, and the exact shape of the heap after: `h` with the stream's
`data_type`, the state record and the bytes of block `b` replaced (`SH`). -/
def EmitOk (s : StreamPtr) (b : Nat) (pre : DeflateState → Prop) (room grow : DeflateState → Nat) (m : M Unit) :
    Prop :=
  ∀ (h : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st →
    PendRoom b st (room st) (4 * st.lit_bufsize.toNat + 9) →
    (st.sym_next ≠ 0 → PendRoom b st (room st) (st.lit_bufsize.toNat + 8)) →
    ∃ h', C.run m h = .ok ((), h') ∧ DWork h' s ∧ DFrame h h' (streamIds s) [b] [] [] ∧ StreamKeep h h' s ∧
      (∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → PbufOnly h h' b pbo (4 * st.lit_bufsize.toNat + 9)) ∧
      (∀ st', DStateIs h' s b st' → EmitKeeps st st' ∧ st'.pending.toNat ≤ st.pending.toNat + grow st ∧
        st'.sym_next ≤ st.sym_next) ∧
      ∀ i z, s = some i → h.streams i = some z → ∃ dt st' d', h' = DeflateInit.SH h i { z with data_type := dt } b st' d'

/-- After a successful run of `m` from the working state of stream `s` (block `b`) with `pre`, no symbol is left in
`sym_buf` (`zng_tr_flush_block` ends with `init_block`). -/
def EmitClears (s : StreamPtr) (b : Nat) (pre : DeflateState → Prop) (m : M Unit) : Prop :=
  ∀ (h h' : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st → C.run m h = .ok ((), h') →
    ∀ st', DStateIs h' s b st' → st'.sym_next = 0

/-- `buf` is `NULL` with `len == 0`, or `len` bytes of the window from offset `k`, below `strstart`. -/
def WindowBuf (b : Nat) (st : DeflateState) (buf : BPtr) (len : UInt32) : Prop :=
  (buf = .null ∧ len = 0) ∨
    ∃ wo k, st.window = .val (.ref (.heap b) wo) ∧ buf = .ref (.heap b) (wo + k) ∧ k + len.toNat ≤ st.strstart.toNat

/-- The precondition of `zng_tr_flush_block` in `FLUSH_BLOCK_ONLY`. -/
def FlushBlockPre (b : Nat) (buf : BPtr) (len : UInt32) (st : DeflateState) : Prop :=
  st.pending = 0 ∧ 0 < st.level ∧ st.bi_valid < 8 ∧ (buf = .null ∨ WindowBuf b st buf len)

/-- The bytes of a stored block of `len` bytes with the bits of `st`: the 3 header bits and the padding to a byte
boundary (`(bi_valid + 3 + 7) / 8` bytes), `LEN` and `NLEN`, the data (the `have` of `deflate_stored`). -/
def storedRoom (st : DeflateState) (len : UInt32) : Nat := len.toNat + (st.bi_valid.toInt.toNat + 42) / 8

/-- The block emitters. `flush_block` is called by `FLUSH_BLOCK_ONLY` with no pending bytes (the previous
`FLUSH_BLOCK` emptied them, or the strategy returned) and fewer than 8 bits in `bi_buf` (the `flush_pending` of the
previous `FLUSH_BLOCK` moved the complete bytes), with `last` 0 or 1 (`FLUSH_BLOCK_ONLY`; `zng_tr_emit_tree` computes `(type << 1) + last` in `int`), at a level
above 0 (level 0 is `deflate_stored`, which does not call it; at level 0 its stored path could copy a block longer than `pending_buf`), and the block's bytes in the window (or `NULL` when
`block_start` is negative); its result fits `pending_buf` (the `sym_buf` overlay argument of `deflate.c`) and it
leaves no symbol (`flush_block_clears`).
`stored_block` writes `storedRoom` bytes; `align` and the `emit_*` of `deflate_quick` (static trees) add at most 16
bytes (with up to 63 bits waiting in `bi_buf`). -/
structure TreesFacts : Prop where
  flush_block : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last → last ≤ 1 →
    EmitOk s b (FlushBlockPre b buf len) (fun _ => 0) (fun st => 4 * st.lit_bufsize.toNat + 9)
      (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)
  flush_block_clears : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32), 0 ≤ last →
    last ≤ 1 → EmitClears s b (FlushBlockPre b buf len) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)
  stored_block : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32),
    EmitOk s b (fun st => WindowBuf b st buf len) (fun st => storedRoom st len) (fun st => storedRoom st len)
      (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last)
  align : ∀ (s : StreamPtr) (b : Nat), EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
    (ZlibNg.Trees.zng_tr_align (some b))
  emit_lit : ∀ (s : StreamPtr) (b : Nat) (c : UInt32), c < 256 →
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c)
  emit_dist : ∀ (s : StreamPtr) (b : Nat) (lc dist : UInt32), lc ≤ 255 → 1 ≤ dist → dist ≤ 32768 →
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) ZlibNg.DeflateQuick.static_ltree_p
        ZlibNg.DeflateQuick.static_dtree_p lc dist)
  emit_tree : ∀ (s : StreamPtr) (b : Nat) (last : Int32), 0 ≤ last → last ≤ 1 →
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last)
  emit_end_block : ∀ (s : StreamPtr) (b : Nat) (last : Int32),
    EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) ZlibNg.DeflateQuick.static_ltree_p last)
  emit_align : ∀ (s : StreamPtr) (b : Nat), EmitOk s b (fun _ => True) (fun _ => 16) (fun _ => 16)
      (ZlibNg.TreesEmit.zng_tr_emit_align (some b))

/-! ## Window facts -/

/-- The input that `read_buf` reads: `next_in` has `avail_in` readable bytes outside block `b` of the stream's
state, and is set when `avail_in` is not zero. -/
def DInput (h : Heap) (s : StreamPtr) : Prop :=
  ∃ z b, StreamAt h s z ∧ z.state = some b ∧ NullOrRead h z.next_in z.avail_in.toNat ∧ NotInBlock b z.next_in ∧
    (z.avail_in ≠ 0 → z.next_in ≠ .null)

/-- The invariant of stream `s`, except that `strstart - block_start` may reach `2^30 + 2^16`: the clauses of `DCore` on
the state with `block_start` at `strstart`, and `block_start` at or before `strstart`. This is the state inside the
insertion loop of `deflateSetDictionary`, which raises `strstart` (by at most the dictionary length in all) before it
sets `block_start = (int)strstart`; `fill_window` needs only `block_start - slide_len` in range. -/
def DInvW (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ DCore h s z b (dview { st with block_start := st.strstart.toInt32 }) al ∧
    st.block_start.toInt ≤ st.strstart.toNat ∧ (st.strstart.toNat : Int) - st.block_start.toInt ≤ 2 ^ 30 + 2 ^ 16

/-- What `fill_window` leaves: `DInvW` and a readable input; only the stream record (`next_in`, `avail_in`,
`total_in`, `adler`) and the stream's block change; `avail_in` does not grow and drops when `lookahead` changes, and
`lookahead` grows by at most the input taken (the window gains only input bytes); `strstart - block_start` is kept (a
slide lowers both by `slide_len`); at the end the lookahead is full or the input empty; the state fields that the
callers read back (`wrap`, `status`, `gzhead`, `level`, `strategy`, the function pointers, `sym_next`, `gzindex`,
`last_flush`) kept. -/
def FillPost (h h' : Heap) (s : StreamPtr) : Prop :=
  DInvW h' s ∧ DInput h' s ∧ DFrame h h' (streamIds s) (stateIds h s) [] [] ∧
  ∃ i z z' b st st', s = some i ∧ h.streams i = some z ∧ h'.streams i = some z' ∧ z.state = some b ∧
    h.dstate b = some st ∧ h'.dstate b = some st' ∧
    z' = { z with
      next_in := z'.next_in
      avail_in := z'.avail_in
      total_in := z'.total_in
      adler := z'.adler } ∧
    z'.avail_in.toNat ≤ z.avail_in.toNat ∧
    (st'.lookahead ≠ st.lookahead → z'.avail_in.toNat < z.avail_in.toNat) ∧
    st'.lookahead.toNat + z'.avail_in.toNat ≤ st.lookahead.toNat + z.avail_in.toNat ∧
    (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt ∧
    (262 ≤ st'.lookahead.toNat ∨ z'.avail_in = 0) ∧
    st'.wrap = st.wrap ∧ st'.status = st.status ∧ st'.gzhead = st.gzhead ∧ st'.level = st.level ∧
    st'.strategy = st.strategy ∧ st'.longest_match = st.longest_match ∧ st'.insert_batch = st.insert_batch ∧
    st'.sym_next = st.sym_next ∧ st'.gzindex = st.gzindex ∧ st'.last_flush = st.last_flush

/-- The window functions that `deflateSetDictionary` (and the strategies) call, one field each, to be proved about
the translated C code: `fill_window` from `DInvW` (the invariant, or the state inside `deflateSetDictionary`'s
insertion loop), a readable input (the CRC tables when it computes a CRC-32) and `lookahead < MIN_LOOKAHEAD` (every
caller's condition), and the `insert_batch` functions of `lm_set_level` over `n >= 1` positions from `str` whose
4-byte reads stay below `strstart + lookahead + 1`; they change only the bytes of the stream's block (`head`, `prev`)
and `ins_h` (the result is the `SH` heap of `Proof/deflate.c.init.lean`). -/
structure WindowFacts : Prop where
  fill_window : ∀ (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState), DInvW h s → DStateIs h s b st →
    DInput h s → (st.wrap = 2 → CrcGlobals h) → st.lookahead.toNat < 262 →
    ∃ h', C.run (ZlibNg.Deflate.fill_window (some b)) h = .ok ((), h') ∧ FillPost h h' s
  insert_batch : ∀ (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8)
    (f : InsertBatchFn) (wo : Nat) (str n : UInt32), DInvW h (some i) → h.streams i = some z → z.state = some b →
    h.dstate b = some st → h.bytes b = some d → st.window = .val (.ref (.heap b) wo) → 1 ≤ n.toNat →
    str.toNat + n.toNat + 2 ≤ st.strstart.toNat + st.lookahead.toNat →
    ∃ st' d', C.run (ZlibNg.InsertString.call_insert_batch f (some b) (.ref (.heap b) wo) str n) h =
        .ok ((), DeflateInit.SH h i z b st' d') ∧
      DInvW (DeflateInit.SH h i z b st' d') (some i) ∧ st' = { st with ins_h := st'.ins_h } ∧ d'.size = d.size

/-! ## Interface lemmas -/

/-- The invariant's pending range as `PendRoom` with no bytes more. -/
theorem pendRoom_of_core {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (c : DCore h s z b (dview st) al) : PendRoom b st 0 (4 * st.lit_bufsize.toNat + 9) := by
  obtain ⟨_, _, _, _, pbo, _, -, -, -, hpb, -, -, -, -, -, poo, hpo, -, hpe⟩ := c.lay
  exact ⟨pbo, poo, hpb, hpo, hpe⟩

/-- An invariant stream is in the working state. -/
theorem DWork.of_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) : DWork h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have b0 : 0 ≤ st.bi_valid := c.bits.1
  have b8 : st.bi_valid < 8 := c.bits.2
  have e8 : (8 : Int32).toInt = 8 := rfl
  have e64 : (64 : Int32).toInt = 64 := rfl
  have l8 := Int32.lt_iff_toInt_lt.mp b8
  have l0 := Int32.le_iff_toInt_le.mp b0
  have hz8 : st.bi_valid.toInt.toNat / 8 = 0 := by
    have : (0 : Int32).toInt = 0 := rfl
    omega
  refine ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, Int32.lt_iff_toInt_lt.mpr (by omega),
    { c with bits := ⟨Int32.le_refl _, show (0 : Int32) < 8 by decide⟩ }, by rw [hz8]; exact pendRoom_of_core c,
    fun hn => ?_⟩
  obtain ⟨pbo, poo, hpb, hpo, hq⟩ := c.psym hn
  exact ⟨pbo, poo, hpb, hpo, by rw [hz8]; exact hq⟩

/-- A working state with fewer than 8 bits in `bi_buf` is invariant. -/
theorem DWork.inv {h : Heap} {s : StreamPtr} (hw : DWork h s)
    (h8 : ∀ b st, DStateIs h s b st → st.bi_valid < 8) : DInv h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, -, c, -⟩ := hw
  exact ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with bits := ⟨b0, h8 b st ⟨i, z, rfl, hz, hb, hst⟩⟩ }⟩

/-- `strstart` of an invariant view is at most 65536, so `(int)strstart` is exact. -/
theorem strstart_toInt32 {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore h s z b v al) : v.strstart.toInt32.toInt = v.strstart.toNat ∧ v.strstart.toNat ≤ 65536 := by
  have hl := c.look
  obtain ⟨-, hw, hws, -⟩ := c.sizes
  have h65 : v.window_size.toNat ≤ 65536 := by
    rw [hws, DeflateInit.wbuf_toNat _ hw]; unfold DeflateAlloc.dWS; split <;> omega
  exact ⟨DeflateAlloc.u32_toInt32_toInt _ (by omega), by omega⟩

/-- An invariant stream satisfies `DInvW`. -/
theorem DInvW.of_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) : DInvW h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have e := (strstart_toInt32 c).1
  have hb1 := c.bstart
  have hb2 := c.bs_lo
  simp only [dview] at e hb1 hb2
  refine ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with
    bstart := by simp only [dview]; rw [e]; exact Int.le_refl _
    bs_lo := by simp only [dview]; rw [e]; omega }, hb1, by omega⟩

/-- `DInvW` with `strstart - block_start` at most `2^30` is the invariant. -/
theorem DInvW.inv {h : Heap} {s : StreamPtr} (hw : DInvW h s)
    (hd : ∀ b st, DStateIs h s b st → (st.strstart.toNat : Int) - st.block_start.toInt ≤ 2 ^ 30) : DInv h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c, h1, h2⟩ := hw
  exact ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with
    bstart := h1
    bs_lo := hd b st ⟨i, z, rfl, hz, hb, hst⟩ }⟩

/-- `fill_window` from an invariant stream leaves the invariant. -/
theorem FillPost.inv {h h' : Heap} {s : StreamPtr} (hv : DInv h s) (hp : FillPost h h' s) : DInv h' s := by
  obtain ⟨hw, -, -, i, z, z', b, st, st', rfl, hz, hz', hb, hst, hst', hzz, -, -, -, hd, -⟩ := hp
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, -, c⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  have hl := c.bs_lo
  simp only [dview] at hl
  refine hw.inv fun b' st2 ⟨i2, z2, e, hz2, hb2, hst2⟩ => ?_
  obtain rfl : i = i2 := Option.some.inj e
  obtain rfl : z' = z2 := Option.some.inj (hz'.symm.trans hz2)
  have hs' : z'.state = z.state := by rw [hzz]
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans (hs'.symm.trans hb2))
  obtain rfl : st' = st2 := Option.some.inj (hst'.symm.trans hst2)
  omega

end ZlibNgF.Proof.DeflateFacts
