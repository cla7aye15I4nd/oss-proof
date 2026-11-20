import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«deflate.c.init»
import ZlibNgF.Proof.«deflate.c.psi»

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
  strategy (`DWork`: the invariant, stated with the bits of `bi_buf` apart; the same as `DInv`), given room after the pending
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

/-- The working state of a strategy: the invariant's clauses with `bi_buf`'s up to 63 bits stated apart (the
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
(`sym_next < sym_end`: every strategy flushes a full buffer before it returns); at level 0 (`deflate_stored`, which
reads `window + block_start` and writes `pending_buf` over `sym_buf`) `block_start` is not negative and there are no
symbols and no lookahead; at level 1 with `Z_FIXED` (`deflate_quick` with `static_emit`, which never tallies and
writes `pending_buf` over `sym_buf`) there are no symbols; with `block_start == strstart` there are no symbols (every
tallied symbol moved `strstart` past `block_start`, `FLUSH_BLOCK` resets both); 8 or more bits wait in `bi_buf` only
at level 1 with `Z_FIXED` and with lookahead (`deflate_quick` with `static_emit` returns `need_more` with up to 63
bits only for `Z_NO_FLUSH`, which never lets the lookahead fall to 0; every other return of a strategy and of
`deflate` with bits written follows `flush_pending`, which leaves fewer than 8; so `zng_tr_flush_block` is called
with fewer than 8 bits, and `deflateParams` and `deflateSetDictionary`, which require no lookahead, see fewer than
8). The range of `block_start` is the invariant's (`DCore.bstart`, `DCore.bs_lo`). -/
def SymsOk (st : DeflateState) : Prop :=
  st.sym_next < st.sym_end ∧
    (st.level = 0 → 0 ≤ st.block_start ∧ st.sym_next = 0 ∧ st.lookahead = 0) ∧
    (st.level = 1 → st.strategy = Z_FIXED → st.sym_next = 0) ∧
    ((st.strstart.toNat : Int) = st.block_start.toInt → st.sym_next = 0) ∧
    (8 ≤ st.bi_valid → st.level = 1 ∧ st.strategy = Z_FIXED ∧ st.lookahead ≠ 0)

/-- The dispatch of `deflate` to the strategy of a level from `configuration_table`: that level, and a strategy
other than `Z_HUFFMAN_ONLY` and `Z_RLE`. -/
def TableAt (lo hi : Int32) (st : DeflateState) : Prop :=
  lo ≤ st.level ∧ st.level ≤ hi ∧ st.strategy ≠ Z_HUFFMAN_ONLY ∧ st.strategy ≠ Z_RLE

/-- The lazy-match fields that `deflate_slow` keeps across calls (`prev_length`, `match_start`, `match_available`):
a pending match (`prev_length >= STD_MIN_MATCH`) is at most `STD_MAX_MATCH` long, fits in the lookahead plus the byte
before `strstart`, and starts at `match_start`, behind `strstart - 1` by at most `MAX_DIST`; a pending literal
(`match_available`) is the byte before `strstart`, after `block_start`; outside the levels of `deflate_slow` (and
after a reset, `last_flush == -2`) there is neither. -/
def LazyOk (st : DeflateState) : Prop :=
  (3 ≤ st.prev_length → st.prev_length.toNat ≤ 258 ∧ st.prev_length.toNat ≤ st.lookahead.toNat + 1 ∧
      st.match_start.toNat + 1 < st.strstart.toNat ∧
      st.strstart.toNat - 1 - st.match_start.toNat ≤ (MAX_DIST st).toNat) ∧
    (st.match_available ≠ 0 → 1 ≤ st.strstart.toNat ∧ st.block_start.toInt < st.strstart.toNat) ∧
    (¬ TableAt 7 9 st → st.prev_length < 3 ∧ st.match_available = 0) ∧
    (st.last_flush = -2 → st.prev_length < 3 ∧ st.match_available = 0)

/-- The fields that a strategy reads back unchanged: it never writes them; outside the levels of `deflate_slow`,
`prev_length` does not grow (`fill_window` may clear it) and `match_available` is kept. -/
def StratKeeps (st st' : DeflateState) : Prop :=
  st'.status = st.status ∧ st'.wrap = st.wrap ∧ st'.gzhead = st.gzhead ∧ st'.gzindex = st.gzindex ∧
    st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.last_flush = st.last_flush ∧
    (¬ TableAt 7 9 st → st'.prev_length ≤ st.prev_length ∧ st'.match_available = st.match_available)

/-- The state in which `deflate` calls a strategy: the invariant, the CRC tables, valid and set buffers, a valid
`flush` (`Z_NO_FLUSH` .. `Z_BLOCK`), no pending bytes (`deflate` flushed them, or returned), the header written
(`status` is `BUSY_STATE` or `FINISH_STATE`, so the invariant allows tallied symbols), `SymsOk`, `LazyOk`, and
`last_flush` a flush value (`deflate` sets `s->last_flush = flush` before it dispatches). -/
def StratPre (h : Heap) (s : StreamPtr) (flush : Int32) : Prop :=
  DInv h s ∧ CrcGlobals h ∧ DStreamIO h s ∧ DBufsSet h s ∧ 0 ≤ flush ∧ flush ≤ 5 ∧
    ∃ b st, DStateIs h s b st ∧ st.pending = 0 ∧ (st.status = BUSY_STATE ∨ st.status = FINISH_STATE) ∧ SymsOk st ∧
      LazyOk st ∧ 0 ≤ st.last_flush

/-- The output buffer of stream `i` in `H` is a tail of its output buffer in `h`. -/
def OutTail (h H : Heap) (i : Nat) : Prop :=
  ∃ z0 z ob oo k, h.streams i = some z0 ∧ H.streams i = some z ∧ z0.next_out = .ref (.heap ob) oo ∧
    z.next_out = .ref (.heap ob) (oo + k) ∧ z.avail_out.toNat + k = z0.avail_out.toNat

/-- The input of stream `i` in `H` is a tail of its input in `h`: `next_in` advanced by the `k` bytes taken (a `NULL`
`next_in` stays, with none taken). -/
def InTail (h H : Heap) (i : Nat) : Prop :=
  ∃ z0 z k, h.streams i = some z0 ∧ H.streams i = some z ∧ z.avail_in.toNat + k = z0.avail_in.toNat ∧
    (match z0.next_in with
     | .null => k = 0 ∧ z.next_in = .null
     | .ref r o => z.next_in = .ref r (o + k))

/-- `InTail` of a heap whose stream record has the input fields of `h`'s. -/
theorem InTail.refl {h H : Heap} {i : Nat} {z z' : ZStream} (hz : h.streams i = some z) (hz' : H.streams i = some z')
    (e1 : z'.next_in = z.next_in) (e2 : z'.avail_in = z.avail_in) : InTail h H i := by
  refine ⟨z, z', 0, hz, hz', by rw [e2]; rfl, ?_⟩
  cases hn : z.next_in with
  | null => exact ⟨rfl, by rw [e1, hn]⟩
  | ref r o => rw [e1, hn]; rfl

/-- `InTail` composes. -/
theorem InTail.trans {h H H' : Heap} {i : Nat} (A : InTail h H i) (B : InTail H H' i) : InTail h H' i := by
  obtain ⟨z0, z1, k, h0, h1, ek, m1⟩ := A
  obtain ⟨z1', z2, k', h1', h2, ek', m2⟩ := B
  obtain rfl := Option.some.inj (h1.symm.trans h1')
  refine ⟨z0, z2, k + k', h0, h2, by omega, ?_⟩
  revert m1
  cases z0.next_in with
  | null =>
    rintro ⟨rfl, e1⟩
    rw [e1] at m2
    obtain ⟨rfl, e2⟩ := m2
    exact ⟨rfl, e2⟩
  | ref r o =>
    intro e1
    rw [e1] at m2
    simp only [] at m2 ⊢
    rw [m2, Nat.add_assoc]

/-- `InTail` after a step that keeps the input fields of the stream. -/
theorem InTail.keep {h H H' : Heap} {i : Nat} {z z' : ZStream} (A : InTail h H i) (hz : H.streams i = some z)
    (hz' : H'.streams i = some z') (e1 : z'.next_in = z.next_in) (e2 : z'.avail_in = z.avail_in) : InTail h H' i :=
  A.trans (InTail.refl hz hz' e1 e2)

/-- The input fields of `H` are those of a tail of `h`'s: `avail_in` does not grow. -/
theorem InTail.le {h H : Heap} {i : Nat} (A : InTail h H i) {z0 z : ZStream} (h0 : h.streams i = some z0)
    (h1 : H.streams i = some z) : z.avail_in.toNat ≤ z0.avail_in.toNat := by
  obtain ⟨z0', z', k, h0', h1', ek, -⟩ := A
  obtain rfl := Option.some.inj (h0.symm.trans h0')
  obtain rfl := Option.some.inj (h1.symm.trans h1')
  omega

/-- The allowance of a strategy call that returns `bs` in the potential: `2^18` for the last block after
`finish_started` / `finish_done` (`deflate` then sets `s->status = FINISH_STATE`, which releases it:
`DeflatePsi.content_finish`), else none. -/
def finSlack (bs : BlockState) : Nat := if bs = .finish_started ∨ bs = .finish_done then 2 ^ 18 else 0

/-- The potential of a strategy call with `flush` that returns `bs` (`DeflatePsi.PsiAccF`): from `h` to `h'`,
`psiS flush` drops by the bytes produced, less `G` per input byte consumed and `finSlack bs`. Only the call's own
flush: with `Z_FIXED` at level 1, `deflate_quick` may raise `quickB f` for another `f` (closing the open block for
`Z_FINISH` raises `quickB Z_NO_FLUSH` from 32 to 64 when lookahead is left). -/
def PsiPost (h : Heap) (s : StreamPtr) (flush : Int32) (bs : BlockState) (h' : Heap) : Prop :=
  ∀ i b, s = some i → StateBlock h s b → DeflatePsi.PsiAccF flush (finSlack bs) h h' i b

/-- What a strategy call with `flush` leaves: the invariant, valid and set buffers, a change of the stream record, the
stream's block and the output buffer only, the output buffer after a tail of the one before (`OutTail`), the stream's
state block kept, the input a tail of the one before (`InTail`), all input consumed or the output full after
`need_more` / `block_done` (each `need_more` follows `fill_window` under `Z_NO_FLUSH`, which leaves a full lookahead
or no input, or a full output; each `block_done` follows an empty lookahead after `fill_window`, or, in
`deflate_stored`, a test of `avail_in == 0`), `finish_started` / `finish_done` only for `Z_FINISH`, progress after
`need_more` / `finish_started` under `Z_FINISH` from an output with room (input consumed or output produced: each
such return follows a full output, or in `deflate_stored` a stored block through `pending_buf`), no pending bytes
after `block_done` / `finish_done`; `SymsOk` again, the
fields of `StratKeeps` unchanged, no symbols after a call with a flush that leaves output room (every such return
goes through `FLUSH_BLOCK`, or the strategy never tallies; `deflate_slow` returns on a full output right after a
tally), no symbols after `block_done` (it follows `FLUSH_BLOCK` or an empty symbol buffer), and no symbols and no
lookahead after `finish_started` / `finish_done`; `LazyOk` kept, and no pending literal after `block_done`
(`deflate_slow` tallies it before it leaves its loop); the potential (`PsiPost`); and `block_done` only with a flush
other than `Z_NO_FLUSH` and `Z_FINISH`, with all input consumed (each `block_done` follows an empty lookahead after
`fill_window` under a flush, or in `deflate_stored` a test of `flush != Z_NO_FLUSH && flush != Z_FINISH &&
avail_in == 0`). -/
def StratPost (h : Heap) (s : StreamPtr) (flush : Int32) (bs : BlockState) (h' : Heap) : Prop :=
  DInv h' s ∧ DStreamIO h' s ∧ DBufsSet h' s ∧ DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧
    (∀ i, s = some i → OutTail h h' i) ∧ (∀ b, StateBlock h s b → StateBlock h' s b) ∧
    (∀ i, s = some i → InTail h h' i) ∧
    (bs = .need_more ∨ bs = .block_done → ∀ z', StreamAt h' s z' → z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
    (bs = .finish_started ∨ bs = .finish_done → flush = Z_FINISH) ∧
    (flush = Z_FINISH → bs = .need_more ∨ bs = .finish_started → ∀ z z', StreamAt h s z → StreamAt h' s z' →
      z.avail_out ≠ 0 → z'.avail_in < z.avail_in ∨ z'.avail_out < z.avail_out) ∧
    (bs = .block_done ∨ bs = .finish_done → ∃ b st, DStateIs h' s b st ∧ st.pending = 0) ∧
    (∀ b st st', DStateIs h s b st → DStateIs h' s b st' → SymsOk st' ∧ StratKeeps st st' ∧
      (flush ≠ Z_NO_FLUSH → (∀ z', StreamAt h' s z' → z'.avail_out ≠ 0) → st'.sym_next = 0) ∧
      (bs = .finish_started ∨ bs = .finish_done → st'.sym_next = 0 ∧ st'.lookahead = 0) ∧
      (bs = .block_done → st'.sym_next = 0) ∧
      (LazyOk st → LazyOk st' ∧ (bs = .block_done → st'.match_available = 0))) ∧
    PsiPost h s flush bs h' ∧
    (bs = .block_done → flush ≠ Z_NO_FLUSH ∧ flush ≠ Z_FINISH ∧ ∀ z', StreamAt h' s z' → z'.avail_in = 0)

/-- A strategy `f` that `deflate` dispatches to on states with `dispatch`: from `StratPre` and `dispatch`, no fault
and `StratPost`. -/
def StratOkP (dispatch : DeflateState → Prop) (f : StatePtr → Int32 → M BlockState) : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (b : Nat) (flush : Int32), StratPre h s flush → StateBlock h s b →
    (∀ b' st, DStateIs h s b' st → dispatch st) →
    ∃ bs h', C.run (f (some b) flush) h = .ok (bs, h') ∧ StratPost h s flush bs h'

/-! ## Hash chains -/

/-- Entry `k` of the `Pos` array at byte offset `o` of `d` (`posLoad`: two bytes, little endian). -/
def posAt (d : Array UInt8) (o k : Nat) : Nat := d[o + 2 * k]!.toNat + 256 * d[o + 2 * k + 1]!.toNat

/-- The bound of the positions in the hash chains: `strstart`, or `strstart + lookahead` at the medium levels 3..6
(`deflate_medium` hashes the start of `next_match` before its emission catches up, and may return `need_more` with it
inserted; every inserted `p` has `p + 4 <= strstart + lookahead` there). A level change out of 3..6 goes through
`lookahead == 0` (`deflateParams` flushes and checks it, or `last_flush == -2`). -/
def chainLim (st : DeflateState) : Nat :=
  st.strstart.toNat + if 3 ≤ st.level ∧ st.level ≤ 6 then st.lookahead.toNat else 0

/-- The hash chains of state `st` (block `b`, bytes `d`). This holds unless the level is 1 (`deflate_quick` inserts
into `head` only, so `prev` goes stale; leaving level 1 is a stale-chain switch of `deflateParams`) or the
configuration is `HASHLESS`. There is a set `I` of positions with (C1) `0 < p < chainLim st` for each `p ∈ I`;
(C2) every nonzero `head[k]` is in `I`; (C3) for `p ∈ I` with `p > strstart - w_size`, `prev[p & w_mask]` is 0 or
in `I`. -/
def ChainOk (b : Nat) (d : Array UInt8) (st : DeflateState) : Prop :=
  st.level ≠ 1 → HASHLESS st.level st.strategy = false →
  ∃ (I : Nat → Prop) (ho po : Nat), st.head = .val (.ref (.heap b) ho) ∧ st.prev = .val (.ref (.heap b) po) ∧
    (∀ p, I p → 0 < p ∧ p < chainLim st) ∧
    (∀ k, k < 65536 → posAt d ho k ≠ 0 → I (posAt d ho k)) ∧
    (∀ p, I p → st.strstart.toNat < p + st.w_size.toNat →
      posAt d po (p % st.w_size.toNat) = 0 ∨ I (posAt d po (p % st.w_size.toNat)))

/-- `StratOkP` for a strategy that walks the hash chains: `ChainOk` of the state on entry gives `ChainOk` on exit. -/
def StratOkC (dispatch : DeflateState → Prop) (f : StatePtr → Int32 → M BlockState) : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (b : Nat) (flush : Int32), StratPre h s flush → StateBlock h s b →
    (∀ b' st, DStateIs h s b' st → dispatch st) →
    (∀ st d, DStateIs h s b st → h.bytes b = some d → ChainOk b d st) →
    ∃ bs h', C.run (f (some b) flush) h = .ok (bs, h') ∧ StratPost h s flush bs h' ∧
      ∀ st d, DStateIs h' s b st → h'.bytes b = some d → ChainOk b d st

/-- The strategies, one field each, with the facts of `deflate`'s dispatch (`level == 0 ? deflate_stored :
strategy == Z_HUFFMAN_ONLY ? deflate_huff : strategy == Z_RLE ? deflate_rle : configuration_table[level].func`;
the table: 1 `deflate_quick`, 2 `deflate_fast`, 3-4 `deflate_medium`, 5-6 `deflate_medium_fizzle`, 7-9
`deflate_slow`). The strategies that walk the hash chains (`deflate_fast`, `deflate_medium*`, `deflate_slow`) also
keep `ChainOk` (`StratOkC`); for the others it is vacuous (`HASHLESS`, or level 1). -/
structure StrategyFacts : Prop where
  stored : StratOkP (fun st => st.level = 0) ZlibNg.DeflateStored.deflate_stored
  quick : StratOkP (TableAt 1 1) ZlibNg.DeflateQuick.deflate_quick
  fast : StratOkC (TableAt 2 2) ZlibNg.DeflateFast.deflate_fast
  medium : StratOkC (TableAt 3 4) ZlibNg.DeflateMedium.deflate_medium
  medium_fizzle : StratOkC (TableAt 5 6) ZlibNg.DeflateMedium.deflate_medium_fizzle
  slow : StratOkC (TableAt 7 9) ZlibNg.DeflateSlow.deflate_slow
  huff : StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_HUFFMAN_ONLY) ZlibNg.DeflateHuff.deflate_huff
  rle : StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_RLE) ZlibNg.DeflateRle.deflate_rle

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

/-- The invariant of stream `s`, stated as the clauses of `DCore` on the state with `block_start` at `strstart`, and
`block_start` between `-(2^30 + 2^16)` and `strstart` (the same as `DInv`: `DInvW.of_inv`, `DInvW.inv`). It is the
state inside the insertion loop of `deflateSetDictionary` and the state that `fill_window` takes and leaves. -/
def DInvW (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ DCore h s z b (dview { st with block_start := st.strstart.toInt32 }) al ∧
    st.block_start.toInt ≤ st.strstart.toNat ∧ -(2 ^ 30 + 2 ^ 16) ≤ st.block_start.toInt

/-- What `fill_window` leaves: `DInvW` and a readable input; only the stream record (`next_in`, `avail_in`,
`total_in`, `adler`) and the stream's block change; `avail_in` does not grow and drops when `lookahead` changes, and
`lookahead` grows by at most the input taken (the window gains only input bytes); `strstart - block_start` does not grow and
becomes 0 only if it was 0 (a slide lowers both by `slide_len`, or, patch 0018, only `strstart` when `block_start`
would fall below `-(2^30 + 2^16)`, which leaves a gap above `2^30`); at the end the lookahead is full or the input empty; the state fields that the
callers read back (`wrap`, `status`, `gzhead`, `level`, `strategy`, the function pointers, `sym_next`, `gzindex`,
`last_flush`, `bi_valid`) kept; the lazy-match fields: a `prev_length` of 3 or more after is the one before, with the
same distance `strstart - match_start` and a `match_start` not above the one before (a slide lowers `strstart` and
`match_start` together, or sets `match_start` and `prev_length` to 0), `prev_length` does not grow, `match_available`
kept; the lookahead does not drop, and a `strstart` of 1 or more stays so (a slide leaves at least `MAX_DIST`); the input
after a tail of the one before (`read_buf`: `next_in += len; avail_in -= len`). -/
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
    (st'.strstart.toNat : Int) - st'.block_start.toInt ≤ (st.strstart.toNat : Int) - st.block_start.toInt ∧
    ((st'.strstart.toNat : Int) = st'.block_start.toInt → (st.strstart.toNat : Int) = st.block_start.toInt) ∧
    (262 ≤ st'.lookahead.toNat ∨ z'.avail_in = 0) ∧
    st'.wrap = st.wrap ∧ st'.status = st.status ∧ st'.gzhead = st.gzhead ∧ st'.level = st.level ∧
    st'.strategy = st.strategy ∧ st'.longest_match = st.longest_match ∧ st'.insert_batch = st.insert_batch ∧
    st'.sym_next = st.sym_next ∧ st'.gzindex = st.gzindex ∧ st'.last_flush = st.last_flush ∧
    st'.bi_valid = st.bi_valid ∧
    (3 ≤ st'.prev_length → st'.prev_length = st.prev_length ∧
      (st.strstart.toNat : Int) - st.match_start.toNat = (st'.strstart.toNat : Int) - st'.match_start.toNat ∧
      st'.match_start ≤ st.match_start) ∧
    st'.prev_length ≤ st.prev_length ∧ st'.match_available = st.match_available ∧
    st.lookahead.toNat ≤ st'.lookahead.toNat ∧ (1 ≤ st.strstart.toNat → 1 ≤ st'.strstart.toNat) ∧
    (∀ i, s = some i → InTail h h' i)

/-- The window functions that `deflateSetDictionary` (and the strategies) call, one field each, to be proved about
the translated C code: `fill_window` from `DInvW` (the invariant, or the state inside `deflateSetDictionary`'s
insertion loop), a readable input (the CRC tables when it computes a CRC-32) and `lookahead < MIN_LOOKAHEAD` (every
caller's condition) and that it keeps the hash chains (`ChainOk`) there, and the `insert_batch` functions of `lm_set_level` over `n >= 1` positions from `str` whose
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
  fill_window_chain : ∀ (h h' : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) (d : Array UInt8), DInv h s →
    DStateIs h s b st → h.bytes b = some d → DInput h s → (st.wrap = 2 → CrcGlobals h) → st.lookahead.toNat < 262 →
    ChainOk b d st → C.run (ZlibNg.Deflate.fill_window (some b)) h = .ok ((), h') →
    ∀ st' d', DStateIs h' s b st' → h'.bytes b = some d' → ChainOk b d' st'

/-! ## Interface lemmas -/

/-- The invariant's pending range as `PendRoom` with no bytes more. -/
theorem pendRoom_of_core {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (c : DCore h s z b (dview st) al) : PendRoom b st 0 (4 * st.lit_bufsize.toNat + 9) := by
  obtain ⟨_, _, _, _, pbo, _, -, -, -, hpb, -, -, -, -, -, poo, hpo, -, hpe⟩ := c.lay
  exact ⟨pbo, poo, hpb, hpo, by simp only [dview] at hpe; omega⟩

/-- An invariant stream is in the working state. -/
theorem DWork.of_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) : DWork h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have b0 : 0 ≤ st.bi_valid := c.bits.1
  have b64 : st.bi_valid < 64 := c.bits.2
  have e0 : (0 : Int32).toInt.toNat / 8 = 0 := rfl
  obtain ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  refine ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, b64,
    { c with
      bits := ⟨Int32.le_refl _, show (0 : Int32) < 64 by decide⟩
      lay := ⟨d, wo, po, ho, pbo, hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo, hpo, hpoo, by
        simp only [dview] at hpe ⊢; rw [e0]; omega⟩
      psym := fun hn => by
        obtain ⟨pbo1, poo1, hp1, ho1, hq⟩ := c.psym hn
        exact ⟨pbo1, poo1, hp1, ho1, by simp only [dview] at hq ⊢; rw [e0]; omega⟩ },
    ⟨pbo, poo, hpb, hpo, hpe⟩, fun hn => ?_⟩
  obtain ⟨pbo1, poo1, hp1, ho1, hq⟩ := c.psym hn
  exact ⟨pbo1, poo1, hp1, ho1, hq⟩

/-- The working state is the invariant (the invariant allows up to 63 bits in `bi_buf`). -/
theorem DWork.inv' {h : Heap} {s : StreamPtr} (hw : DWork h s) : DInv h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, b64, c, ⟨pbo, poo, hpb, hpo, hq⟩, hps⟩ := hw
  obtain ⟨d, wo, po, ho, pbo', hd, hw, hp, hh, hpb', h1, h2, h3, h4, hsb, poo', hpo', hpoo, -⟩ := c.lay
  have ea := hpb'.symm.trans hpb
  obtain rfl : pbo' = pbo := by injection ea with e1; injection e1
  have eb := hpo'.symm.trans hpo
  obtain rfl : poo' = poo := by injection eb with e1; injection e1
  exact ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with
    bits := ⟨b0, b64⟩
    lay := ⟨d, wo, po, ho, pbo', hd, hw, hp, hh, hpb, h1, h2, h3, h4, hsb, poo', hpo, hpoo, hq⟩
    psym := fun hn => hps hn }⟩

/-- A working state with fewer than 8 bits in `bi_buf` is invariant (`DWork.inv'`; the bound is not needed). -/
theorem DWork.inv {h : Heap} {s : StreamPtr} (hw : DWork h s)
    (_h8 : ∀ b st, DStateIs h s b st → st.bi_valid < 8) : DInv h s := DWork.inv' hw

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
    bs_lo := by simp only [dview]; rw [e]; omega }, hb1, hb2⟩

/-- `DInvW` is the invariant. -/
theorem DInvW.inv {h : Heap} {s : StreamPtr} (hw : DInvW h s) : DInv h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c, h1, h2⟩ := hw
  exact ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with
    bstart := h1
    bs_lo := h2 }⟩

/-- `fill_window` from an invariant stream leaves the invariant. -/
theorem FillPost.inv {h h' : Heap} {s : StreamPtr} (_hv : DInv h s) (hp : FillPost h h' s) : DInv h' s :=
  hp.1.inv

/-- `TableAt` reads the state through `level` and `strategy`. -/
theorem tableAt_congr {lo hi : Int32} {st st' : DeflateState} (e1 : st'.level = st.level)
    (e2 : st'.strategy = st.strategy) : TableAt lo hi st' ↔ TableAt lo hi st := by
  unfold TableAt; rw [e1, e2]

/-- No pending match and no pending literal: `LazyOk`. -/
theorem LazyOk.of_clear {st : DeflateState} (h1 : st.prev_length < 3) (h2 : st.match_available = 0) : LazyOk st :=
  ⟨fun e => absurd e (UInt32.not_le.mpr h1), fun e => absurd h2 e, fun _ => ⟨h1, h2⟩, fun _ => ⟨h1, h2⟩⟩

/-- Outside the levels of `deflate_slow` there is no pending match and no pending literal. -/
theorem LazyOk.clear {st : DeflateState} (L : LazyOk st) (ht : ¬ TableAt 7 9 st) :
    st.prev_length < 3 ∧ st.match_available = 0 :=
  L.2.2.1 ht

/-- Outside the levels of `deflate_slow`, `StratKeeps` keeps `LazyOk`, with no pending literal. -/
theorem StratKeeps.lazy {st st' : DeflateState} (K : StratKeeps st st') (L : LazyOk st) (ht : ¬ TableAt 7 9 st) :
    LazyOk st' ∧ st'.match_available = 0 := by
  obtain ⟨c1, c2⟩ := L.clear ht
  obtain ⟨k1, k2⟩ := K.2.2.2.2.2.2.2 ht
  have h1 : st'.prev_length < 3 := UInt32.lt_of_le_of_lt k1 c1
  have h2 : st'.match_available = 0 := k2.trans c2
  exact ⟨LazyOk.of_clear h1 h2, h2⟩

/-- `LazyOk` reads the state through `prev_length`, `lookahead`, `match_start`, `strstart`, `w_size`,
`match_available`, `block_start`, `level`, `strategy`, `last_flush`. -/
theorem LazyOk.of_eq {st st' : DeflateState} (L : LazyOk st) (e1 : st'.prev_length = st.prev_length)
    (e2 : st'.lookahead = st.lookahead) (e3 : st'.match_start = st.match_start) (e4 : st'.strstart = st.strstart)
    (e5 : st'.w_size = st.w_size) (e6 : st'.match_available = st.match_available)
    (e7 : st'.block_start = st.block_start) (e8 : st'.level = st.level) (e9 : st'.strategy = st.strategy)
    (e10 : st'.last_flush = st.last_flush) : LazyOk st' := by
  unfold LazyOk MAX_DIST TableAt at *
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]; exact L

end ZlibNgF.Proof.DeflateFacts
