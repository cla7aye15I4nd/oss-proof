import ZlibNgF.Proof.«deflate.c.invariant»
import ZlibNgF.Proof.«deflate.c.init»

/-!
# The output potential of a deflate state (`ZlibNgF`)

`psi f st` bounds the bytes that `deflate` calls with flush `f` can still produce from state `st` without further
input. It is the potential of `GzWriteNeeds.CallOk`: a `deflate` call lowers it by at least the bytes it produces,
less `G` per input byte consumed and 5 when it fills the output; a `deflateParams` call likewise with `f = Z_BLOCK`
and nothing for a full output. It reads neither `level`, `strategy` nor the hash fields, which `deflateParams`
changes between calls. Its parts:

* `owed`: the pending bytes and the bytes of the bits waiting in `bi_buf`;
* `content`: `2^19` per lookahead byte (each byte becomes a symbol, a direct emission of `deflate_quick` or a window
  byte), 6 per window byte not yet emitted (`strstart - block_start`: a stored block of `n >= 1` bytes takes at most
  `n + 5`), `2^18` per tallied symbol and for the pending literal of `deflate_slow` (a non-final block flush has at
  least one symbol and adds at most `4 * lit_bufsize + 9 + 8 < 2^18` bytes), 16 for a zlib or plain gzip header not
  yet written (`INIT_STATE`, `GZIP_STATE`), `2^18` until `FINISH_STATE` (the last block, which may be empty), and the
  trailer of `4 * wrap` bytes while `wrap > 0`;
* `quickB`: the static block of `deflate_quick` with `Z_FIXED` (at most 24 bytes per header or end-of-block code):
  one close for an open block, an open and a close when there is lookahead and no open block, and for `Z_FINISH` on
  an open non-last block a close, an open of the last block and its close;
* `mark`: the flush marker (`zng_tr_align`: 10 bits, at most 2 bytes; the empty stored block of `Z_SYNC_FLUSH` and
  `Z_FULL_FLUSH`: 3 bits, the padding and 4 bytes, at most 5 bytes) that the next call with `f` emits after
  `block_done`: before `FINISH_STATE`, when bytes are pending (a call that empties them skips the `RANK` test) or the
  last flush ranks below `f` (a call that fills the output sets `last_flush` to -1, so a repeated flush emits another
  marker: that is the 5 of `CallOk` for a full output).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflatePsi
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv

/-- `RANK(f)` of `deflate.c` (`((f) * 2) - ((f) > 4 ? 9 : 0)`) in integers. -/
def rank (f : Int32) : Int := 2 * f.toInt - if 4 < f.toInt then 9 else 0

/-- The bytes of the flush marker of `f`. -/
def markK (f : Int32) : Nat :=
  if f = Z_PARTIAL_FLUSH then 2 else if f = Z_SYNC_FLUSH ∨ f = Z_FULL_FLUSH then 5 else 0

/-- The pending bytes and the bytes of the bits in `bi_buf`. -/
def owed (st : DeflateState) : Nat := st.pending.toNat + (st.bi_valid.toInt.toNat + 7) / 8

/-- The window bytes not yet emitted: `strstart - block_start`. -/
def span (st : DeflateState) : Nat := ((st.strstart.toNat : Int) - st.block_start.toInt).toNat

/-- The content not yet coded, the headers, the last block and the trailer. -/
def content (st : DeflateState) : Nat :=
  2 ^ 19 * st.lookahead.toNat + 6 * span st + 2 ^ 18 * (st.sym_next.toNat / 3) +
    (if st.match_available ≠ 0 then 2 ^ 18 else 0) +
    (if st.status = INIT_STATE ∨ st.status = GZIP_STATE then 16 else 0) +
    (if st.status ≠ FINISH_STATE then 2 ^ 18 else 0) + 4 * st.wrap.toInt.toNat

/-- The static block of `deflate_quick` with `Z_FIXED`. -/
def quickB (f : Int32) (st : DeflateState) : Nat :=
  if st.block_open ≠ 0 then (if f = Z_FINISH ∧ st.block_open = 1 then 96 else 32)
  else if st.lookahead ≠ 0 then 64 else 0

/-- The flush marker that the next call with `f` emits. -/
def mark (f : Int32) (st : DeflateState) : Nat :=
  if st.status ≠ FINISH_STATE ∧ (st.pending ≠ 0 ∨ rank st.last_flush < rank f) then markK f else 0

/-- **The potential** of state `st` for flush `f`. -/
def psi (f : Int32) (st : DeflateState) : Nat := content st + quickB f st + owed st + mark f st

/-- The raise allowed per input byte consumed. -/
def G : Nat := 2 ^ 20

theorem G_le : G ≤ 2 ^ 28 := by decide

/-! ## The bound -/

theorem markK_le (f : Int32) : markK f ≤ 5 := by unfold markK; split <;> [omega; split <;> omega]

theorem mark_le (f : Int32) (st : DeflateState) : mark f st ≤ 5 := by
  unfold mark; split
  · exact markK_le f
  · omega

theorem quickB_le (f : Int32) (st : DeflateState) : quickB f st ≤ 96 := by
  unfold quickB; split <;> [split <;> omega; split <;> omega]

/-- The window size of an invariant view is at most 65536. -/
theorem window_size_le {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore h s z b v al) : v.window_size.toNat ≤ 65536 := by
  obtain ⟨-, hw, hws, -⟩ := c.sizes
  rw [hws, DeflateInit.wbuf_toNat _ hw]; unfold DeflateAlloc.dWS; split <;> omega

/-- The parts of `psi` on an invariant state. -/
theorem parts_le {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (c : DCore h s z b (dview st) al) :
    st.lookahead.toNat ≤ 65536 ∧ span st ≤ 2 ^ 30 + 2 ^ 17 ∧ st.sym_next.toNat ≤ 3 * 32768 ∧
      owed st ≤ 4 * 32768 + 17 ∧ st.wrap.toInt.toNat ≤ 2 := by
  have hws := window_size_le c
  have hl := c.look
  have hb := c.bs_lo
  have hsy := c.syms_le
  have hbi := c.bits
  obtain ⟨-, -, -, hl1, hl2, -, -⟩ := c.sizes
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, poo, -, -, hpe⟩ := c.lay
  have hw := c.wrap
  simp only [dview] at hws hl hb hsy hbi hl1 hl2 hpe hw
  have hb0 : (0 : Int32).toInt = 0 := rfl
  have hb64 : (64 : Int32).toInt = 64 := rfl
  have hbi1 := Int32.le_iff_toInt_le.mp hbi.1
  have hbi2 := Int32.lt_iff_toInt_lt.mp hbi.2
  rw [hb0] at hbi1; rw [hb64] at hbi2
  refine ⟨by omega, ?_, by omega, ?_, ?_⟩
  · unfold span; omega
  · unfold owed; omega
  · rcases hw with e | e | e | e | e <;> rw [e] <;> decide

/-- **`psi` is at most `2^48`** on an invariant stream. -/
theorem psi_le {h : Heap} {s : StreamPtr} {b : Nat} {st : DeflateState} (f : Int32) (hv : DInv h s)
    (hs : DStateOf h s b st) : psi f st ≤ 2 ^ 48 := by
  obtain ⟨i, z, b', st', al, rfl, hz, hb, hst, -, c⟩ := hv
  obtain ⟨⟨z', ⟨i', ei, hz'⟩, hb''⟩, hst''⟩ := hs
  cases ei
  rw [hz] at hz'; cases hz'
  rw [hb] at hb''; cases hb''
  rw [hst] at hst''; cases hst''
  obtain ⟨h1, h2, h3, h4, -⟩ := parts_le c
  have hq := quickB_le f st
  have hm := mark_le f st
  have hw := (parts_le c).2.2.2.2
  unfold psi content
  split <;> split <;> split <;> omega

/-! ## Updates of the state -/

/-- `psi` in its parts. -/
theorem psi_eq (f : Int32) (st : DeflateState) : psi f st = content st + quickB f st + owed st + mark f st := rfl

/-- A call that keeps each part or lowers it, and lowers `owed` by `k` more, lowers `psi` by `k`. -/
theorem psi_step {f : Int32} {st st' : DeflateState} {k : Nat} (h1 : content st' ≤ content st)
    (h2 : quickB f st' ≤ quickB f st) (h3 : owed st' + k ≤ owed st) (h4 : mark f st' ≤ mark f st) :
    psi f st' + k ≤ psi f st := by
  unfold psi; omega

/-- `zng_tr_flush_bits` moves the complete bytes of `bi_buf` to the pending bytes: `owed` stays. -/
theorem owed_flush_bits (p b : Nat) (hb : b < 64) : (p + b / 8) + (b % 8 + 7) / 8 = p + (b + 7) / 8 := by
  omega

/-- After `s->last_flush = flush` with no pending bytes, no marker is owed for `flush`. -/
theorem mark_self {f : Int32} {st : DeflateState} (hp : st.pending = 0) (hl : st.last_flush = f) : mark f st = 0 := by
  unfold mark; rw [if_neg]; rintro ⟨-, h | h⟩
  · exact h hp
  · rw [hl] at h; exact Int.lt_irrefl _ h

/-- After `s->last_flush = -1` (a full output), the marker owed is at most 5 (the `K` of `CallOk`). -/
theorem mark_full (f : Int32) (st : DeflateState) : mark f st ≤ 5 := mark_le f st

/-- No marker for `Z_NO_FLUSH`, `Z_FINISH` and `Z_BLOCK`. -/
theorem mark_zero {f : Int32} (hf : f = Z_NO_FLUSH ∨ f = Z_FINISH ∨ f = Z_BLOCK) (st : DeflateState) :
    mark f st = 0 := by
  unfold mark markK
  rcases hf with rfl | rfl | rfl <;> simp [Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH]

/-- A literal or a match of `L >= 1` bytes tallied: `L` bytes move from the lookahead to the window span and one
symbol is added; `content` drops by at least `2^19 L - 6 L - 2^18`. -/
theorem content_tally {st st' : DeflateState} (L : Nat) (hL : 1 ≤ L)
    (e1 : st'.lookahead.toNat + L = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + L)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next.toNat = st.sym_next.toNat + 3) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' + 2 ^ 18 ≤ content st := by
  unfold content span
  rw [e4, e5, e6]
  have : (st.sym_next.toNat + 3) / 3 = st.sym_next.toNat / 3 + 1 := by omega
  rw [e3, this]
  split <;> split <;> split <;> omega

/-- The pending literal of `deflate_slow` set (`match_available = 1`, one byte from the lookahead to the span). -/
theorem content_pend_lit {st st' : DeflateState}
    (e1 : st'.lookahead.toNat + 1 = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + 1)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next = st.sym_next) (e4 : st.match_available = 0) (e4' : st'.match_available ≠ 0)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' + 2 ^ 18 ≤ content st := by
  unfold content span
  rw [e3, e5, e6, if_pos e4', if_neg (not_not.mpr e4)]
  split <;> split <;> omega

/-- A block flush (`FLUSH_BLOCK_ONLY`: `block_start = strstart`, no symbols after) of a block with at least one
symbol: `content` drops by `2^18`, which pays the block (at most `4 * lit_bufsize + 9` pending bytes from none, and
the bits). -/
theorem content_flush_block {st st' : DeflateState} (hs : 3 ≤ st.sym_next.toNat)
    (e1 : st'.lookahead = st.lookahead) (e2 : st'.block_start.toInt = st'.strstart.toNat)
    (e3 : st'.sym_next = 0) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' + 2 ^ 18 ≤ content st := by
  unfold content span
  rw [e1, e3, e4, e5, e6, e2]
  have : (st.sym_next.toNat / 3) ≥ 1 := by omega
  simp only [UInt32.toNat_zero, Nat.zero_div, Nat.mul_zero, Int.sub_self, Int.toNat_zero]
  split <;> split <;> split <;> omega

/-- `s->status = FINISH_STATE` from `BUSY_STATE`: `content` drops by `2^18`, which pays the last block. -/
theorem content_finish {st st' : DeflateState} (hb : st.status ≠ FINISH_STATE) (e0 : st'.status = FINISH_STATE)
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = span st) (e3 : st'.sym_next = st.sym_next)
    (e4 : st'.match_available = st.match_available) (e6 : st'.wrap = st.wrap) :
    content st' + 2 ^ 18 ≤ content st := by
  unfold content
  rw [e1, e2, e3, e4, e6, e0, if_pos hb]
  simp only [ne_eq, not_true_eq_false, if_false]
  have h1 : ¬ (FINISH_STATE = INIT_STATE ∨ FINISH_STATE = GZIP_STATE) := by decide
  rw [if_neg h1]
  split <;> omega

/-- `s->wrap = -s->wrap` after the trailer: `content` drops by `4 * wrap`, the trailer's bytes. -/
theorem content_wrap {st st' : DeflateState} (hw : 0 < st.wrap.toInt) (e0 : st'.wrap.toInt = -st.wrap.toInt)
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = span st) (e3 : st'.sym_next = st.sym_next)
    (e4 : st'.match_available = st.match_available) (e5 : st'.status = st.status) :
    content st' + 4 * st.wrap.toInt.toNat = content st := by
  unfold content
  rw [e1, e2, e3, e4, e5, e0]
  omega

/-- The lookahead grows by `n` input bytes (`read_buf`): `content` and `quickB` grow by at most `G n`. -/
theorem psi_read {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat = st.lookahead.toNat + n) (e2 : span st' = span st)
    (e3 : st'.sym_next = st.sym_next) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) (e9 : mark f st' = mark f st) : psi f st' ≤ psi f st + G * n := by
  unfold psi content quickB G
  rw [e2, e3, e4, e5, e6, e7, e8, e9, e1]
  by_cases hn : n = 0
  · subst hn; simp only [Nat.add_zero, Nat.mul_zero]; omega
  · split <;> split <;> split <;> split <;> (try split) <;> (try split) <;> omega

end ZlibNgF.Proof.DeflatePsi
