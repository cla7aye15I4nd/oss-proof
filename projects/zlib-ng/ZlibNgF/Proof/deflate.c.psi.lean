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
  else if st.lookahead.toNat ≠ 0 then 64 else 0

/-- The flush marker that the next call with `f` emits. -/
def mark (f : Int32) (st : DeflateState) : Nat :=
  if st.status ≠ FINISH_STATE ∧ (st.pending ≠ 0 ∨ rank st.last_flush < rank f) then markK f else 0

/-- **The potential** of state `st` for flush `f`. -/
def psi (f : Int32) (st : DeflateState) : Nat := content st + quickB f st + owed st + mark f st

/-- The raise allowed per input byte consumed. -/
def G : Nat := 2 ^ 20

theorem G_le : G ≤ 2 ^ 28 := by decide

/-! ## The bound -/

theorem markK_le (f : Int32) : markK f ≤ 5 := by unfold markK; split <;> (try split) <;> omega

theorem mark_le (f : Int32) (st : DeflateState) : mark f st ≤ 5 := by
  unfold mark; split
  · exact markK_le f
  · omega

theorem quickB_le (f : Int32) (st : DeflateState) : quickB f st ≤ 96 := by
  unfold quickB; split <;> split <;> omega

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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpe⟩ := c.lay
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
theorem owed_flush_bits (p b : Nat) : (p + b / 8) + (b % 8 + 7) / 8 = p + (b + 7) / 8 := by
  omega

/-- After `s->last_flush = flush` with no pending bytes, no marker is owed for `flush`. -/
theorem mark_self {f : Int32} {st : DeflateState} (hp : st.pending = 0) (hl : st.last_flush = f) : mark f st = 0 := by
  unfold mark
  refine ite_eq_right ?_
  rintro ⟨-, h | h⟩
  · exact h hp
  · rw [hl] at h; exact Int.lt_irrefl _ h

/-- After `s->last_flush = -1` (a full output), the marker owed is at most 5 (the `K` of `CallOk`). -/
theorem mark_full (f : Int32) (st : DeflateState) : mark f st ≤ 5 := mark_le f st

/-- No marker for `Z_NO_FLUSH`, `Z_FINISH` and `Z_BLOCK`. -/
theorem mark_zero {f : Int32} (hf : f = Z_NO_FLUSH ∨ f = Z_FINISH ∨ f = Z_BLOCK) (st : DeflateState) :
    mark f st = 0 := by
  unfold mark markK
  rcases hf with rfl | rfl | rfl <;> simp [Z_NO_FLUSH, Z_FINISH, Z_BLOCK, Z_PARTIAL_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH]

/-- `L` bytes move from the lookahead to the window span (a direct emission of `deflate_quick` with `Z_FIXED`):
`content` drops by `2^19 L - 6 L`, which pays the emitted codes. -/
theorem content_move {st st' : DeflateState} (L : Nat)
    (e1 : st'.lookahead.toNat + L = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + L)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next = st.sym_next) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' + 2 ^ 19 * L ≤ content st + 6 * L := by
  unfold content span
  rw [e3, e4, e5, e6]
  omega

/-- A literal or a match of `L` bytes tallied: `L` bytes move from the lookahead to the window span and one symbol
is added. -/
theorem content_tally {st st' : DeflateState} (L : Nat)
    (e1 : st'.lookahead.toNat + L = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + L)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next.toNat = st.sym_next.toNat + 3) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) :
    content st' + 2 ^ 19 * L ≤ content st + 6 * L + 2 ^ 18 := by
  unfold content span
  rw [e4, e5, e6]
  have : (st.sym_next.toNat + 3) / 3 = st.sym_next.toNat / 3 + 1 := by omega
  rw [e3, this]
  omega

/-- The pending literal of `deflate_slow` set (`match_available = 1`, one byte from the lookahead to the span). -/
theorem content_pend_lit {st st' : DeflateState}
    (e1 : st'.lookahead.toNat + 1 = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + 1)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next = st.sym_next) (e4 : st.match_available = 0) (e4' : st'.match_available ≠ 0)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' + 2 ^ 19 ≤ content st + 6 + 2 ^ 18 := by
  unfold content span
  have m1 : (if st'.match_available ≠ 0 then (2 : Nat) ^ 18 else 0) = 2 ^ 18 := ite_eq_left e4'
  have m0 : (if st.match_available ≠ 0 then (2 : Nat) ^ 18 else 0) = 0 := ite_eq_right (fun h => h e4)
  rw [e3, e5, e6, m1, m0]
  omega

/-- The pending literal of `deflate_slow` tallied (`match_available = 0`, one symbol added). -/
theorem content_tally_pend {st st' : DeflateState}
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = span st)
    (e3 : st'.sym_next.toNat = st.sym_next.toNat + 3) (e4 : st.match_available ≠ 0) (e4' : st'.match_available = 0)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) : content st' ≤ content st := by
  unfold content
  have m1 : (if st.match_available ≠ 0 then (2 : Nat) ^ 18 else 0) = 2 ^ 18 := ite_eq_left e4
  have m0 : (if st'.match_available ≠ 0 then (2 : Nat) ^ 18 else 0) = 0 := ite_eq_right (fun h => h e4')
  have : (st.sym_next.toNat + 3) / 3 = st.sym_next.toNat / 3 + 1 := by omega
  rw [e1, e2, e3, e5, e6, m1, m0, this]
  omega

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
  have f1 : (if st.status ≠ FINISH_STATE then (2 : Nat) ^ 18 else 0) = 2 ^ 18 := ite_eq_left hb
  have f2 : (if FINISH_STATE ≠ FINISH_STATE then (2 : Nat) ^ 18 else 0) = 0 := ite_eq_right (fun h => h rfl)
  have f3 : (if FINISH_STATE = INIT_STATE ∨ FINISH_STATE = GZIP_STATE then (16 : Nat) else 0) = 0 :=
    ite_eq_right (by decide)
  rw [e1, e2, e3, e4, e6, e0, f1, f2, f3]
  omega

/-- `s->wrap = -s->wrap` after the trailer: `content` drops by `4 * wrap`, the trailer's bytes. -/
theorem content_wrap {st st' : DeflateState} (hw : 0 < st.wrap.toInt) (e0 : st'.wrap.toInt = -st.wrap.toInt)
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = span st) (e3 : st'.sym_next = st.sym_next)
    (e4 : st'.match_available = st.match_available) (e5 : st'.status = st.status) :
    content st' + 4 * st.wrap.toInt.toNat = content st := by
  unfold content
  rw [e1, e2, e3, e4, e5, e0]
  omega

/-- The lookahead grows by `n` bytes: `quickB` grows by at most `64 n`. -/
theorem quickB_read {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat = st.lookahead.toNat + n) (e7 : st'.block_open = st.block_open) :
    quickB f st' ≤ quickB f st + 64 * n := by
  unfold quickB
  rw [e7, e1]
  by_cases hb : st.block_open ≠ 0
  · rw [ite_eq_left hb, ite_eq_left hb]; omega
  · rw [ite_eq_right hb, ite_eq_right hb]
    by_cases hl : st.lookahead.toNat ≠ 0
    · rw [ite_eq_left hl, ite_eq_left (by omega : st.lookahead.toNat + n ≠ 0)]; omega
    · rw [ite_eq_right hl]
      by_cases hn : st.lookahead.toNat + n ≠ 0
      · rw [ite_eq_left hn]; omega
      · rw [ite_eq_right hn]; omega

/-- The lookahead grows by `n` input bytes (`read_buf`): `psi` grows by at most `G n`. -/
theorem psi_read {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat = st.lookahead.toNat + n) (e2 : span st' = span st)
    (e3 : st'.sym_next = st.sym_next) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) (e9 : mark f st' = mark f st) : psi f st' ≤ psi f st + G * n := by
  have hq := quickB_read (f := f) n e1 e7
  have hc : content st' = content st + 2 ^ 19 * n := by
    unfold content; rw [e1, e2, e3, e4, e5, e6]; omega
  unfold psi G; rw [hc, e8, e9]; omega

/-! ## The part that the strategies change -/

/-- `psi` without the flush marker: what a strategy call changes (the marker is the dispatch's). -/
def psiS (f : Int32) (st : DeflateState) : Nat := content st + quickB f st + owed st

theorem psi_psiS (f : Int32) (st : DeflateState) : psi f st = psiS f st + mark f st := rfl

/-- `psiS` reads `lookahead`, `strstart`, `block_start`, `sym_next`, `match_available`, `status`, `wrap`,
`block_open`, `pending` and `bi_valid`. -/
theorem psiS_congr {f : Int32} {st st' : DeflateState} (e1 : st'.lookahead = st.lookahead)
    (e2 : st'.strstart = st.strstart) (e3 : st'.block_start = st.block_start) (e4 : st'.sym_next = st.sym_next)
    (e5 : st'.match_available = st.match_available) (e6 : st'.status = st.status) (e7 : st'.wrap = st.wrap)
    (e8 : st'.block_open = st.block_open) (e9 : st'.pending = st.pending) (e10 : st'.bi_valid = st.bi_valid) :
    psiS f st' = psiS f st := by
  unfold psiS content quickB owed span; rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

/-- `quickB` does not grow when the lookahead drops (`block_open` kept). -/
theorem quickB_drop {f : Int32} {st st' : DeflateState} (e1 : st'.lookahead.toNat ≤ st.lookahead.toNat)
    (e7 : st'.block_open = st.block_open) : quickB f st' ≤ quickB f st := by
  unfold quickB
  rw [e7]
  by_cases hb : st.block_open ≠ 0
  · rw [ite_eq_left hb, ite_eq_left hb]; exact Nat.le_refl _
  · rw [ite_eq_right hb, ite_eq_right hb]
    by_cases hl : st'.lookahead.toNat ≠ 0
    · rw [ite_eq_left hl, ite_eq_left (by omega : st.lookahead.toNat ≠ 0)]; exact Nat.le_refl _
    · rw [ite_eq_right hl]; exact Nat.zero_le _

/-- A tally of `n >= 1` bytes (a literal or a match): `psiS` does not grow. -/
theorem psiS_tally {f : Int32} {st st' : DeflateState} (n : Nat) (hn : 1 ≤ n)
    (e1 : st'.lookahead.toNat + n = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + n)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next.toNat = st.sym_next.toNat + 3) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) : psiS f st' ≤ psiS f st := by
  have hc := content_tally n e1 e2 hs0 e3 e4 e5 e6
  have hq := quickB_drop (f := f) (by omega : st'.lookahead.toNat ≤ st.lookahead.toNat) e7
  unfold psiS; rw [e8]
  have : 6 * n + 2 ^ 18 ≤ 2 ^ 19 * n := by omega
  omega

/-- The pending literal of `deflate_slow` set: `psiS` does not grow. -/
theorem psiS_pend_lit {f : Int32} {st st' : DeflateState}
    (e1 : st'.lookahead.toNat + 1 = st.lookahead.toNat)
    (e2 : (st'.strstart.toNat : Int) - st'.block_start.toInt = (st.strstart.toNat : Int) - st.block_start.toInt + 1)
    (hs0 : st.block_start.toInt ≤ st.strstart.toNat)
    (e3 : st'.sym_next = st.sym_next) (e4 : st.match_available = 0) (e4' : st'.match_available ≠ 0)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) : psiS f st' ≤ psiS f st := by
  have hc := content_pend_lit e1 e2 hs0 e3 e4 e4' e5 e6
  have hq := quickB_drop (f := f) (by omega : st'.lookahead.toNat ≤ st.lookahead.toNat) e7
  unfold psiS; rw [e8]; omega

/-- The pending literal of `deflate_slow` tallied: `psiS` does not grow. -/
theorem psiS_tally_pend {f : Int32} {st st' : DeflateState}
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = span st)
    (e3 : st'.sym_next.toNat = st.sym_next.toNat + 3) (e4 : st.match_available ≠ 0) (e4' : st'.match_available = 0)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) : psiS f st' ≤ psiS f st := by
  have hc := content_tally_pend e1 e2 e3 e4 e4' e5 e6
  have hq := quickB_drop (f := f) (by rw [e1]; exact Nat.le_refl _ : st'.lookahead.toNat ≤ st.lookahead.toNat) e7
  unfold psiS; rw [e8]; omega

/-- The lookahead grows by `n` input bytes and the window span does not grow (`fill_window`): `psiS` grows by at
most `G n`. -/
theorem quickB_read_le {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat ≤ st.lookahead.toNat + n) (e7 : st'.block_open = st.block_open) :
    quickB f st' ≤ quickB f st + 64 * n := by
  unfold quickB
  rw [e7]
  by_cases hb : st.block_open ≠ 0
  · rw [ite_eq_left hb, ite_eq_left hb]; omega
  · rw [ite_eq_right hb, ite_eq_right hb]
    by_cases hl : st'.lookahead.toNat ≠ 0
    · rw [ite_eq_left hl]
      by_cases hl0 : st.lookahead.toNat ≠ 0
      · rw [ite_eq_left hl0]; omega
      · rw [ite_eq_right hl0]; omega
    · rw [ite_eq_right hl]; omega

theorem psiS_read {f : Int32} {st st' : DeflateState} (n : Nat)
    (e1 : st'.lookahead.toNat ≤ st.lookahead.toNat + n) (e2 : span st' ≤ span st)
    (e3 : st'.sym_next = st.sym_next) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) (e7 : st'.block_open = st.block_open)
    (e8 : owed st' = owed st) : psiS f st' ≤ psiS f st + G * n := by
  have hq := quickB_read_le (f := f) n e1 e7
  have hc : content st' ≤ content st + 2 ^ 19 * n := by
    unfold content; rw [e3, e4, e5, e6]; omega
  unfold psiS G; rw [e8]; omega

/-- A block flush (`block_start = strstart`, no symbols after): `content` drops by the span's and the symbols'
weights. -/
theorem content_flush_le {st st' : DeflateState}
    (e1 : st'.lookahead = st.lookahead) (e2 : span st' = 0)
    (e3 : st'.sym_next = 0) (e4 : st'.match_available = st.match_available)
    (e5 : st'.status = st.status) (e6 : st'.wrap = st.wrap) :
    content st' + 6 * span st + 2 ^ 18 * (st.sym_next.toNat / 3) = content st := by
  unfold content
  rw [e1, e2, e3, e4, e5, e6]
  simp only [UInt32.toNat_zero, Nat.zero_div, Nat.mul_zero]
  omega

/-! ## The accounting of a strategy call -/

/-- From the heap `h` to the heap `H` (stream `i`, state block `b`), `psiS` dropped by the bytes produced, less `G`
per input byte consumed and `e`. -/
def PsiAcc (e : Nat) (h H : Heap) (i b : Nat) : Prop :=
  ∀ z0 z st0 st, h.streams i = some z0 → H.streams i = some z → h.dstate b = some st0 → H.dstate b = some st →
    ∀ f, psiS f st + (z0.avail_out.toNat - z.avail_out.toNat) ≤
      psiS f st0 + G * (z0.avail_in.toNat - z.avail_in.toNat) + e

theorem PsiAcc.refl (h : Heap) (i b : Nat) : PsiAcc 0 h h i b := by
  intro z0 z st0 st h0 h1 s0 s1 f
  rw [h0] at h1; cases h1; rw [s0] at s1; cases s1
  simp

theorem PsiAcc.mono {e e' : Nat} {h H : Heap} {i b : Nat} (A : PsiAcc e h H i b) (he : e ≤ e') :
    PsiAcc e' h H i b := fun z0 z st0 st h0 h1 s0 s1 f => Nat.le_trans (A z0 z st0 st h0 h1 s0 s1 f) (by omega)

theorem G_mul_split (a b c : Nat) (h1 : b ≤ a) (h2 : c ≤ b) : G * (a - c) = G * (a - b) + G * (b - c) := by
  rw [← Nat.mul_add]; congr 1; omega

/-- `PsiAcc` composes with a step from `H` to `H'` that does not grow `avail_in` / `avail_out`. -/
theorem PsiAcc.step {e e' : Nat} {h H H' : Heap} {i b : Nat} (A : PsiAcc e h H i b)
    (hmono : ∀ z0 z, h.streams i = some z0 → H.streams i = some z →
      z.avail_out.toNat ≤ z0.avail_out.toNat ∧ z.avail_in.toNat ≤ z0.avail_in.toNat)
    (hz : ∃ z, H.streams i = some z) (hs : ∃ st, H.dstate b = some st)
    (S : ∀ z z' st st', H.streams i = some z → H'.streams i = some z' → H.dstate b = some st →
      H'.dstate b = some st' → z'.avail_out.toNat ≤ z.avail_out.toNat ∧ z'.avail_in.toNat ≤ z.avail_in.toNat ∧
      ∀ f, psiS f st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
        psiS f st + G * (z.avail_in.toNat - z'.avail_in.toNat) + e') :
    PsiAcc (e + e') h H' i b := by
  intro z0 z2 st0 st2 h0 h2 s0 s2 f
  obtain ⟨z1, h1⟩ := hz
  obtain ⟨st1, s1⟩ := hs
  have a := A z0 z1 st0 st1 h0 h1 s0 s1 f
  obtain ⟨m1, m2⟩ := hmono z0 z1 h0 h1
  obtain ⟨n1, n2, q⟩ := S z1 z2 st1 st2 h1 h2 s1 s2
  have q := q f
  rw [G_mul_split _ _ _ m2 n2]
  generalize G * (z0.avail_in.toNat - z1.avail_in.toNat) = X at *
  generalize G * (z1.avail_in.toNat - z2.avail_in.toNat) = Y at *
  omega

/-- A step that keeps the stream record and does not grow `psiS`. -/
theorem PsiAcc.state {e e' : Nat} {h H H' : Heap} {i b : Nat} (A : PsiAcc e h H i b)
    (hz : ∀ z, H.streams i = some z → H'.streams i = some z) (hz' : ∃ z, H.streams i = some z)
    (hs : ∃ st, H.dstate b = some st)
    (S : ∀ st st', H.dstate b = some st → H'.dstate b = some st' → ∀ f, psiS f st' + e ≤ psiS f st + e') :
    PsiAcc e' h H' i b := by
  intro z0 z2 st0 st2 h0 h2 s0 s2 f
  obtain ⟨z1, h1⟩ := hz'
  obtain ⟨st1, s1⟩ := hs
  have e := Option.some.inj ((hz z1 h1).symm.trans h2)
  subst e
  have a := A z0 z1 st0 st1 h0 h1 s0 s1 f
  have q := S st1 st2 s1 s2 f
  omega

end ZlibNgF.Proof.DeflatePsi
