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
later call keeps: `pending_buf` is set, `head` lies in the plain bytes of the block (`CLEAR_HASH`), `level` is 0..9
(`lm_set_level`), the tree arrays have their C sizes (`zng_tr_init`); the sizes `w_size`, `window_size`,
`lit_bufsize`, `pending_buf_size`, `sym_end`; the layout of `alloc_deflate` (window, `prev`, `head`, `pending_buf` in
that order, `sym_buf` at `pending_buf + lit_bufsize + PENDING_BUF_PAD`) and the pending bytes within `pending_buf`
(from `pending_buf` itself when there are none); whole symbols in `sym_buf` up to `sym_end + 3`; at most 63 bits in
`bi_buf`, whose complete bytes fit after the pending bytes; `strstart + lookahead` within the window; a valid `strategy`; both function pointers of `lm_set_level` set, `insert_batch` the one of `level`;
valid distances in the tallied symbols and frequencies that count them, the pending bytes before `sym_buf` while there
are symbols, no symbols in the header states; `block_start` and `insert` at or before `strstart`,
`block_start` bounded below; `w_size` a power of two and `fill_end + MIN_LOOKAHEAD` a multiple of it within the window; the
tree descriptors of `zng_tr_init`; `lit_bufsize` a multiple of 16; the sizes of the scratch arrays of `trees.c`;
`opt_len`, `static_len` and the `bl_tree` frequencies 0 between blocks.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateInv
open C ZlibNgF.Spec ZlibNg.Deflate
open ZlibNgF.Proof.InflateInv (ldStream_app)

/-- The `insert_batch` function that `lm_set_level` stores for `level` (`deflate.c:1193-1201`): `insert_roll_batch`
from `MIN_ROLL_LEVEL` (9) on, else `insert_knuth_batch_head` at level 1 (`HAVE_QUICK_STRATEGY`) and
`insert_knuth_batch` otherwise. -/
def insertBatchOf (level : Int32) : InsertBatchFn :=
  if level ≥ MIN_ROLL_LEVEL then .insert_roll_batch
  else if level == 1 then .insert_knuth_batch_head else .insert_knuth_batch

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
  block_start : Int32
  insert : UInt32
  fill_end : UInt32
  ltree : Array Ct
  dtree : Array Ct
  l_dyn : Ival CtPtr
  l_stat : Ival StaticDescPtr
  d_dyn : Ival CtPtr
  d_stat : Ival StaticDescPtr
  bl_dyn : Ival CtPtr
  bl_stat : Ival StaticDescPtr
  pqlsize : Nat
  pqssize : Nat
  blcsize : Nat
  opt_len : UInt32
  static_len : UInt32
  bltree : Array Ct

/-- The constrained fields of `st`. -/
def dview (st : DeflateState) : DView :=
  ⟨st.strm, st.alloc_bufs, st.status, st.wrap, st.gzhead, st.w_size, st.pending_buf, st.head, st.level,
    st.dyn_ltree.size, st.dyn_dtree.size, st.bl_tree.size, st.window, st.prev, st.window_size, st.lit_bufsize,
    st.pending_buf_size, st.sym_buf, st.sym_end, st.sym_next, st.pending, st.pending_out, st.bi_valid, st.strstart,
    st.lookahead, st.strategy, st.longest_match, st.insert_batch, st.block_start, st.insert, st.fill_end,
    st.dyn_ltree, st.dyn_dtree, st.l_desc.dyn_tree, st.l_desc.stat_desc, st.d_desc.dyn_tree, st.d_desc.stat_desc,
    st.bl_desc.dyn_tree, st.bl_desc.stat_desc, st.pq_leaves.size, st.pq_scratch.size, st.bl_count.size, st.opt_len,
    st.static_len, st.bl_tree⟩

/-! ## The tallied symbols -/

/-- The distance of tallied symbol `j` (the first two bytes, little endian) in bytes `d` from `sym_buf` offset `sbo`;
0 for a literal. -/
def symDist (d : Array UInt8) (sbo j : Nat) : Nat := d[sbo + 3 * j]!.toNat + 256 * d[sbo + 3 * j + 1]!.toNat

/-- The literal/length code of tallied symbol `j`: the literal byte, or `zng_length_code[lc] + LITERALS + 1`. -/
def symLCode (d : Array UInt8) (sbo j : Nat) : Nat :=
  if symDist d sbo j = 0 then d[sbo + 3 * j + 2]!.toNat else zng_length_code[d[sbo + 3 * j + 2]!.toNat]!.toNat + 257

/-- `d_code(dist)` on natural numbers. -/
def dCodeOf (dist : Nat) : Nat :=
  if dist < 256 then zng_dist_code[dist]!.toNat else zng_dist_code[256 + dist / 128]!.toNat

/-- The number of the first `n` tallied symbols whose literal/length code is `c`. -/
def lCount (d : Array UInt8) (sbo n c : Nat) : Nat := (List.range n).countP (fun j => symLCode d sbo j = c)

/-- The number of the first `n` tallied symbols that are matches with distance code `c` (`d_code(dist - 1)`). -/
def dCount (d : Array UInt8) (sbo n c : Nat) : Nat :=
  (List.range n).countP (fun j => symDist d sbo j ≠ 0 ∧ dCodeOf (symDist d sbo j - 1) = c)

/-- The symbols in `sym_buf` (bytes `d` from offset `sbo`, `sym_next` bytes) are those that `zng_tr_tally_*` write,
and the frequencies of `dyn_ltree` / `dyn_dtree` count them: a distance of at most 32768 (`compress_block` indexes
`zng_dist_code` with `d_code(dist - 1)`); `dyn_ltree[c].Freq` the number of symbols with literal/length code `c`, plus
one for `END_BLOCK` (`init_block`); `dyn_dtree[c].Freq` the number of matches with distance code `c`. -/
structure SymOk (d : Array UInt8) (sbo : Nat) (sym_next : UInt32) (lt dt : Array Ct) : Prop where
  dist : ∀ j, j < sym_next.toNat / 3 → symDist d sbo j ≤ 32768
  lfreq : ∀ c, c < 286 → (lt[c]!).fc.toNat = lCount d sbo (sym_next.toNat / 3) c + (if c = 256 then 1 else 0)
  dfreq : ∀ c, c < 30 → (dt[c]!).fc.toNat = dCount d sbo (sym_next.toNat / 3) c

/-- `SymOk` reads only the bytes of the symbols. -/
theorem SymOk.of_eq {d d' : Array UInt8} {sbo : Nat} {n : UInt32} {lt dt : Array Ct} (hs : SymOk d sbo n lt dt)
    (he : ∀ k, k < n.toNat → d'[sbo + k]! = d[sbo + k]!) : SymOk d' sbo n lt dt := by
  have hj : ∀ j, j < n.toNat / 3 → symDist d' sbo j = symDist d sbo j ∧ symLCode d' sbo j = symLCode d sbo j := by
    intro j hj
    have e0 := he (3 * j) (by omega)
    have e1 := he (3 * j + 1) (by omega)
    have e2 := he (3 * j + 2) (by omega)
    rw [← Nat.add_assoc] at e1 e2
    have hd : symDist d' sbo j = symDist d sbo j := by simp only [symDist, e0, e1]
    exact ⟨hd, by simp only [symLCode, hd, e2]⟩
  refine ⟨fun j h3 => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [(hj j h3).1]; exact hs.dist j h3
  · rw [hs.lfreq c hc]; congr 1
    exact List.countP_congr fun j hm => by
      rw [(hj j (List.mem_range.mp hm)).2]
  · rw [hs.dfreq c hc]
    exact List.countP_congr fun j hm => by
      rw [(hj j (List.mem_range.mp hm)).1]

/-- With no symbols, `SymOk` says that the frequencies are those of `init_block`. -/
theorem SymOk.empty {d : Array UInt8} {sbo : Nat} {lt dt : Array Ct}
    (hl : ∀ c, c < 286 → (lt[c]!).fc.toNat = if c = 256 then 1 else 0) (hd : ∀ c, c < 30 → (dt[c]!).fc.toNat = 0) :
    SymOk d sbo 0 lt dt :=
  ⟨fun j h => by simp at h, fun c hc => by simp [lCount, hl c hc], fun c hc => by simp [dCount, hd c hc]⟩

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
  /-- `wrap` is 0 (raw), 1 (zlib) or 2 (gzip), negated by `deflate` once the trailer is written (`Z_FINISH`) -/
  wrap : v.wrap = 0 ∨ v.wrap = 1 ∨ v.wrap = 2 ∨ v.wrap = -1 ∨ v.wrap = -2
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
  `[pending_out, pending_out + pending)` and the complete bytes of `bi_buf` after them lie within `pending_buf` -/
  lay : ∃ d wo po ho pbo, h.bytes b = some d ∧ v.window = .val (.ref (.heap b) wo) ∧
    v.prev = .val (.ref (.heap b) po) ∧ v.head = .val (.ref (.heap b) ho) ∧
    v.pending_buf = .val (.ref (.heap b) pbo) ∧ wo + v.window_size.toNat ≤ po ∧ po + 2 * v.w_size.toNat ≤ ho ∧
    ho + 131072 ≤ pbo ∧ pbo + 4 * v.lit_bufsize.toNat + 64 ≤ d.size ∧
    v.sym_buf = .val (.ref (.heap b) (pbo + v.lit_bufsize.toNat + 8)) ∧
    ∃ poo, v.pending_out = .val (.ref (.heap b) poo) ∧ pbo ≤ poo ∧
      poo - pbo + v.pending.toNat + v.bi_valid.toInt.toNat / 8 ≤ 4 * v.lit_bufsize.toNat + 9
  /-- with no pending bytes, `pending_out` is back at `pending_buf` (`flush_pending`, `deflateResetKeep`) -/
  pout : v.pending = 0 → v.pending_out = v.pending_buf
  /-- the symbol buffer holds whole three-byte symbols, at most `sym_end + 3` bytes (`lit_bufsize` symbols): `deflate_fast`
  and `deflate_medium` tally one more match at `sym_next == sym_end` before their `FLUSH_BLOCK` (the continuation of
  a maximal match after a tally that filled the buffer); between calls `DeflateFacts.SymsOk` keeps
  `sym_next < sym_end` -/
  syms : v.sym_next ≤ v.sym_end + 3 ∧ v.sym_next.toNat % 3 = 0
  /-- the bit buffer (64 bits) holds at most 63 bits: `zng_tr_flush_bits` (`flush_pending`, `deflatePrime`) moves the
  complete bytes to `pending_buf`, but `deflate_quick` with `Z_FIXED` may return `need_more` with up to 63 bits
  waiting (when fewer than 8 bits are left is a between-call fact, `DeflateFacts.SymsOk`) -/
  bits : 0 ≤ v.bi_valid ∧ v.bi_valid < 64
  /-- the window positions in use lie in the window -/
  look : v.strstart.toNat + v.lookahead.toNat ≤ v.window_size.toNat
  /-- `strategy` is one of the five strategies -/
  strategy : 0 ≤ v.strategy ∧ v.strategy ≤ 4
  /-- `lm_set_level` has set both function pointers, `insert_batch` to the function of `level` -/
  fns : (∃ f, v.longest_match = .val f) ∧ v.insert_batch = .val (insertBatchOf v.level)
  /-- the symbols in `sym_buf` are those that `zng_tr_tally_*` write, and the frequencies count them (`SymOk`) -/
  symv : ∃ d sbo, h.bytes b = some d ∧ v.sym_buf = .val (.ref (.heap b) sbo) ∧
    SymOk d sbo v.sym_next v.ltree v.dtree
  /-- while symbols wait in `sym_buf`, the pending bytes and the complete bytes of `bi_buf` end before it -/
  psym : v.sym_next ≠ 0 → ∃ pbo poo, v.pending_buf = .val (.ref (.heap b) pbo) ∧
    v.pending_out = .val (.ref (.heap b) poo) ∧
    poo - pbo + v.pending.toNat + v.bi_valid.toInt.toNat / 8 ≤ v.lit_bufsize.toNat + 8
  /-- in the header states (before the first block), no symbol is tallied -/
  hdr : v.status ≠ BUSY_STATE → v.status ≠ FINISH_STATE → v.sym_next = 0
  /-- `block_start` lies at or before `strstart` -/
  bstart : v.block_start.toInt ≤ v.strstart.toNat
  /-- `insert` is at most `strstart` -/
  ins : v.insert ≤ v.strstart
  /-- `w_size` is a power of two (`1 << windowBits`, `windowBits` 9..15) -/
  wpow : ∃ k, 9 ≤ k ∧ k ≤ 15 ∧ v.w_size.toNat = 2 ^ k
  /-- `fill_end + MIN_LOOKAHEAD` is a multiple of `w_size` (`lm_init` sets `2 * w_size - MIN_LOOKAHEAD`,
  `fill_window` adds `w_size`) within the window -/
  fe_mod : (v.fill_end.toNat + 262) % v.w_size.toNat = 0
  fe_hi : v.fill_end.toNat + 262 ≤ v.window_size.toNat
  /-- `block_start` stays far from `INT_MIN` (patch 0018: `fill_window` lowers it only while it stays at or above
  `-(2^30 + 2^16)`; every other store writes `strstart`, 0, or a value at least 0) -/
  bs_lo : -(2 ^ 30 + 2 ^ 16) ≤ v.block_start.toInt
  /-- the tree descriptors that `zng_tr_init` sets -/
  descs : v.l_dyn = .val (.ref (.dyn_ltree b) 0) ∧ v.l_stat = .val .static_l_desc ∧
    v.d_dyn = .val (.ref (.dyn_dtree b) 0) ∧ v.d_stat = .val .static_d_desc ∧
    v.bl_dyn = .val (.ref (.bl_tree b) 0) ∧ v.bl_stat = .val .static_bl_desc
  /-- `lit_bufsize = 1 << (memLevel + 6)` is a multiple of 16 (`alloc_deflate` of `deflateCopy` aligns the state that
  follows `pending_buf` with it) -/
  lmod : v.lit_bufsize.toNat % 16 = 0
  /-- `lit_bufsize = 1 << (memLevel + 6)` is a power of two (`memLevel` 1..9) -/
  lpow : ∃ k, 7 ≤ k ∧ k ≤ 15 ∧ v.lit_bufsize.toNat = 2 ^ k
  /-- the scratch arrays of `build_tree` / `gen_bitlen` have their C sizes: `pq_leaves` and `pq_scratch` `L_CODES + 1`
  entries, `bl_count` `MAX_BITS + 1` -/
  scratch : v.pqlsize = 287 ∧ v.pqssize = 287 ∧ v.blcsize = 16
  /-- between blocks `opt_len`, `static_len` and the frequencies of `bl_tree` are 0: `init_block` sets them, and only
  `zng_tr_flush_block` (which ends with `init_block`) writes them -/
  blk : v.opt_len = 0 ∧ v.static_len = 0 ∧ ∀ c, c < 19 → (v.bltree[c]!).fc = 0

/-- The clauses read the heap only through block `b`. -/
theorem DCore.of_heap {h h' : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (hb : h'.bytes b = h.bytes b) (c : DCore h s z b v al) : DCore h' s z b v al :=
  { c with head := by rw [hb]; exact c.head, lay := by rw [hb]; exact c.lay, symv := by rw [hb]; exact c.symv }

/-- `sym_end + 3` does not wrap: `sym_end = 3 * (lit_bufsize - 1)` with `lit_bufsize ≤ 32768`. -/
theorem DCore.sym_end3 {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore h s z b v al) : (v.sym_end + 3).toNat = v.sym_end.toNat + 3 := by
  obtain ⟨-, -, -, -, hl, -, hse⟩ := c.sizes
  rw [UInt32.toNat_add]; simp only [UInt32.reduceToNat]; omega

/-- The symbol count of `DCore.syms` in natural numbers: at most `sym_end + 3 = 3 * lit_bufsize` bytes. -/
theorem DCore.syms_le {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {v : DView} {al : DeflateAllocs}
    (c : DCore h s z b v al) :
    v.sym_next.toNat ≤ v.sym_end.toNat + 3 ∧ v.sym_next.toNat ≤ 3 * v.lit_bufsize.toNat ∧ v.sym_next.toNat % 3 = 0 := by
  have h1 := UInt32.le_iff_toNat_le.mp c.syms.1
  rw [c.sym_end3] at h1
  obtain ⟨-, -, -, hl1, -, -, hse⟩ := c.sizes
  exact ⟨h1, by omega, c.syms.2⟩

/-- `sym_next ≤ sym_end` gives the `syms` clause (`sym_end + 3` does not wrap, `sym_end < 2^32 - 3`). -/
theorem syms_of_le {a e : UInt32} (h : a ≤ e) (he : e.toNat + 3 < 2 ^ 32) : a ≤ e + 3 := by
  rw [UInt32.le_iff_toNat_le] at h ⊢
  rw [UInt32.toNat_add]; simp only [UInt32.reduceToNat]; omega

/-- The structural invariant of the deflate stream `s` in `h`. -/
def DInv (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ DCore h s z b (dview st) al

/-- `st'` agrees with `st` on the fields that the between-call facts (`DeflateSide.SideAt`) read. -/
structure SideEq (st st' : DeflateState) : Prop where
  status : st'.status = st.status
  wrap : st'.wrap = st.wrap
  gzhead : st'.gzhead = st.gzhead
  gzindex : st'.gzindex = st.gzindex
  sym_next : st'.sym_next = st.sym_next
  sym_end : st'.sym_end = st.sym_end
  strstart : st'.strstart = st.strstart
  block_start : st'.block_start = st.block_start
  level : st'.level = st.level
  lookahead : st'.lookahead = st.lookahead
  strategy : st'.strategy = st.strategy
  last_flush : st'.last_flush = st.last_flush
  /-- `bi_buf` holds 8 or more bits only if it did before -/
  bits : 8 ≤ st'.bi_valid → 8 ≤ st.bi_valid

theorem SideEq.refl (st : DeflateState) : SideEq st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id⟩

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
