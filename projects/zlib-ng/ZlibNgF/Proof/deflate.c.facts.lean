import ZlibNgF.Proof.«deflate.c.invariant»

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

/-- The state in which `deflate` calls a strategy: the invariant, the CRC tables, valid and set buffers, a valid
`flush` (`Z_NO_FLUSH` .. `Z_BLOCK`), and no pending bytes (`deflate` flushed them, or returned). -/
def StratPre (h : Heap) (s : StreamPtr) (flush : Int32) : Prop :=
  DInv h s ∧ CrcGlobals h ∧ DStreamIO h s ∧ DBufsSet h s ∧ 0 ≤ flush ∧ flush ≤ 5 ∧
    ∃ b st, DStateIs h s b st ∧ st.pending = 0

/-- What a strategy call leaves: the invariant, valid and set buffers, a change of the stream record, the stream's block
and the output buffer only, and no pending bytes after `block_done` / `finish_done`. -/
def StratPost (h : Heap) (s : StreamPtr) (bs : BlockState) (h' : Heap) : Prop :=
  DInv h' s ∧ DStreamIO h' s ∧ DBufsSet h' s ∧ DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧
    (bs = .block_done ∨ bs = .finish_done → ∃ b st, DStateIs h' s b st ∧ st.pending = 0)

/-- A strategy `f`: from `StratPre`, no fault and `StratPost`. -/
def StratOk (f : StatePtr → Int32 → M BlockState) : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (b : Nat) (flush : Int32), StratPre h s flush → StateBlock h s b →
    ∃ bs h', C.run (f (some b) flush) h = .ok (bs, h') ∧ StratPost h s bs h'

/-- The strategies, one field each (`deflate` calls `deflate_stored` for level 0, `deflate_huff` for
`Z_HUFFMAN_ONLY`, `deflate_rle` for `Z_RLE`, else the function of `configuration_table`). -/
structure StrategyFacts : Prop where
  stored : StratOk ZlibNg.DeflateStored.deflate_stored
  quick : StratOk ZlibNg.DeflateQuick.deflate_quick
  fast : StratOk ZlibNg.DeflateFast.deflate_fast
  medium : StratOk ZlibNg.DeflateMedium.deflate_medium
  medium_fizzle : StratOk ZlibNg.DeflateMedium.deflate_medium_fizzle
  slow : StratOk ZlibNg.DeflateSlow.deflate_slow
  huff : StratOk ZlibNg.DeflateHuff.deflate_huff
  rle : StratOk ZlibNg.DeflateRle.deflate_rle

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
(`EmitKeeps`), and at most `grow st` more pending bytes. -/
def EmitOk (s : StreamPtr) (b : Nat) (pre : DeflateState → Prop) (room grow : DeflateState → Nat) (m : M Unit) :
    Prop :=
  ∀ (h : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st →
    PendRoom b st (room st) (4 * st.lit_bufsize.toNat + 9) →
    (st.sym_next ≠ 0 → PendRoom b st (room st) (st.lit_bufsize.toNat + 8)) →
    ∃ h', C.run m h = .ok ((), h') ∧ DWork h' s ∧ DFrame h h' (streamIds s) [b] [] [] ∧ StreamKeep h h' s ∧
      (∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → PbufOnly h h' b pbo (4 * st.lit_bufsize.toNat + 9)) ∧
      ∀ st', DStateIs h' s b st' → EmitKeeps st st' ∧ st'.pending.toNat ≤ st.pending.toNat + grow st

/-- `buf` is `NULL` with `len == 0`, or `len` bytes of the window from offset `k`, below `strstart`. -/
def WindowBuf (b : Nat) (st : DeflateState) (buf : BPtr) (len : UInt32) : Prop :=
  (buf = .null ∧ len = 0) ∨
    ∃ wo k, st.window = .val (.ref (.heap b) wo) ∧ buf = .ref (.heap b) (wo + k) ∧ k + len.toNat ≤ st.strstart.toNat

/-- The bytes of a stored block of `len` bytes with the bits of `st`: the 3 header bits and the padding to a byte
boundary (`(bi_valid + 3 + 7) / 8` bytes), `LEN` and `NLEN`, the data (the `have` of `deflate_stored`). -/
def storedRoom (st : DeflateState) (len : UInt32) : Nat := len.toNat + (st.bi_valid.toInt.toNat + 42) / 8

/-- The block emitters. `flush_block` is called by `FLUSH_BLOCK_ONLY` with no pending bytes (the previous
`FLUSH_BLOCK` emptied them, or the strategy returned) and the block's bytes in the window (or `NULL` when
`block_start` is negative); its result fits `pending_buf` (the `sym_buf` overlay argument of `deflate.c`).
`stored_block` writes `storedRoom` bytes; `align` and the `emit_*` of `deflate_quick` (static trees) add at most 16
bytes (with up to 63 bits waiting in `bi_buf`). -/
structure TreesFacts : Prop where
  flush_block : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32),
    EmitOk s b (fun st => st.pending = 0 ∧ (buf = .null ∨ WindowBuf b st buf len)) (fun _ => 0)
      (fun st => 4 * st.lit_bufsize.toNat + 9) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)
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

end ZlibNgF.Proof.DeflateFacts
