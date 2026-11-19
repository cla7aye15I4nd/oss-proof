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
  strategy (`DWork`: the invariant, except that up to 63 bits may wait in `bi_buf`), do not fault, keep the working
  state, change only the stream's block, and add a bounded number of pending bytes.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateFacts
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv

/-- The working state of a strategy: the invariant's clauses, except that `bi_buf` holds up to 63 bits (the
clauses are those of `DCore` on the state with `bi_valid` cleared). -/
def DWork (h : Heap) (s : StreamPtr) : Prop :=
  ∃ i z b st al, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st ∧
    h.dallocsOf b = some al ∧ 0 ≤ st.bi_valid ∧ st.bi_valid < 64 ∧
    DCore h s z b (dview { st with bi_valid := 0 }) al

/-- The state record of stream `s` in `h`: block `b`, record `st`. -/
def DStateIs (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) : Prop :=
  ∃ i z, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧ h.dstate b = some st

/-- The state in which `deflate` calls a strategy: the invariant, the CRC tables, valid buffers, a valid `flush`
(`Z_NO_FLUSH` .. `Z_BLOCK`), and no pending bytes (`deflate` flushed them, or returned). -/
def StratPre (h : Heap) (s : StreamPtr) (flush : Int32) : Prop :=
  DInv h s ∧ CrcGlobals h ∧ DStreamIO h s ∧ 0 ≤ flush ∧ flush ≤ 5 ∧
    ∃ b st, DStateIs h s b st ∧ st.pending = 0

/-- What a strategy call leaves: the invariant, valid buffers, a change of the stream record, the stream's block
and the output buffer only, and no pending bytes after `block_done` / `finish_done`. -/
def StratPost (h : Heap) (s : StreamPtr) (bs : BlockState) (h' : Heap) : Prop :=
  DInv h' s ∧ DStreamIO h' s ∧ DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧
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

/-- An emitter `m` on stream `s` (block `b`): from the working state with at least `room` bytes left in
`pending_buf` (`pending + room <= PENDING_BUF_SIZE`), no fault, the working state after, only block `b` changed,
and at most `grow` more pending bytes. -/
def EmitOk (s : StreamPtr) (b : Nat) (room : Nat) (pre : DeflateState → Prop) (grow : Nat) (m : M Unit) : Prop :=
  ∀ (h : Heap) (st : DeflateState), DWork h s → DStateIs h s b st → pre st →
    st.pending.toNat + room ≤ 4 * st.lit_bufsize.toNat + 9 →
    ∃ h', C.run m h = .ok ((), h') ∧ DWork h' s ∧ DFrame h h' [] [b] [] [] ∧
      ∀ st', DStateIs h' s b st' → st'.pending.toNat ≤ st.pending.toNat + grow

/-- `buf` is `NULL` with `len == 0`, or `len` bytes of the window from offset `k`, below `strstart`. -/
def WindowBuf (b : Nat) (st : DeflateState) (buf : BPtr) (len : UInt32) : Prop :=
  (buf = .null ∧ len = 0) ∨
    ∃ wo k, st.window = .val (.ref (.heap b) wo) ∧ buf = .ref (.heap b) (wo + k) ∧ k + len.toNat ≤ st.strstart.toNat

/-- The block emitters. `flush_block` is called by `FLUSH_BLOCK_ONLY` with no pending bytes (the previous
`FLUSH_BLOCK` emptied them, or the strategy returned) and the block's bytes in the window (or `NULL` when
`block_start` is negative); its result fits `pending_buf` (the `sym_buf` overlay argument of `deflate.c`).
`stored_block` writes a header of at most 12 bytes and the `len` bytes of `buf`; `align` and the `emit_*` of
`deflate_quick` (static trees) add at most 16 bytes. -/
structure TreesFacts : Prop where
  flush_block : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32),
    EmitOk s b 0 (fun st => st.pending = 0 ∧ (buf = .null ∨ WindowBuf b st buf len))
      (4 * 32768 + 9) (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last)
  stored_block : ∀ (s : StreamPtr) (b : Nat) (buf : BPtr) (len : UInt32) (last : Int32),
    EmitOk s b (len.toNat + 12) (fun st => WindowBuf b st buf len) (len.toNat + 12)
      (ZlibNg.Trees.zng_tr_stored_block (some b) buf len last)
  align : ∀ (s : StreamPtr) (b : Nat), EmitOk s b 16 (fun _ => True) 16 (ZlibNg.Trees.zng_tr_align (some b))
  emit_lit : ∀ (s : StreamPtr) (b : Nat) (c : UInt32), c < 256 →
    EmitOk s b 16 (fun _ => True) 16
      (ZlibNg.TreesEmit.zng_tr_emit_lit (some b) ZlibNg.DeflateQuick.static_ltree_p c)
  emit_dist : ∀ (s : StreamPtr) (b : Nat) (lc dist : UInt32), lc ≤ 255 → 1 ≤ dist → dist ≤ 32768 →
    EmitOk s b 16 (fun _ => True) 16
      (ZlibNg.TreesEmit.zng_tr_emit_dist (some b) ZlibNg.DeflateQuick.static_ltree_p
        ZlibNg.DeflateQuick.static_dtree_p lc dist)
  emit_tree : ∀ (s : StreamPtr) (b : Nat) (last : Int32),
    EmitOk s b 16 (fun _ => True) 16 (ZlibNg.TreesEmit.zng_tr_emit_tree (some b) ZlibNg.Trees.STATIC_TREES last)
  emit_end_block : ∀ (s : StreamPtr) (b : Nat) (last : Int32),
    EmitOk s b 16 (fun _ => True) 16
      (ZlibNg.TreesEmit.zng_tr_emit_end_block (some b) ZlibNg.DeflateQuick.static_ltree_p last)
  emit_align : ∀ (s : StreamPtr) (b : Nat), EmitOk s b 16 (fun _ => True) 16
      (ZlibNg.TreesEmit.zng_tr_emit_align (some b))

/-! ## Interface lemmas -/

/-- An invariant stream is in the working state. -/
theorem DWork.of_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) : DWork h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  have b0 : 0 ≤ st.bi_valid := c.bits.1
  have b8 : st.bi_valid < 8 := c.bits.2
  have e8 : (8 : Int32).toInt = 8 := rfl
  have e64 : (64 : Int32).toInt = 64 := rfl
  have l8 := Int32.lt_iff_toInt_lt.mp b8
  refine ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, Int32.lt_iff_toInt_lt.mpr (by omega),
    { c with bits := ⟨Int32.le_refl _, show (0 : Int32) < 8 by decide⟩ }⟩

/-- A working state with fewer than 8 bits in `bi_buf` is invariant. -/
theorem DWork.inv {h : Heap} {s : StreamPtr} (hw : DWork h s)
    (h8 : ∀ b st, DStateIs h s b st → st.bi_valid < 8) : DInv h s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, b0, -, c⟩ := hw
  exact ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, { c with bits := ⟨b0, h8 b st ⟨i, z, rfl, hz, hb, hst⟩⟩ }⟩

end ZlibNgF.Proof.DeflateFacts
