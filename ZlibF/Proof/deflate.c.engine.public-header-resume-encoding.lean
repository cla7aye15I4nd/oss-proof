import ZlibF.Proof.«deflate.c.engine.header-pending-encoding»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # The next actual public request completes a split initial header -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The split header invariant determines the actual remaining byte count;
it is not an extra caller restriction. -/
theorem HeaderPending.one_remaining {h : Heap} {d : DeflateState}
    (encoding : HeaderPending h d [120]) :
    d.pending.toNat = 1 ∧ PendingBits h d (ZlibF.Spec.bytesToBits [156]) := by
  obtain ⟨remaining, pending, wire, bits, _start, _look⟩ := encoding
  change (120 : UInt8) :: remaining = 120 :: [156] at wire
  have tail : remaining = [156] := (List.cons.inj wire).2
  rw [tail] at pending
  obtain ⟨bytes, data, equal⟩ := pending
  have value : bytes = [156] := by
    apply encoded_bytes_injective
    simpa only [bits, Zlib.Trees.Proofs.Out.natBits, List.range_zero,
      List.map_nil, List.append_nil] using equal.symm
  have count := public_bytes_length data
  rw [value] at count
  exact ⟨count.symm, bytes, data, equal⟩

/-- The actual public last-flush store does not change pending header bytes. -/
theorem HeaderPending.last_flush {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {published : List UInt8}
    (encoding : HeaderPending h d published) (good : DGood h r ds z d) (flush : Int32) :
    HeaderPending (setD h ds { d with last_flush := flush }) { d with last_flush := flush } published := by
  obtain ⟨remaining, pending, wire, bits, start, look⟩ := encoding
  exact ⟨remaining, last_flush_pending_bits good pending flush, wire, bits, start, look⟩


/-- Publishing the last header byte cannot leave raw pending bits. The
independent empty raw history follows from the exact byte equation. -/
theorem header_byte_drain_encoding {after : Heap} {result : DeflateState}
    {input : Nat → UInt8} {written : List UInt8} {remaining : List Bool}
    (pending : PendingBits after result remaining)
    (empty : result.pending.toNat = 0) (bits : result.bi_valid.toInt.toNat = 0)
    (wire : ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits [156]) :
    written = [156] ∧ RawPrefix after result input 0 [] := by
  have remainingEmpty := pending_bits_empty pending empty bits
  have byteEq : written = [156] := by
    apply encoded_bytes_injective
    simpa only [remainingEmpty, List.append_nil] using wire
  rw [remainingEmpty] at pending
  refine ⟨byteEq, [], [], pending, rfl, ?_⟩
  simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0

/-- Every accepted flush with a one-byte caller buffer completes an actual
split header before dispatch. The public call consumes no input, writes
exactly 156 and establishes the empty raw phase on the same returned heap. -/
theorem public_header_pending_one_output_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (flush : Int32) (boundary : BufferedBoundary h r ds z d input origin 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (one : z.avail_out = 1)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (encoding : HeaderPending h d [120]) :
    ∃ after z' result,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [156] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      result.pending = 0 ∧ RawPrefix after result input 0 [] := by
  have shape := encoding.one_remaining
  obtain ⟨_pb, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, outputA, lastA, countA,
      _bits, fields, bytesA, pendingA, wireA⟩ :=
    public_pending_buffered_exhausted flush boundary buffers pointer inputValid flagLo flagHi
      (by intro impossible; rw [status] at impossible; cases impossible)
      (by rw [one]; decide) (by rw [one, shape.1]; decide) shape.2
  have empty : result.pending.toNat = 0 := by rw [one, shape.1] at countA; change result.pending.toNat + 1 = 1 at countA; omega
  have bits : result.bi_valid.toInt.toNat = 0 := by
    rw [fields]
    obtain ⟨_, _, _, bits, _, _⟩ := encoding
    exact bits
  obtain ⟨writtenEq, encodingA⟩ := header_byte_drain_encoding pendingA empty bits wireA
  refine ⟨after, z', result, run, stateA, buffersA, ?_, ?_, outputA, ?_, lastA,
    UInt64.toNat_inj.mp empty, encodingA⟩
  · simpa only [one, UInt32.toNat_one] using accountA
  · simpa only [one, UInt32.toNat_one, writtenEq] using bytesA
  · rw [fields]; exact status


end Zlib.Deflate.Engine.Proofs
