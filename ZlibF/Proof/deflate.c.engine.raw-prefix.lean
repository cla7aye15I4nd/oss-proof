import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.eof-stream-encoding»
import ZlibF.Proof.«deflate.c.engine.body-prefix-step»
import ZlibF.Proof.«deflate.c.engine.encoding-output-slices»
import ZlibF.Proof.«deflate.c.engine.body-all-scalar-output»
import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»
import ZlibF.Proof.«deflate.c.engine.eof-output-interval»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»
import ZlibF.Proof.«deflate.c.engine.buffered-initial»

/-! # An initialized raw encoding invariant for publication and caller replacement -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Independent raw nonfinal-block meaning of already published bytes
and the actual remaining pending bits. This is the raw data phase; pending
wrapper header/trailer bytes have their separate public phases. The input
history and private representation are supplied by BufferedBoundary. -/
def RawPrefix (h : Heap) (d : DeflateState) (input : Nat → UInt8) (base : Nat)
    (published : List UInt8) : Prop :=
  ∃ remaining encoded, PendingBits h d remaining ∧
    ZlibF.Spec.bytesToBits published ++ remaining = encoded ∧
    BlockPrefix [] 0 [] encoded (inputPrefix input base)

/-- Legal caller replacement keeps the exact private raw pending sequence
and its independent meaning. Earlier published bytes are ghost history,
so the caller may reuse or replace the former public output buffer. -/
theorem RawPrefix.rebuffer {h g : Heap} {r : ZStreamRef} {ds base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {published : List UInt8}
    (encoding : RawPrefix h d input base published) (good : DGood h r ds z d)
    (edit : Rebuffer h g r) : RawPrefix g d input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, rebuffer_pending_bits good edit pending, wire, meaning⟩

/-- Actual pending publication advances the raw byte history without
changing the completed blocks' meaning. Base and advanced cursors, zero
capacity and partial drains are admitted. The initialized buffered boundary
and next strategy readiness coexist on the same returned heap. -/
theorem flush_pending_raw_prefix {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (encoding : RawPrefix h d input base published) :
    ∃ after z' result written,
      flush_pending (some r) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base xs config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 written.length ∧ Bytes after z.next_out written.length written ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      RawPrefix after result input base (published ++ written) := by
  obtain ⟨before, encoded, pending, wire, meaning⟩ := encoding
  obtain ⟨_pb, produced, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, _amount, _left, _fields,
      readyA, bytesA, pendingA, wireA⟩ :=
    flush_pending_buffered_boundary boundary buffers pointer pending
  have length := public_bytes_length bytesA
  have wireAll : ZlibF.Spec.bytesToBits (published ++ written) ++ remaining = encoded := by
    simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc] at wireA wire ⊢
    rw [wireA, wire]
  refine ⟨after, z', result, written, run, stateA, buffersA, ?_, ?_, readyA,
    remaining, encoded, pendingA, wireAll, meaning⟩
  · rw [length]; exact accountA
  · rw [length]; exact bytesA

/-- Actual successful default-parameter initialization establishes the raw
encoding invariant with no prior bytes or blocks. The engine/content and
EOF invariants are conclusions of that same execution. The universal Init2
contract and any engine or encoding invariant are not assumptions. Wrapper
header creation and allocation-failure safety remain separate results. -/
theorem default_initialization_raw_prefix {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      BufferedBoundary after r h.nextBlk zf sf input 0 0 [] (engineConfig sf) ∧
      StreamReachable .deflate after r ∧ RawPrefix after sf input 0 [] := by
  obtain ⟨after, zf, sf, run, start, boundary, frontier, _initial, reachable⟩ :=
    default_initialization_end_frontier hf hu hg hz ha hv params alloc input
  have stateA := boundary.buffered frontier (fun _ => start.pendingOut)
  obtain ⟨_pb, _buf, trees, _ledger, _balance⟩ := boundary.symbols
  have held := pending_bits_base trees start.pendingOut
  have empty := pending_bits_empty held (by rw [start.pending]; rfl) (by rw [start.bits]; rfl)
  rw [empty] at held
  refine ⟨after, zf, sf, run, stateA, reachable, [], [], held, rfl, ?_⟩
  simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0

end Zlib.Deflate.Engine.Proofs
