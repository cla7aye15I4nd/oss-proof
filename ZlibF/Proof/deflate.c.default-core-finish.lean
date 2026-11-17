import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Functional.Format.Wrapper
import ZlibF.Proof.«deflate.c.engine.encoding-init-observed»
import ZlibF.Proof.«deflate.c.engine.encoded-state-finish»
import ZlibF.Spec.Functional.Sequences
import ZlibF.Proof.«deflate.c.engine.encoded-state-scalar-request»
import ZlibF.Proof.«public-deflate-end»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request»
import ZlibF.Proof.«deflate.c.borrow-stable»
import ZlibF.Proof.«deflate.c.engine.public-finish-progress»
import ZlibF.Proof.«deflate.c.engine.public-request-buffer-frame»
import ZlibF.Proof.«deflate.c.engine.caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.input-slices»

/-! # Actual FINISH observations retain the fixed remaining source -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- A readable input snapshot implies the actual null-input entry guard. -/
theorem snapshot_input_valid {h : Heap} {z : ZStream} {input : List UInt8}
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    z.avail_in ≠ 0 → z.next_in ≠ .null := by
  intro nonzero null
  rcases snapshot with ⟨_pointer, zero, _input⟩ | ⟨_ref, _off, _array, pointer, _get, _fit, _value⟩
  · exact nonzero (UInt32.toNat_inj.mp zero)
  · rw [null] at pointer
    cases pointer

/-- The continuation's quantified FINISH input guard follows from the
actual private state and the unchanged readable snapshot. -/
theorem finish_snapshot_protocol {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {input : List UInt8}
    (good : DGood h r ds z d) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∀ id state, z.state = some (.deflate id) → h.dstates id = some state →
      state.status = FINISH_STATE → input = [] := by
  intro id state kind live status
  have ids : ds = id := by
    simpa only [good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
  subst id
  have states : state = d := Option.some.inj (live.symm.trans good.live.hs)
  subst state
  have length := caller_bytes_length snapshot
  rw [accepted status] at length
  exact List.eq_nil_iff_length_eq_zero.mpr length

end ZlibF.Spec.Public.Proofs.DeflateCore
