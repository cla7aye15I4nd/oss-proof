import ZlibF.Spec.Safety.Streams
import ZlibF.Spec.Safety.Copy

/-!
# The widened stream safety goals imply the old ones

Evidence that the refusal clauses strengthen the 23 per-call stream safety goals and the two copy
goals: each old statement (as registered before the change, restated here as `Old.<goal>`) follows
from the new goal. For a stream goal the old statement is the new goal's second conjunct. For
`deflateCopy_safety` the old refusal clause (a `NULL` `zalloc`, `zfree` or state) is an instance
of the new one (`RefusedDeflate`); `inflateCopy_safety` gains a fourth clause.
-/

namespace ZlibF.Spec.Public.RefusalStrengthening
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `Goal.inflate_safety` as stated before the refusal clauses. -/
def Old.inflate_safety : Prop :=
  ∀ h r flush,
    StreamCallDomain .inflate h r (.inflate (some r) flush) →
    StreamCallSafe .inflate h r (.inflate (some r) flush)

/-- `Goal.inflateSetDictionary_safety` as stated before the refusal clauses. -/
def Old.inflateSetDictionary_safety : Prop :=
  ∀ h r dictionary dictLength,
    StreamCallDomain .inflate h r (.inflateSetDictionary (some r) dictionary dictLength) →
    StreamCallSafe .inflate h r (.inflateSetDictionary (some r) dictionary dictLength)

/-- `Goal.inflateGetDictionary_safety` as stated before the refusal clauses. -/
def Old.inflateGetDictionary_safety : Prop :=
  ∀ h r dictionary dictLength,
    StreamCallDomain .inflate h r (.inflateGetDictionary (some r) dictionary dictLength) →
    StreamCallSafe .inflate h r (.inflateGetDictionary (some r) dictionary dictLength)

/-- `Goal.inflateSync_safety` as stated before the refusal clauses. -/
def Old.inflateSync_safety : Prop :=
  ∀ h r,
    StreamCallDomain .inflate h r (.inflateSync (some r)) →
    StreamCallSafe .inflate h r (.inflateSync (some r))

/-- `Goal.inflateReset_safety` as stated before the refusal clauses. -/
def Old.inflateReset_safety : Prop :=
  ∀ h r,
    StreamCallDomain .inflate h r (.inflateReset (some r)) →
    StreamCallSafe .inflate h r (.inflateReset (some r))

/-- `Goal.inflateReset2_safety` as stated before the refusal clauses. -/
def Old.inflateReset2_safety : Prop :=
  ∀ h r windowBits,
    StreamCallDomain .inflate h r (.inflateReset2 (some r) windowBits) →
    StreamCallSafe .inflate h r (.inflateReset2 (some r) windowBits)

/-- `Goal.inflatePrime_safety` as stated before the refusal clauses. -/
def Old.inflatePrime_safety : Prop :=
  ∀ h r bits value,
    StreamCallDomain .inflate h r (.inflatePrime (some r) bits value) →
    StreamCallSafe .inflate h r (.inflatePrime (some r) bits value)

/-- `Goal.inflateMark_safety` as stated before the refusal clauses. -/
def Old.inflateMark_safety : Prop :=
  ∀ h r,
    StreamCallDomain .inflate h r (.inflateMark (some r)) →
    StreamCallSafe .inflate h r (.inflateMark (some r))

/-- `Goal.inflateGetHeader_safety` as stated before the refusal clauses. -/
def Old.inflateGetHeader_safety : Prop :=
  ∀ h r head,
    StreamCallDomain .inflate h r (.inflateGetHeader (some r) head) →
    StreamCallSafe .inflate h r (.inflateGetHeader (some r) head)

/-- `Goal.deflate_safety` as stated before the refusal clauses. -/
def Old.deflate_safety : Prop :=
  ∀ h r flush,
    StreamCallDomain .deflate h r (.deflate (some r) flush) →
    StreamCallSafe .deflate h r (.deflate (some r) flush)

/-- `Goal.deflateSetDictionary_safety` as stated before the refusal clauses. -/
def Old.deflateSetDictionary_safety : Prop :=
  ∀ h r dictionary dictLength,
    StreamCallDomain .deflate h r (.deflateSetDictionary (some r) dictionary dictLength) →
    StreamCallSafe .deflate h r (.deflateSetDictionary (some r) dictionary dictLength)

/-- `Goal.deflateGetDictionary_safety` as stated before the refusal clauses. -/
def Old.deflateGetDictionary_safety : Prop :=
  ∀ h r dictionary hasDictLength,
    StreamCallDomain .deflate h r (.deflateGetDictionary (some r) dictionary hasDictLength) →
    StreamCallSafe .deflate h r (.deflateGetDictionary (some r) dictionary hasDictLength)

/-- `Goal.deflateReset_safety` as stated before the refusal clauses. -/
def Old.deflateReset_safety : Prop :=
  ∀ h r,
    StreamCallDomain .deflate h r (.deflateReset (some r)) →
    StreamCallSafe .deflate h r (.deflateReset (some r))

/-- `Goal.deflateParams_safety` as stated before the refusal clauses. -/
def Old.deflateParams_safety : Prop :=
  ∀ h r level strategy,
    StreamCallDomain .deflate h r (.deflateParams (some r) level strategy) →
    StreamCallSafe .deflate h r (.deflateParams (some r) level strategy)

/-- `Goal.deflateTune_safety` as stated before the refusal clauses. -/
def Old.deflateTune_safety : Prop :=
  ∀ h r good_length max_lazy nice_length max_chain,
    StreamCallDomain .deflate h r (.deflateTune (some r) good_length max_lazy nice_length max_chain) →
    StreamCallSafe .deflate h r (.deflateTune (some r) good_length max_lazy nice_length max_chain)

/-- `Goal.deflateBound_safety` as stated before the refusal clauses. -/
def Old.deflateBound_safety : Prop :=
  ∀ h r sourceLen,
    StreamCallDomain .deflate h r (.deflateBound (some r) sourceLen) →
    StreamCallSafe .deflate h r (.deflateBound (some r) sourceLen)

/-- `Goal.deflateBound_z_safety` as stated before the refusal clauses. -/
def Old.deflateBound_z_safety : Prop :=
  ∀ h r sourceLen,
    StreamCallDomain .deflate h r (.deflateBound_z (some r) sourceLen) →
    StreamCallSafe .deflate h r (.deflateBound_z (some r) sourceLen)

/-- `Goal.deflatePending_safety` as stated before the refusal clauses. -/
def Old.deflatePending_safety : Prop :=
  ∀ h r hasPending hasBits,
    StreamCallDomain .deflate h r (.deflatePending (some r) hasPending hasBits) →
    StreamCallSafe .deflate h r (.deflatePending (some r) hasPending hasBits)

/-- `Goal.deflateUsed_safety` as stated before the refusal clauses. -/
def Old.deflateUsed_safety : Prop :=
  ∀ h r hasBits,
    StreamCallDomain .deflate h r (.deflateUsed (some r) hasBits) →
    StreamCallSafe .deflate h r (.deflateUsed (some r) hasBits)

/-- `Goal.deflatePrime_safety` as stated before the refusal clauses. -/
def Old.deflatePrime_safety : Prop :=
  ∀ h r bits value,
    StreamCallDomain .deflate h r (.deflatePrime (some r) bits value) →
    StreamCallSafe .deflate h r (.deflatePrime (some r) bits value)

/-- `Goal.deflateSetHeader_safety` as stated before the refusal clauses. -/
def Old.deflateSetHeader_safety : Prop :=
  ∀ h r head,
    StreamCallDomain .deflate h r (.deflateSetHeader (some r) head) →
    StreamCallSafe .deflate h r (.deflateSetHeader (some r) head)

/-- `Goal.inflateEnd_safety` as stated before the refusal clauses. -/
def Old.inflateEnd_safety : Prop :=
  ∀ h r, StreamReachable .inflate h r →
    ∃ rc after z, C.run (Zlib.Inflate.inflateEnd (some r)) h = .ok (rc, after) ∧ rc = Z_OK ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r)

/-- `Goal.deflateEnd_safety` as stated before the refusal clauses. -/
def Old.deflateEnd_safety : Prop :=
  ∀ h r, StreamReachable .deflate h r →
    ∃ rc after z, C.run (Zlib.Deflate.deflateEnd (some r)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ rc = Z_DATA_ERROR) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r)

/-- `Goal.deflateCopy_safety` as stated before the refusal clauses. -/
def Old.deflateCopy_safety : Prop :=
  (∀ h source, C.run (Zlib.Deflate.deflateCopy none source) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h dest z, dest.get h = some z →
    C.run (Zlib.Deflate.deflateCopy (some dest) none) h =
      .ok (Z_STREAM_ERROR, dest.put h { z with state := none })) ∧
  (∀ h source i z s dest oldDest,
    StreamReachable .deflate h source → Zlib.Deflate.Spec.DGood h source i z s →
    Zlib.Deflate.Spec.DefAlloc z → source ≠ dest → dest.get h = some oldDest →
    ∃ rc after,
      C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      source.get after = some z ∧ after.dstates i = some s ∧ Frame h after (StreamRoot dest) ∧
      ((rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
        dest.get after = some { oldDest with state := none } ∧
        LiveChange h after (fun _ => False) (fun _ => False)) ∨
       (rc = Z_OK ∧ (∃ i' z' s', Zlib.Deflate.Spec.DGood after dest i' z' s' ∧ Zlib.Deflate.Spec.DefAlloc z') ∧
       ∃ copied,
         after.dstates h.nextBlk = some copied ∧
         (∀ b, DeflateOwned h.nextBlk copied b ↔ h.nextBlk ≤ b ∧ b < h.nextBlk + 5) ∧
         LiveChange h after (DeflateOwned h.nextBlk copied) (fun _ => False)))) ∧
  (∀ h source dest zs oldDest, source.get h = some zs → dest.get h = some oldDest →
    (zs.zalloc = .null ∨ zs.zfree = .null ∨ zs.state = none) →
    C.run (Zlib.Deflate.deflateCopy (some dest) (some source)) h =
      .ok (Z_STREAM_ERROR, dest.put h { oldDest with state := none }))

/-- `Goal.inflateCopy_safety` as stated before the refusal clauses. -/
def Old.inflateCopy_safety : Prop :=
  (∀ h source, C.run (Zlib.Inflate.inflateCopy none source) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h dest z, dest.get h = some z →
    C.run (Zlib.Inflate.inflateCopy (some dest) none) h =
      .ok (Z_STREAM_ERROR, dest.put h { z with state := none })) ∧
  (∀ h source i z s dest oldDest,
    StreamReachable .inflate h source → Zlib.Inflate.Spec.Good h source i z s →
    Zlib.Inflate.Spec.DefAlloc z → source ≠ dest → dest.get h = some oldDest →
    ∃ rc after,
      C.run (Zlib.Inflate.inflateCopy (some dest) (some source)) h = .ok (rc, after) ∧
      source.get after = some z ∧ after.istates i = some s ∧ Frame h after (StreamRoot dest) ∧
      ((rc = Z_MEM_ERROR ∧ AllocationFailed h after ∧
        dest.get after = some { oldDest with state := none } ∧
        LiveChange h after (fun _ => False) (fun _ => False)) ∨
       (rc = Z_OK ∧ StreamReachable .inflate after dest ∧
        ∃ copied, after.istates h.nextBlk = some copied ∧
          (∀ b, InflateOwned h.nextBlk copied b → h.nextBlk ≤ b) ∧
          LiveChange h after (InflateOwned h.nextBlk copied) (fun _ => False))))

/-- The new `Goal.inflate_safety` implies the old one: its second conjunct. -/
theorem inflate_safety_strengthens : Goal.inflate_safety → Old.inflate_safety := fun g => g.2

/-- The new `Goal.inflateSetDictionary_safety` implies the old one: its second conjunct. -/
theorem inflateSetDictionary_safety_strengthens : Goal.inflateSetDictionary_safety → Old.inflateSetDictionary_safety := fun g => g.2

/-- The new `Goal.inflateGetDictionary_safety` implies the old one: its second conjunct. -/
theorem inflateGetDictionary_safety_strengthens : Goal.inflateGetDictionary_safety → Old.inflateGetDictionary_safety := fun g => g.2

/-- The new `Goal.inflateSync_safety` implies the old one: its second conjunct. -/
theorem inflateSync_safety_strengthens : Goal.inflateSync_safety → Old.inflateSync_safety := fun g => g.2

/-- The new `Goal.inflateReset_safety` implies the old one: its second conjunct. -/
theorem inflateReset_safety_strengthens : Goal.inflateReset_safety → Old.inflateReset_safety := fun g => g.2

/-- The new `Goal.inflateReset2_safety` implies the old one: its second conjunct. -/
theorem inflateReset2_safety_strengthens : Goal.inflateReset2_safety → Old.inflateReset2_safety := fun g => g.2

/-- The new `Goal.inflatePrime_safety` implies the old one: its second conjunct. -/
theorem inflatePrime_safety_strengthens : Goal.inflatePrime_safety → Old.inflatePrime_safety := fun g => g.2

/-- The new `Goal.inflateMark_safety` implies the old one: its second conjunct. -/
theorem inflateMark_safety_strengthens : Goal.inflateMark_safety → Old.inflateMark_safety := fun g => g.2

/-- The new `Goal.inflateGetHeader_safety` implies the old one: its second conjunct. -/
theorem inflateGetHeader_safety_strengthens : Goal.inflateGetHeader_safety → Old.inflateGetHeader_safety := fun g => g.2

/-- The new `Goal.deflate_safety` implies the old one: its second conjunct. -/
theorem deflate_safety_strengthens : Goal.deflate_safety → Old.deflate_safety := fun g => g.2

/-- The new `Goal.deflateSetDictionary_safety` implies the old one: its second conjunct. -/
theorem deflateSetDictionary_safety_strengthens : Goal.deflateSetDictionary_safety → Old.deflateSetDictionary_safety := fun g => g.2

/-- The new `Goal.deflateGetDictionary_safety` implies the old one: its second conjunct. -/
theorem deflateGetDictionary_safety_strengthens : Goal.deflateGetDictionary_safety → Old.deflateGetDictionary_safety := fun g => g.2

/-- The new `Goal.deflateReset_safety` implies the old one: its second conjunct. -/
theorem deflateReset_safety_strengthens : Goal.deflateReset_safety → Old.deflateReset_safety := fun g => g.2

/-- The new `Goal.deflateParams_safety` implies the old one: its second conjunct. -/
theorem deflateParams_safety_strengthens : Goal.deflateParams_safety → Old.deflateParams_safety := fun g => g.2

/-- The new `Goal.deflateTune_safety` implies the old one: its second conjunct. -/
theorem deflateTune_safety_strengthens : Goal.deflateTune_safety → Old.deflateTune_safety := fun g => g.2

/-- The new `Goal.deflateBound_safety` implies the old one: its second conjunct. -/
theorem deflateBound_safety_strengthens : Goal.deflateBound_safety → Old.deflateBound_safety := fun g => g.2

/-- The new `Goal.deflateBound_z_safety` implies the old one: its second conjunct. -/
theorem deflateBound_z_safety_strengthens : Goal.deflateBound_z_safety → Old.deflateBound_z_safety := fun g => g.2

/-- The new `Goal.deflatePending_safety` implies the old one: its second conjunct. -/
theorem deflatePending_safety_strengthens : Goal.deflatePending_safety → Old.deflatePending_safety := fun g => g.2

/-- The new `Goal.deflateUsed_safety` implies the old one: its second conjunct. -/
theorem deflateUsed_safety_strengthens : Goal.deflateUsed_safety → Old.deflateUsed_safety := fun g => g.2

/-- The new `Goal.deflatePrime_safety` implies the old one: its second conjunct. -/
theorem deflatePrime_safety_strengthens : Goal.deflatePrime_safety → Old.deflatePrime_safety := fun g => g.2

/-- The new `Goal.deflateSetHeader_safety` implies the old one: its second conjunct. -/
theorem deflateSetHeader_safety_strengthens : Goal.deflateSetHeader_safety → Old.deflateSetHeader_safety := fun g => g.2

/-- The new `Goal.inflateEnd_safety` implies the old one: its second conjunct. -/
theorem inflateEnd_safety_strengthens : Goal.inflateEnd_safety → Old.inflateEnd_safety := fun g => g.2

/-- The new `Goal.deflateEnd_safety` implies the old one: its second conjunct. -/
theorem deflateEnd_safety_strengthens : Goal.deflateEnd_safety → Old.deflateEnd_safety := fun g => g.2

/-- The new `Goal.deflateCopy_safety` implies the old one: a source with a `NULL` `zalloc`, `zfree` or
state is in `RefusedDeflate`. -/
theorem deflateCopy_safety_strengthens : Goal.deflateCopy_safety → Old.deflateCopy_safety :=
  fun g => ⟨g.1, g.2.1, g.2.2.1, fun h source dest zs oldDest sget dget bad =>
    g.2.2.2 h source dest oldDest dget (Or.inr ⟨source, zs, rfl, sget, by
      rcases bad with b | b | b
      · exact Or.inl b
      · exact Or.inr (Or.inl b)
      · exact Or.inr (Or.inr (Or.inl b))⟩)⟩

/-- The new `Goal.inflateCopy_safety` implies the old one: its first three clauses. -/
theorem inflateCopy_safety_strengthens : Goal.inflateCopy_safety → Old.inflateCopy_safety :=
  fun g => ⟨g.1, g.2.1, g.2.2.1⟩

end ZlibF.Spec.Public.RefusalStrengthening
