import ZlibF.Proof.«public-inflate-sequence-safety»
import ZlibF.Proof.«public-deflate-goals»
import ZlibF.Spec.Safety.Streams

/-!
# Per-function safety of the inflate and deflate functions

Each theorem proves one goal of `ZlibF/Spec/Safety/Streams.lean` as a corollary of the sequence
safety theorems `Zlib.Inflate.Proofs.inflate_sequence_safety_public` (clauses 2 and 3 of
`StreamSequenceSafety .inflate`) and `Zlib.Deflate.Universal.deflate_sequence_safety`.
-/

namespace ZlibF.Spec.Public.StreamCallSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

/-- `Goal.inflate_safety`: one call of `inflate` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflate_safety : Goal.inflate_safety :=
  fun h r flush d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateSetDictionary_safety`: one call of `inflateSetDictionary` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateSetDictionary_safety : Goal.inflateSetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateGetDictionary_safety`: one call of `inflateGetDictionary` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateGetDictionary_safety : Goal.inflateGetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateSync_safety`: one call of `inflateSync` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateSync_safety : Goal.inflateSync_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateReset_safety`: one call of `inflateReset` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateReset_safety : Goal.inflateReset_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateReset2_safety`: one call of `inflateReset2` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateReset2_safety : Goal.inflateReset2_safety :=
  fun h r windowBits d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflatePrime_safety`: one call of `inflatePrime` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflatePrime_safety : Goal.inflatePrime_safety :=
  fun h r bits value d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateMark_safety`: one call of `inflateMark` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateMark_safety : Goal.inflateMark_safety :=
  fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateGetHeader_safety`: one call of `inflateGetHeader` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. -/
theorem inflateGetHeader_safety : Goal.inflateGetHeader_safety :=
  fun h r head d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflate_safety`: one call of `deflate` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflate_safety : Goal.deflate_safety :=
  fun h r flush d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateSetDictionary_safety`: one call of `deflateSetDictionary` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateSetDictionary_safety : Goal.deflateSetDictionary_safety :=
  fun h r dictionary dictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateGetDictionary_safety`: one call of `deflateGetDictionary` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateGetDictionary_safety : Goal.deflateGetDictionary_safety :=
  fun h r dictionary hasDictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateReset_safety`: one call of `deflateReset` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateReset_safety : Goal.deflateReset_safety :=
  fun h r d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateParams_safety`: one call of `deflateParams` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateParams_safety : Goal.deflateParams_safety :=
  fun h r level strategy d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateTune_safety`: one call of `deflateTune` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateTune_safety : Goal.deflateTune_safety :=
  fun h r good_length max_lazy nice_length max_chain d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateBound_safety`: one call of `deflateBound` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateBound_safety : Goal.deflateBound_safety :=
  fun h r sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateBound_z_safety`: one call of `deflateBound_z` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateBound_z_safety : Goal.deflateBound_z_safety :=
  fun h r sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflatePending_safety`: one call of `deflatePending` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflatePending_safety : Goal.deflatePending_safety :=
  fun h r hasPending hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateUsed_safety`: one call of `deflateUsed` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateUsed_safety : Goal.deflateUsed_safety :=
  fun h r hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflatePrime_safety`: one call of `deflatePrime` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflatePrime_safety : Goal.deflatePrime_safety :=
  fun h r bits value d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.deflateSetHeader_safety`: one call of `deflateSetHeader` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. -/
theorem deflateSetHeader_safety : Goal.deflateSetHeader_safety :=
  fun h r head d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2

/-- `Goal.inflateEnd_safety`: `inflateEnd` is safe on a stream that holds the inflate sequence invariant; clause 3 (End) of the inflate sequence theorem. -/
theorem inflateEnd_safety : Goal.inflateEnd_safety := by
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨hk, _⟩
  · exact hrc
  · cases hk

/-- `Goal.deflateEnd_safety`: `deflateEnd` is safe on a stream that holds the deflate sequence invariant; clause 3 (End) of the deflate sequence theorem. -/
theorem deflateEnd_safety : Goal.deflateEnd_safety := by
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Deflate.Universal.deflate_sequence_safety.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨_, hrc⟩
  · exact Or.inl hrc
  · exact Or.inr hrc

end ZlibF.Spec.Public.StreamCallSafetyProof
