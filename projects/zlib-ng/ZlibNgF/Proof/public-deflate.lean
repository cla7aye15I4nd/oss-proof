import ZlibNgF.Proof.«deflate.c.body.ok»
import ZlibNgF.Proof.«deflate_quick.c.static»
import ZlibNgF.Proof.«deflate_fast.c.safety»
import ZlibNgF.Proof.«deflate_medium.c.safety»
import ZlibNgF.Proof.«deflate_slow.c.safety»

/-!
# The safety of `deflate` and the deflate control functions (`ZlibNgF`)

`strategyFacts`: every strategy of the configuration table (and `deflate_huff`, `deflate_rle`) meets its contract,
given the block emitters (`TreesFactsP.treesFacts`). With it, `deflate` keeps the invariant (`DeflateBody.deflate_ok`),
so `DPending` holds, and every goal derived from `DPending` in `Proof/deflate.c.reach.lean` is proved.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflatePublic
open ZlibNgF.Spec.Safety ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateReach

/-- Every strategy meets its contract. -/
theorem strategyFacts : StrategyFacts :=
  let T := TreesFactsP.treesFacts
  let A := Strategy.strategiesA T
  ⟨A.1, A.2.1, FastP.fast_ok T, MediumLoop.medium_ok T, MediumLoop.medium_fizzle_ok T, SlowSafety.slow_ok T,
    A.2.2.1, A.2.2.2⟩

/-- The pending obligations of the reachability induction, proved. -/
theorem dpending : DPending := DeflateBody.dpending strategyFacts

theorem deflate_safety : Goal.deflate_safety := deflate_safety_of dpending
theorem deflateEnd_safety : Goal.deflateEnd_safety := deflateEnd_safety_of dpending
theorem deflateParams_safety : Goal.deflateParams_safety := deflateParams_safety_of dpending
theorem deflateTune_safety : Goal.deflateTune_safety := deflateTune_safety_of dpending
theorem deflatePrime_safety : Goal.deflatePrime_safety := deflatePrime_safety_of dpending
theorem deflateSetDictionary_safety : Goal.deflateSetDictionary_safety := deflateSetDictionary_safety_of dpending
theorem deflateGetDictionary_safety : Goal.deflateGetDictionary_safety := deflateGetDictionary_safety_of dpending
theorem deflateSetHeader_safety : Goal.deflateSetHeader_safety := deflateSetHeader_safety_of dpending
theorem deflatePending_safety : Goal.deflatePending_safety := deflatePending_safety_of dpending
theorem deflateUsed_safety : Goal.deflateUsed_safety := deflateUsed_safety_of dpending
theorem deflateBound_safety : Goal.deflateBound_safety := deflateBound_safety_of dpending
theorem deflateBound_z_safety : Goal.deflateBound_z_safety := deflateBound_z_safety_of dpending
theorem deflateReset_safety : Goal.deflateReset_safety := deflateReset_safety_of dpending
theorem deflateResetKeep_safety : Goal.deflateResetKeep_safety := deflateResetKeep_safety_of dpending
theorem deflateCopy_safety : Goal.deflateCopy_safety := deflateCopy_safety_of dpending

end ZlibNgF.Proof.DeflatePublic
