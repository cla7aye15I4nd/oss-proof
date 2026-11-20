import ZlibNgF.Proof.«deflate.c.keep»
import ZlibNgF.Proof.«gzwrite.c.needs»

/-!
# `deflate` and `deflateParams` keep what the gz write side needs (`ZlibNgF`)

The `DKeep` conjuncts of the `deflate` and `deflateParams` fields of `GzWriteNeeds.DeflateGz`: every run that returns,
whatever its result and from any heap, keeps the saved pointers of every block, `DFreshBlocks`, and the registered
`gz_header` (`Proof/deflate.c.keep.lean`: `K.ZlibNg.Deflate.deflate`, `K.ZlibNg.Deflate.deflateParams`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateGz
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate
open ZlibNgF.Proof.GzWriteNeeds (DKeep)
open ZlibNgF.Proof.DeflateKeep (DR)

theorem dstate_of_dr {h h' : Heap} (k : DR h h') {b : Nat} {st' : DeflateState} (e : h'.dstate b = some st') :
    ∃ st, h.dstate b = some st ∧ st.gzhead = st'.gzhead := by
  unfold Heap.dstate at e
  cases hb' : h'.bytes b with
  | none => rw [hb'] at e; cases e
  | some a' =>
    rw [hb'] at e
    simp only at e
    have hbl := k.bl b
    rw [hb'] at hbl
    cases hb : h.bytes b with
    | none => rw [hb] at hbl; cases hbl
    | some a =>
      have hds := k.ds b
      rw [e] at hds
      cases hs : h.dstates b with
      | none => rw [hs] at hds; cases hds
      | some st =>
        rw [hs] at hds
        refine ⟨st, ?_, (Option.some.inj hds).symm⟩
        unfold Heap.dstate; rw [hb, hs]

/-- `DR` gives `DKeep`. -/
theorem dkeep_of_dr {h h' : Heap} (s : StreamPtr) (k : DR h h') : DKeep h h' s := by
  refine ⟨fun c _ _ => by rw [k.sp], fun f => ⟨fun b hb => ?_, fun b hb => ?_⟩, fun hp hreg => Or.inr ?_⟩
  · rw [k.nb] at hb
    obtain ⟨e1, e2, e3⟩ := f.1 b hb
    refine ⟨by rw [k.ist]; exact e1, by rw [k.ial]; exact e2, ?_⟩
    have := k.bl b
    rw [e3] at this
    cases h3 : h'.bytes b with
    | none => rfl
    | some _ => rw [h3] at this; cases this
  · rw [k.nb] at hb
    obtain ⟨e1, e2⟩ := f.2 b hb
    refine ⟨?_, by rw [k.dal]; exact e2⟩
    have := k.ds b
    rw [e1] at this
    cases h3 : h'.dstates b with
    | none => rfl
    | some _ => rw [h3] at this; cases this
  · obtain ⟨b, st', ⟨⟨z', ⟨i, rfl, hz'⟩, hzb⟩, hst'⟩, hg⟩ := hreg
    have hzs := k.zs i
    rw [hz'] at hzs
    cases hz : h.streams i with
    | none => rw [hz] at hzs; cases hzs
    | some z =>
      rw [hz] at hzs
      obtain ⟨st, hst, hgz⟩ := dstate_of_dr k hst'
      refine ⟨b, st, ⟨⟨z, ⟨i, rfl, hz⟩, ?_⟩, hst⟩, hgz.trans hg⟩
      rw [← hzb]; exact (Option.some.inj hzs).symm

/-- **`deflate` keeps what the gz write side needs** (the `DKeep` conjunct of the `deflate` field of
`GzWriteNeeds.DeflateGz`), for every run that returns, whatever the result. -/
theorem deflate_keep (h h' : Heap) (s : StreamPtr) (flush r : Int32)
    (e : C.run (deflate s flush) h = .ok (r, h')) : DKeep h h' s :=
  dkeep_of_dr s ((DeflateKeep.K.ZlibNg.Deflate.deflate s flush).run h r h' e)

/-- **`deflateParams` keeps what the gz write side needs** (the `DKeep` conjunct of the `deflateParams` field of
`GzWriteNeeds.DeflateGz`), for every run that returns, whatever the result. -/
theorem params_keep (h h' : Heap) (s : StreamPtr) (level strategy r : Int32)
    (e : C.run (deflateParams s level strategy) h = .ok (r, h')) : DKeep h h' s :=
  dkeep_of_dr s ((DeflateKeep.K.ZlibNg.Deflate.deflateParams s level strategy).run h r h' e)

end ZlibNgF.Proof.DeflateGz
