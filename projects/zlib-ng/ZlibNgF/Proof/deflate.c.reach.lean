import ZlibNgF.Proof.«public-deflate-bound»
import ZlibNgF.Proof.«inflate.c.reach»
import ZlibNgF.Proof.«public-deflate-init»
import ZlibNgF.Proof.«deflate.c.reset»
import ZlibNgF.Proof.«deflate.c.prime»
import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«deflate.c.setdict»
import ZlibNgF.Proof.«deflate.c.fill_window.facts»
import ZlibNgF.Proof.«deflate.c.copy»
import ZlibNgF.Proof.«deflate.c.side»

/-!
# Reachable deflate streams have the structural invariant (`ZlibNgF`)

`dreach (P : DPending) : DeflateReachable h s → DInv h s ∧ DSide h s`, by induction over `DeflateReachable`, as
`InflateReach.reach_inv` on the inflate side: the structural invariant and the between-call facts
(`Proof/deflate.c.side.lean`). The constructor cases proved: `deflateInit_` and `deflateInit2_`
(`Proof/public-deflate-init.lean`), the caller step, the copy constructor (`Proof/deflate.c.copy.lean`), and the
steps `deflatePending`, `deflateUsed`, `deflateTune`, `deflateSetHeader`, `deflateBound`, `deflateBound_z`,
`deflateReset`, `deflateResetKeep` (on a stream with nothing unfinished), `deflateGetDictionary`
(`Proof/deflate.c.dict.lean`), `deflatePrime` (`Proof/deflate.c.prime.lean`), `deflateSetDictionary`
(`Proof/deflate.c.setdict.lean`, with the window facts `FillFacts.windowFacts`), and `deflateCopy` on the source.
Every other case is a field of `DPending`, the list of obligations not proved yet: `deflate` and `deflateParams`, and
the hash chains (`ChainOk`, the last part of `DSide`) after `deflateCopy` (destination) and
`deflateSetDictionary` (after `deflateInit_`, `deflateInit2_` and `deflateReset` they follow from `lm_init`'s
`CLEAR_HASH`, `FreshHead`; `deflateResetKeep` keeps them).
The `*_safety_of` theorems derive registered goals from `DPending`; a goal is registered as proved only once
`DPending` is.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateReach
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv

open ZlibNgF.Proof.DeflateSide (DSide)
open ZlibNgF.Proof.DeflateFacts (ChainOk DStateIs)

/-- The hash chains of stream `s` in `h` (`ChainOk` of its state, the part of `DSide` about `head` / `prev`). -/
def DChain (h : Heap) (s : StreamPtr) : Prop := ∀ b st d, DStateIs h s b st → h.bytes b = some d → ChainOk b d st

/-- The obligations still to prove: each remaining public step keeps the invariant and the between-call facts
(`DSide`). -/
structure DPending : Prop where
  deflate : ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → DSide h s → CrcGlobals h →
    DStreamIO h s → C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h') → DInv h' s ∧ DSide h' s
  params : ∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DInv h s → DSide h s → CrcGlobals h →
    DStreamIO h s → C.run (ZlibNg.Deflate.deflateParams s level strategy) h = .ok (r, h') → DInv h' s ∧ DSide h' s
  copy_chain : ∀ (h h' : Heap) (src dst : StreamPtr), DInv h src → DSide h src → DFreshBlocks h → InitReady h dst →
    dst ≠ src → C.run (ZlibNg.Deflate.deflateCopy dst src) h = .ok (Z_OK, h') → DChain h' dst
  setDict_chain : ∀ (h h' : Heap) (s : StreamPtr) (d : BPtr) (n : UInt32) (r : Int32), DInv h s → DSide h s →
    DictReady h s → NullOrRead h d n.toNat → (∀ b, StateBlock h s b → NotInBlock b d) →
    C.run (ZlibNg.Deflate.deflateSetDictionary s d n) h = .ok (r, h') → DChain h' s

/-- Two runs of one computation on one heap agree. -/
theorem det {α : Type} {m : M α} {h h' h'' : Heap} {r r' : α} (e : C.run m h = .ok (r, h'))
    (e' : C.run m h = .ok (r', h'')) : h' = h'' := by
  rw [e] at e'; cases e'; rfl

/-- A caller step keeps the invariant: it changes only the buffer fields of the `z_stream`, and neither the state
nor the allocation record of the stream's block. -/
theorem caller_inv {h h' : Heap} {s : StreamPtr} (hv : DInv h s) (hc : DCallerStep h h' s) : DInv h' s := by
  obtain ⟨i, z, b, st, al, rfl, hz, hb, hst, hal, c⟩ := hv
  obtain ⟨i', z1, z', b', st1, e1, hz1, hz', hb', _, ez, hbytes, hdstates, hdallocs, _, _, _⟩ := hc
  obtain rfl : i' = i := (Option.some.inj e1).symm
  obtain rfl : z1 = z := Option.some.inj (hz1.symm.trans hz)
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs' : z'.state = z1.state := by rw [ez]
  have hst' : h'.dstate b' = some st := by simp only [Heap.dstate, hbytes, hdstates]; exact hst
  have hal' : h'.dallocsOf b' = some al := by simp only [Heap.dallocsOf, hbytes, hdallocs]; exact hal
  refine ⟨i', z', b', st, al, rfl, hz', hs'.trans hb, hst', hal', ?_⟩
  have za : z'.zalloc = z1.zalloc := by rw [ez]
  have zf : z'.zfree = z1.zfree := by rw [ez]
  exact { DCore.of_heap hbytes c with zalloc := za.trans c.zalloc, zfree := zf.trans c.zfree }

/-- Every public step keeps the invariant and `DSide`, given the pending preservation lemmas. -/
theorem step_inv (P : DPending) {h h' : Heap} {s : StreamPtr} (hv : DInv h s) (hsd : DSide h s)
    (hs : DeflateStep h h' s) : DInv h' s ∧ DSide h' s := by
  rcases hs with ⟨flush, r, hcg, hio, e⟩ | ⟨level, strategy, r, hcg, hio, e⟩ | ⟨d, n, r, hdr, hd, hnb, e⟩ |
    ⟨d, hasLen, r, hd, hnb, hdis, e⟩ | ⟨hp, r, hbf, _, e⟩ | ⟨hp, hb, r, e⟩ | ⟨hb, r, e⟩ | ⟨bits, value, r, hpr, e⟩ |
    ⟨g, l, n, c, r, e⟩ | ⟨n, r, e⟩ | ⟨n, r, e⟩ | ⟨r, e⟩ | ⟨r, hrk, e⟩ | ⟨dst, r, hfr, hdst, hne, e⟩
  · exact P.deflate h h' s flush r hv hsd hcg hio e
  · exact P.params h h' s level strategy r hv hsd hcg hio e
  · obtain ⟨_, _, e0, hi, _⟩ := DeflateSetDict.setDict_inv FillFacts.windowFacts hv hd hnb
    rw [det e e0]
    have hs' := DeflateSide.setDict_side hv hsd hdr hd hnb e (P.setDict_chain h h' s d n r hv hsd hdr hd hnb e)
    exact ⟨hi, by rw [← det e e0]; exact hs'⟩
  · obtain ⟨_, _, e0, hi, _⟩ := DeflateDict.getDict_inv hasLen hv hd hnb
    rw [det e e0]
    exact ⟨hi, by rw [← det e e0]; exact DeflateSide.getDict_side hv hsd hd hnb hdis e⟩
  · refine ⟨?_, DeflateSide.setHeader_side hv hsd hbf e⟩
    rcases DeflateControl.deflateSetHeader_inv hv hp with e0 | ⟨_, _, _, _, _, _, _, _, e0, hi⟩
    · rw [det e e0]; exact hv
    · rw [det e e0]; exact hi
  · obtain ⟨_, e0⟩ := DeflateControl.deflatePending_inv hv hp hb
    rw [det e e0]; exact ⟨hv, hsd⟩
  · obtain ⟨_, e0⟩ := DeflateControl.deflateUsed_inv hv hb
    rw [det e e0]; exact ⟨hv, hsd⟩
  · obtain ⟨_, _, _, _, _, _, _, _, e0, _, _, hi⟩ := DeflatePrime.prime_inv hv bits value
    rw [det e e0]
    exact ⟨hi hpr, by rw [← det e e0]; exact DeflateSide.prime_side hv hsd e⟩
  · obtain ⟨_, _, _, _, _, _, _, _, e0, hi⟩ := DeflateControl.deflateTune_inv hv g l n c
    obtain ⟨_, e1, hs1⟩ := DeflateSide.tune_side hv hsd g l n c
    rw [det e e0]
    exact ⟨hi, by rw [← det e e0, det e e1]; exact hs1⟩
  · rw [DeflateBound.RO.deflateBound s n h r h' e]; exact ⟨hv, hsd⟩
  · rw [DeflateBound.RO.deflateBound_z s n h r h' e]; exact ⟨hv, hsd⟩
  · obtain ⟨_, _, _, rfl, _, _, _, H, e0, ⟨_, hi, _, hq⟩⟩ := DeflateReset.reset_inv hv
    rw [det e e0]; exact ⟨hi, DeflateSide.side_fresh hi hq⟩
  · have hs' := DeflateSide.resetKeep_side hv hsd hrk e
    obtain ⟨_, _, _, rfl, _, _, _, H, e0, ⟨_, hi, _, _⟩⟩ := DeflateReset.resetKeep_inv hv
    rw [det e e0] at hs' ⊢
    exact ⟨hi, hs'⟩
  · exact ⟨(DeflateCopy.copy_inv hv hdst hne e).1, DeflateSide.copy_src_side hv hsd hfr hdst hne e⟩

/-- **The induction.** Every reachable deflate stream has the structural invariant and `DSide`, given the pending
obligations. -/
theorem dreach (P : DPending) {h : Heap} {s : StreamPtr} (hr : DeflateReachable h s) : DInv h s ∧ DSide h s := by
  induction hr with
  | init h h' s level version size hi hv e =>
    obtain ⟨a, b⟩ := DeflateInitPublic.init_inv h h' s level version size hi hv e
    exact ⟨a, DeflateSide.side_fresh a b⟩
  | init2 h h' s level method wb ml st version size hi hv e =>
    obtain ⟨a, b⟩ := DeflateInitPublic.init2__inv h h' s level method wb ml st version size hi hv e
    exact ⟨a, DeflateSide.side_fresh a b⟩
  | copy h h' src dst _ hfr hdst hne e ih =>
    obtain ⟨hv', hc⟩ := (DeflateCopy.copy_inv ih.1 hdst hne e).2 rfl
    obtain ⟨r0, h0, e0, f⟩ := DeflateCopy.copy_safe ih.1 hfr hdst hne
    rw [← det e e0] at f
    exact ⟨hv', DeflateSide.copy_side ih.2 hfr hc f (P.copy_chain h h' src dst ih.1 ih.2 hfr hdst hne e)⟩
  | step h h' s _ hs ih => exact step_inv P ih.1 ih.2 hs
  | caller h h' s _ hc ih => exact ⟨caller_inv ih.1 hc, DeflateSide.caller_side ih.2 hc⟩

/-- Every reachable deflate stream has the structural invariant, given the pending obligations. -/
theorem dreach_inv (P : DPending) {h : Heap} {s : StreamPtr} (hr : DeflateReachable h s) : DInv h s :=
  (dreach P hr).1

/-! ## Registered goals, given `DPending` -/

open ZlibNgF.Spec.Safety

/-- `DeflateHandle` is `DNoState` or reachable. -/
theorem handle_cases {h : Heap} {s : StreamPtr} (hh : DeflateHandle h s) : DNoState h s ∨ DeflateReachable h s := by
  rcases hh with hn | hn | hr
  · exact Or.inl (Or.inl hn)
  · exact Or.inl (Or.inr hn)
  · exact Or.inr hr

theorem dframe_refl (h : Heap) (a b c : List Nat) (w : List (BPtr × Nat)) : DFrame h h a b c w :=
  ⟨InflateInit.frame_refl h a b c w, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem stateIds_of {h : Heap} {i : Nat} {z : ZStream} {b : Nat} (hz : h.streams i = some z)
    (hb : z.state = some b) : stateIds h (some i) = [b] := by
  simp [stateIds, hz, hb]

/-- The frame of a store into the state of the stream's block. -/
theorem dframe_setD {h : Heap} {i : Nat} {z : ZStream} {b : Nat} (st' : DeflateState)
    (hz : h.streams i = some z) (hb : z.state = some b) (S G : List Nat) (w : List (BPtr × Nat)) :
    DFrame h { h with dstates := upd h.dstates b (some st') } S (stateIds h (some i)) G w := by
  rw [stateIds_of hz hb]
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ data hd => ⟨data, hd, rfl,
    fun _ _ _ => rfl⟩, fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun c _ hc => ⟨?_, rfl⟩⟩
  exact upd_ne _ _ _ _ (by simpa using hc)

theorem deflatePending_safety_of (P : DPending) : Goal.deflatePending_safety := by
  intro h s hp hb hh
  rcases handle_cases hh with hn | hr
  · exact DeflateControl.deflatePending_noState hn hp hb
  · exact DeflateControl.deflatePending_inv (dreach_inv P hr) hp hb

theorem deflateUsed_safety_of (P : DPending) : Goal.deflateUsed_safety := by
  intro h s hb hh
  rcases handle_cases hh with hn | hr
  · exact DeflateControl.deflateUsed_noState hn hb
  · exact DeflateControl.deflateUsed_inv (dreach_inv P hr) hb

theorem deflateTune_safety_of (P : DPending) : Goal.deflateTune_safety := by
  intro h s g l n c hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateControl.deflateTune_noState hn g l n c, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, st, rfl, hz, hzb, _, e, _⟩ := DeflateControl.deflateTune_inv (dreach_inv P hr) g l n c
    exact ⟨_, _, e, dframe_setD _ hz hzb _ _ _⟩

theorem deflateSetHeader_safety_of (P : DPending) : Goal.deflateSetHeader_safety := by
  intro h s hp hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateControl.deflateSetHeader_noState hn hp, dframe_refl h _ _ _ _⟩
  · rcases DeflateControl.deflateSetHeader_inv (dreach_inv P hr) hp with e | ⟨i, z, b, st, rfl, hz, hzb, _, e, _⟩
    · exact ⟨_, _, e, dframe_refl h _ _ _ _⟩
    · exact ⟨_, _, e, dframe_setD _ hz hzb _ _ _⟩

theorem deflateEnd_safety_of (P : DPending) : Goal.deflateEnd_safety := by
  intro h s hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateControl.deflateEnd_noState hn, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, r, rfl, hz, hzb, e⟩ := DeflateControl.deflateEnd_inv (dreach_inv P hr)
    refine ⟨r, _, e, ?_⟩
    rw [stateIds_of hz hzb]
    refine ⟨InflateReach.frame_of (fun c hc => upd_ne _ _ _ _ (by simpa [streamIds] using hc)) (fun _ _ => rfl)
      (fun c hc => ⟨rfl, rfl, upd_ne _ _ _ _ (by simpa using hc)⟩) rfl rfl rfl rfl (Nat.le_refl _),
      fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem deflateBound_safety_of (P : DPending) : Goal.deflateBound_safety := by
  intro h s n hh hr hob
  rcases handle_cases hh with hn | hre
  · exact DeflateBound.deflateBound_noState hn n
  · exact DeflateBound.deflateBound_inv (dreach_inv P hre) hr hob n

theorem deflateBound_z_safety_of (P : DPending) : Goal.deflateBound_z_safety := by
  intro h s n hh hr hob
  rcases handle_cases hh with hn | hre
  · exact DeflateBound.deflateBound_z_noState hn n
  · exact DeflateBound.deflateBound_z_inv (dreach_inv P hre) hr hob n

theorem deflateReset_safety_of (P : DPending) : Goal.deflateReset_safety := by
  intro h s hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateReset.reset_noState hn, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, ⟨_, _, f, _⟩⟩ := DeflateReset.reset_inv (dreach_inv P hr)
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateResetKeep_safety_of (P : DPending) : Goal.deflateResetKeep_safety := by
  intro h s hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateReset.resetKeep_noState hn, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, ⟨_, _, f, _⟩⟩ := DeflateReset.resetKeep_inv (dreach_inv P hr)
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateGetDictionary_safety_of (P : DPending) : Goal.deflateGetDictionary_safety := by
  intro h s d hasLen hh hd hnb
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateDict.getDict_noState hn d hasLen, dframe_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f, _⟩ := DeflateDict.getDict_inv hasLen (dreach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

theorem deflatePrime_safety_of (P : DPending) : Goal.deflatePrime_safety := by
  intro h s bits value hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflatePrime.prime_noState hn bits value, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, f, _, _⟩ := DeflatePrime.prime_inv (dreach_inv P hr) bits value
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateSetDictionary_safety_of (P : DPending) : Goal.deflateSetDictionary_safety := by
  intro h s d n hh hd hnb
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateSetDict.setDict_noState hn d n, dframe_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f, _⟩ := DeflateSetDict.setDict_inv FillFacts.windowFacts (dreach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

theorem deflateCopy_safety_of (P : DPending) : Goal.deflateCopy_safety := by
  intro h dst src hfr hh hdst hne
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateCopy.copy_noState hn dst, dframe_refl h _ _ _ _⟩
  · exact DeflateCopy.copy_safe (dreach_inv P hr) hfr hdst hne

end ZlibNgF.Proof.DeflateReach
