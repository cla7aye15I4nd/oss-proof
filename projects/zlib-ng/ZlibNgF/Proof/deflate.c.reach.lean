import ZlibNgF.Proof.«public-deflate-bound»
import ZlibNgF.Proof.«inflate.c.reach»
import ZlibNgF.Proof.«public-deflate-init»
import ZlibNgF.Proof.«deflate.c.reset»
import ZlibNgF.Proof.«deflate.c.prime»
import ZlibNgF.Proof.«deflate.c.facts»
import ZlibNgF.Proof.«deflate.c.setdict»
import ZlibNgF.Proof.«deflate.c.fill_window.facts»

/-!
# Reachable deflate streams have the structural invariant (`ZlibNgF`)

`dreach_inv (P : DPending) : DeflateReachable h s → DInv h s`, by induction over `DeflateReachable`, as
`InflateReach.reach_inv` on the inflate side. The constructor cases proved: `deflateInit_` and `deflateInit2_`
(`Proof/public-deflate-init.lean`), the caller step, and the steps `deflatePending`, `deflateUsed`, `deflateTune`,
`deflateSetHeader`, `deflateBound`, `deflateBound_z`, `deflateReset`, `deflateResetKeep`, `deflateGetDictionary`
(`Proof/deflate.c.dict.lean`), `deflatePrime` (`Proof/deflate.c.prime.lean`), `deflateSetDictionary`
(`Proof/deflate.c.setdict.lean`, with the window facts `FillFacts.windowFacts`). Every other case is a field of
`DPending`, the list of obligations not proved yet: the preservation by `deflateCopy`, `deflate`, `deflateParams`. The `*_safety_of` theorems
derive registered goals from `DPending`; a goal is registered as proved only once `DPending` is.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateReach
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv

/-- The obligations still to prove: a successful copy establishes the invariant, and each remaining public step keeps
it. -/
structure DPending : Prop where
  /-- `deflateCopy` keeps the source's invariant and, on `Z_OK`, establishes the destination's. -/
  copy : ∀ (h h' : Heap) (src dst : StreamPtr) (r : Int32), DInv h src → InitReady h dst → dst ≠ src →
    C.run (ZlibNg.Deflate.deflateCopy dst src) h = .ok (r, h') → DInv h' src ∧ (r = Z_OK → DInv h' dst)
  deflate : ∀ (h h' : Heap) (s : StreamPtr) (flush r : Int32), DInv h s → CrcGlobals h → DStreamIO h s →
    C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h') → DInv h' s
  params : ∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DInv h s → CrcGlobals h → DStreamIO h s →
    C.run (ZlibNg.Deflate.deflateParams s level strategy) h = .ok (r, h') → DInv h' s

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

/-- Every public step keeps the invariant, given the pending preservation lemmas. -/
theorem step_inv (P : DPending) {h h' : Heap} {s : StreamPtr} (hv : DInv h s) (hs : DeflateStep h h' s) :
    DInv h' s := by
  rcases hs with ⟨flush, r, hcg, hio, e⟩ | ⟨level, strategy, r, hcg, hio, e⟩ | ⟨d, n, r, hd, hnb, e⟩ |
    ⟨d, hasLen, r, hd, hnb, e⟩ | ⟨hp, r, _, _, e⟩ | ⟨hp, hb, r, e⟩ | ⟨hb, r, e⟩ | ⟨bits, value, r, hpr, e⟩ |
    ⟨g, l, n, c, r, e⟩ | ⟨n, r, e⟩ | ⟨n, r, e⟩ | ⟨r, e⟩ | ⟨r, e⟩ | ⟨dst, r, hdst, hne, e⟩
  · exact P.deflate h h' s flush r hv hcg hio e
  · exact P.params h h' s level strategy r hv hcg hio e
  · obtain ⟨_, _, e0, hi, _⟩ := DeflateSetDict.setDict_inv FillFacts.windowFacts hv hd hnb
    rw [det e e0]; exact hi
  · obtain ⟨_, _, e0, hi, _⟩ := DeflateDict.getDict_inv hasLen hv hd hnb
    rw [det e e0]; exact hi
  · rcases DeflateControl.deflateSetHeader_inv hv hp with e0 | ⟨_, _, _, _, _, _, _, _, e0, hi⟩
    · rw [det e e0]; exact hv
    · rw [det e e0]; exact hi
  · obtain ⟨_, e0⟩ := DeflateControl.deflatePending_inv hv hp hb
    rw [det e e0]; exact hv
  · obtain ⟨_, e0⟩ := DeflateControl.deflateUsed_inv hv hb
    rw [det e e0]; exact hv
  · obtain ⟨_, _, _, _, _, _, _, _, e0, _, hi⟩ := DeflatePrime.prime_inv hv bits value
    rw [det e e0]; exact hi hpr
  · obtain ⟨_, _, _, _, _, _, _, _, e0, hi⟩ := DeflateControl.deflateTune_inv hv g l n c
    rw [det e e0]; exact hi
  · rw [DeflateBound.RO.deflateBound s n h r h' e]; exact hv
  · rw [DeflateBound.RO.deflateBound_z s n h r h' e]; exact hv
  · obtain ⟨_, _, _, rfl, _, _, _, H, e0, ⟨_, hi, _⟩⟩ := DeflateReset.reset_inv hv
    rw [det e e0]; exact hi
  · obtain ⟨_, _, _, rfl, _, _, _, H, e0, ⟨_, hi, _⟩⟩ := DeflateReset.resetKeep_inv hv
    rw [det e e0]; exact hi
  · exact (P.copy h h' s dst r hv hdst hne e).1

/-- **The induction.** Every reachable deflate stream has the structural invariant, given the pending obligations. -/
theorem dreach_inv (P : DPending) {h : Heap} {s : StreamPtr} (hr : DeflateReachable h s) : DInv h s := by
  induction hr with
  | init h h' s level version size hi hv e => exact DeflateInitPublic.init_inv h h' s level version size hi hv e
  | init2 h h' s level method wb ml st version size hi hv e =>
    exact DeflateInitPublic.init2__inv h h' s level method wb ml st version size hi hv e
  | copy h h' src dst _ hdst hne e ih => exact (P.copy h h' src dst Z_OK ih hdst hne e).2 rfl
  | step h h' s _ hs ih => exact step_inv P ih hs
  | caller h h' s _ hc ih => exact caller_inv ih hc

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
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, ⟨_, _, f⟩⟩ := DeflateReset.reset_inv (dreach_inv P hr)
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateResetKeep_safety_of (P : DPending) : Goal.deflateResetKeep_safety := by
  intro h s hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateReset.resetKeep_noState hn, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, ⟨_, _, f⟩⟩ := DeflateReset.resetKeep_inv (dreach_inv P hr)
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateGetDictionary_safety_of (P : DPending) : Goal.deflateGetDictionary_safety := by
  intro h s d hasLen hh hd hnb
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateDict.getDict_noState hn d hasLen, dframe_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f⟩ := DeflateDict.getDict_inv hasLen (dreach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

theorem deflatePrime_safety_of (P : DPending) : Goal.deflatePrime_safety := by
  intro h s bits value hh
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflatePrime.prime_noState hn bits value, dframe_refl h _ _ _ _⟩
  · obtain ⟨i, z, b, rfl, hz, hzb, r, h', e, f, _⟩ := DeflatePrime.prime_inv (dreach_inv P hr) bits value
    exact ⟨r, h', e, by rw [stateIds_of hz hzb]; exact f⟩

theorem deflateSetDictionary_safety_of (P : DPending) : Goal.deflateSetDictionary_safety := by
  intro h s d n hh hd hnb
  rcases handle_cases hh with hn | hr
  · exact ⟨_, _, DeflateSetDict.setDict_noState hn d n, dframe_refl h _ _ _ _⟩
  · obtain ⟨r, h', e, _, f⟩ := DeflateSetDict.setDict_inv FillFacts.windowFacts (dreach_inv P hr) hd hnb
    exact ⟨r, h', e, f⟩

end ZlibNgF.Proof.DeflateReach
