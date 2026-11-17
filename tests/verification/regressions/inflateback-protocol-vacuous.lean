import ZlibF.Spec.Common.Back
import ZlibF.Proof.«inflate.c.base»

open C ZlibF.Spec ZlibF.Spec.Public Zlib.Infback

/-! The former `CallbackProtocol` required `inStep` and `outStep` on every heap that satisfies the
protocol's invariant. `local_` makes the invariant insensitive to every block outside `own`, and
`disjoint` puts the state block outside `own`. So an invariant that holds on a heap `h` also holds
on `bad h state`, the heap in which the state block holds two objects. `inStep` on that heap must
end in a heap that is `Uniq` (`ExternalFrame`) and that keeps the state block unchanged (`Frame`),
which is impossible. Hence no former protocol had a state that satisfied its invariant
(`OldCallbackProtocol.invariant_empty`), and the call clauses of `Goal.inflateBack_safety` and
`Goal.inflate_back_sequence_safety`, whose premise is `protocol.invariant h _`, were vacuous.

The correction asks `inStep` and `outStep` only on a heap that satisfies `CallbackEntry`, which is
what the library provides when it calls `in` or `out`. Every former protocol is a protocol of the
corrected kind (`OldCallbackProtocol.toNew`), so the corrected goals imply the former ones; the
corrected kind is inhabited with a non-empty invariant (`Goal.inflateBack_call_domain`). -/

/-- The definition of `CallbackProtocol` before the correction. -/
structure OldCallbackProtocol (r : ZStreamRef) (state : Nat) (window : BPtr) (capacity : Nat)
    (input : InCb) (inDesc : BPtr) (output : OutCb) (outDesc : BPtr) where
  own : Nat → Prop
  invariant : Heap → BackLog → Prop
  inputBound : Nat
  disjoint : (¬ own state) ∧ (∀ b, StreamRoot r b → ¬ own b)
  local_ : ∀ h after log, ExternalAgreement own h (restoreWindow h after window capacity) →
    (invariant h log ↔ invariant after log)
  bounded : ∀ h log, invariant h log → log.supplied.length ≤ inputBound
  liveInput : ∀ h log, invariant h log → log.held ≠ [] → Bytes h log.active log.held.length log.held
  inStep : ∀ h log next, invariant h log → ∃ n pointer after bytes,
    input inDesc next h = .ok ((n, pointer), after) ∧
    bytes.length = n.toNat ∧ ExternalFrame own h after ∧
    SameBytePrefix h after window window capacity ∧
    (n ≠ 0 → Bytes after pointer n.toNat bytes ∧ Separate pointer n.toNat window capacity ∧
      ∀ b, ByteRoot pointer b → b ≠ state ∧ ¬ StreamRoot r b) ∧
    invariant after { log with
      supplied := log.supplied ++ bytes, active := pointer, held := bytes, exhausted := n == 0 }
  outStep : ∀ h log pointer n bytes, invariant h log →
    Bytes h pointer n.toNat bytes → n.toNat ≤ capacity →
    ∃ rc after, output outDesc pointer n h = .ok (rc, after) ∧ ExternalFrame own h after ∧
      SameBytePrefix h after window window capacity ∧
      (log.held ≠ [] → Bytes after log.active log.held.length log.held) ∧
      invariant after { log with chunks := log.chunks ++ [bytes], failed := log.failed || rc != 0 }

theorem arr_split (a : Array UInt8) (i c : Nat) :
    a.extract 0 i ++ a.extract i (i + c) ++ a.extract (i + c) a.size = a := by
  apply Array.ext_getElem?
  intro k
  simp [Array.getElem?_extract]
  grind

@[simp] theorem ext_max (a : Array UInt8) (k : Nat) : a.extract 0 (max k a.size) = a := by
  apply Array.ext_getElem?
  intro i
  simp [Array.getElem?_extract]
  grind

/-- The heap `h` with block `st` holding two objects. -/
def bad (h : Heap) (st : Nat) : Heap :=
  { h with bytes := upd h.bytes st (some #[]), istates := upd h.istates st (some default) }

theorem agree (own : Nat → Prop) (h : Heap) (st : Nat) (hst : ¬ own st) (w : BPtr) (c : Nat) :
    ExternalAgreement own h (restoreWindow h (bad h st) w c) := by
  have key : ∀ b, own b → b ≠ st := fun b hb e => hst (e ▸ hb)
  unfold restoreWindow
  cases w with
  | null =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
    simp [bad, upd_ne _ _ _ _ (key b hb)]
  | ref r off =>
    cases r with
    | blk wb =>
      simp only [Space.get, Space.put]
      split
      · rename_i old cur ho hc
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        have hne := key b hb
        refine ⟨?_, by simp [bad], by simp [bad], by simp [bad], by simp [bad],
          by simp [bad, upd_ne _ _ _ _ hne], by simp [bad], by simp [bad]⟩
        by_cases hbw : b = wb
        · subst hbw
          have : cur = old := by
            have : (bad h st).bytes b = h.bytes b := by simp [bad, upd_ne _ _ _ _ hne]
            rw [this, ho] at hc; exact (Option.some.inj hc).symm
          subst this
          simp [upd_same, ho]
        · simp [bad, upd_ne _ _ _ _ hbw, upd_ne _ _ _ _ hne]
      · refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        simp [bad, upd_ne _ _ _ _ (key b hb)]
    | dstate_depth id =>
      simp only [Space.get, Space.put]
      split
      · rename_i old cur ho hc
        have hd : (bad h st).dstates = h.dstates := rfl
        rw [hd] at hc ⊢
        cases hs : h.dstates id with
        | none => simp [hs] at ho
        | some s =>
          simp only [hs, Option.map_some, Option.some.injEq] at ho hc
          subst ho; subst hc
          refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
          have hne := key b hb
          refine ⟨by simp [bad, upd_ne _ _ _ _ hne], by simp [bad], by simp [bad], by simp [bad], ?_,
            by simp [bad, upd_ne _ _ _ _ hne], by simp [bad], by simp [bad]⟩
          by_cases hbi : b = id
          · subst hbi; simp [upd_same, hs]
          · simp [upd_ne _ _ _ _ hbi]
      · refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        simp [bad, upd_ne _ _ _ _ (key b hb)]
    | str i =>
      simp only [Space.get, Space.put]
      try split
      all_goals
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        simp [bad, upd_ne _ _ _ _ (key b hb)]
    | st_dist_code =>
      simp only [Space.get, Space.put]
      try split
      all_goals
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        simp [bad, upd_ne _ _ _ _ (key b hb)]
    | st_length_code =>
      simp only [Space.get, Space.put]
      try split
      all_goals
        refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
        simp [bad, upd_ne _ _ _ _ (key b hb)]
/-- No former protocol has a state that satisfies its invariant. -/
theorem OldCallbackProtocol.invariant_empty {r : ZStreamRef} {state : Nat} {window : BPtr} {capacity : Nat}
    {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (p : OldCallbackProtocol r state window capacity input inDesc output outDesc)
    (h : Heap) (log : BackLog) : ¬ p.invariant h log := by
  intro hinv
  have h2 : p.invariant (bad h state) log :=
    (p.local_ h (bad h state) log (agree p.own h state p.disjoint.1 window capacity)).mp hinv
  obtain ⟨n, ptr, after, bytes, _, _, ⟨hframe, _, huniq, _⟩, _⟩ := p.inStep (bad h state) log .null h2
  have hlive : (bad h state).live state := Or.inl (by simp [bad, upd_same])
  have hf := hframe.2.2.2.2.2 state hlive p.disjoint.1
  have hu := huniq state
  have hb : after.bytes state = some #[] := by rw [hf.1]; simp [bad, upd_same]
  have hi : after.istates state = some default := by rw [hf.2.2.2.2.2.1]; simp [bad, upd_same]
  rw [hb, hi] at hu
  simp [Zlib.Inflate.Spec.cnt] at hu
  omega

/-- Every former protocol is a protocol of the corrected kind, with the same invariant. -/
def OldCallbackProtocol.toNew {r : ZStreamRef} {state : Nat} {window : BPtr} {capacity : Nat}
    {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (p : OldCallbackProtocol r state window capacity input inDesc output outDesc) :
    CallbackProtocol r state window capacity input inDesc output outDesc where
  own := p.own
  invariant := p.invariant
  inputBound := p.inputBound
  disjoint := p.disjoint
  local_ := p.local_
  bounded := p.bounded
  liveInput := p.liveInput
  inStep := fun h log next _ inv => p.inStep h log next inv
  outStep := fun h log pointer n bytes _ inv => p.outStep h log pointer n bytes inv

#print axioms OldCallbackProtocol.invariant_empty
#print axioms OldCallbackProtocol.toNew
