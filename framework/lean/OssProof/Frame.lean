import OssProof.Wp

/-!
# Generic Relational Preservation & Write-Footprint Engine (`OssProof.Frame`)

Replaces duplicated per-module frame towers (`FooFrameM`/`FooFrameX` re-walking the same C module
10+ times for different projections) with a single generic relational judgement `Preserves R m`:
whenever `m h = .ok (a, h')`, the heap transition satisfies `R h h'`.

Prove **one** write-footprint theorem `Preserves (Modifies W) fn` per C function, and derive every
frame corollary by `Preserves.mono` in one line.
-/

namespace OssProof

/-- `Preserves R m`: every successful execution of `m` relates its initial and final heaps by `R`. -/
def Preserves {H α : Type} (R : H → H → Prop) (m : M H α) : Prop :=
  ∀ h a h', m h = .ok (a, h') → R h h'

namespace Preserves

variable {H α β : Type}

theorem mono {R R' : H → H → Prop} {m : M H α}
    (hp : Preserves R m) (himp : ∀ h h', R h h' → R' h h') : Preserves R' m :=
  fun h a h' he => himp h h' (hp h a h' he)

theorem and {R1 R2 : H → H → Prop} {m : M H α}
    (h1 : Preserves R1 m) (h2 : Preserves R2 m) : Preserves (fun h h' => R1 h h' ∧ R2 h h') m :=
  fun h a h' he => ⟨h1 h a h' he, h2 h a h' he⟩

theorem pure {R : H → H → Prop} (hrefl : ∀ h, R h h) (a : α) :
    Preserves R (Pure.pure a : M H α) := by
  intro h a' h' he
  cases he
  exact hrefl h

theorem readOnly {R : H → H → Prop} {m : M H α}
    (hrefl : ∀ h, R h h) (hro : ∀ h a h', m h = .ok (a, h') → h' = h) : Preserves R m := by
  intro h a h' he
  rw [hro h a h' he]
  exact hrefl h

theorem bind {R : H → H → Prop} (htrans : ∀ h1 h2 h3, R h1 h2 → R h2 h3 → R h1 h3)
    {m : M H α} {f : α → M H β}
    (hm : Preserves R m) (hf : ∀ a, Preserves R (f a)) : Preserves R (m >>= f) := by
  intro h b h'' he
  simp only [M.bind_apply] at he
  cases hmh : m h with
  | error e => simp [hmh] at he
  | ok p =>
    rcases p with ⟨a, h'⟩
    simp only [hmh] at he
    exact htrans h h' h'' (hm h a h' hmh) (hf a h' b h'' he)

theorem ite {R : H → H → Prop} {c : Prop} [Decidable c] {t e : M H α}
    (ht : c → Preserves R t) (he : ¬ c → Preserves R e) : Preserves R (if c then t else e) := by
  split
  · exact ht ‹_›
  · exact he ‹_›

theorem fail {R : H → H → Prop} (e : Fault) : Preserves R (M.fail e : M H α) := by
  intro h a h' he
  cases he

theorem guardUB {R : H → H → Prop} (hrefl : ∀ h, R h h) (c : Bool) (msg : String) :
    Preserves R (M.guardUB c msg) := by
  unfold M.guardUB
  split
  · exact pure hrefl ()
  · exact fail (.ub msg)

theorem cwhile {R : H → H → Prop} {σ : Type}
    (hrefl : ∀ h, R h h) (htrans : ∀ h1 h2 h3, R h1 h2 → R h2 h3 → R h1 h3)
    (cond : σ → M H Bool) (body : σ → M H σ)
    (hcond : ∀ s, Preserves R (cond s)) (hbody : ∀ s, Preserves R (body s)) :
    ∀ fuel s, Preserves R (OssProof.cwhile fuel s cond body) := by
  intro fuel
  induction fuel with
  | zero => intro s; exact fail .fuel
  | succ n ih =>
    intro s
    unfold OssProof.cwhile
    refine bind htrans (hcond s) fun c => ?_
    cases c with
    | false => exact pure hrefl s
    | true => exact bind htrans (hbody s) fun next => ih next

theorem cloop {R : H → H → Prop} {σ ρ : Type}
    (hrefl : ∀ h, R h h) (htrans : ∀ h1 h2 h3, R h1 h2 → R h2 h3 → R h1 h3)
    (step : σ → M H (LoopStep σ ρ)) (hstep : ∀ s, Preserves R (step s)) :
    ∀ fuel s, Preserves R (OssProof.cloop fuel s step) := by
  intro fuel
  induction fuel with
  | zero => intro s; exact fail .fuel
  | succ n ih =>
    intro s
    unfold OssProof.cloop
    refine bind htrans (hstep s) fun r => ?_
    cases r with
    | cont s' => exact ih s'
    | brk s' => exact pure hrefl (Sum.inl s')
    | ret rv => exact pure hrefl (Sum.inr rv)

theorem cfor {R : H → H → Prop} {σ ρ : Type}
    (hrefl : ∀ h, R h h) (htrans : ∀ h1 h2 h3, R h1 h2 → R h2 h3 → R h1 h3)
    (cond : σ → M H Bool) (body : σ → M H (LoopStep σ ρ))
    (hcond : ∀ s, Preserves R (cond s)) (hbody : ∀ s, Preserves R (body s)) :
    ∀ fuel s, Preserves R (OssProof.cfor fuel s cond body) := by
  intro fuel s
  unfold OssProof.cfor
  refine cloop hrefl htrans _ ?_ fuel s
  intro st
  refine bind htrans (hcond st) fun c => ?_
  cases c with
  | true => exact hbody st
  | false => exact pure hrefl (LoopStep.brk st)

theorem cdoWhile {R : H → H → Prop} {σ : Type}
    (hrefl : ∀ h, R h h) (htrans : ∀ h1 h2 h3, R h1 h2 → R h2 h3 → R h1 h3)
    (body : σ → M H σ) (cond : σ → M H Bool)
    (hbody : ∀ s, Preserves R (body s)) (hcond : ∀ s, Preserves R (cond s)) :
    ∀ fuel s, Preserves R (OssProof.cdoWhile fuel s body cond) := by
  intro fuel
  induction fuel with
  | zero => intro s; exact fail .fuel
  | succ n ih =>
    intro s
    unfold OssProof.cdoWhile
    refine bind htrans (hbody s) fun next => ?_
    refine bind htrans (hcond next) fun c => ?_
    cases c with
    | true => exact ih next
    | false => exact pure hrefl next

/-- Combine a `Wp` proof with a `Preserves` footprint theorem in one step. -/
theorem with_wp {R : H → H → Prop} {m : M H α} {h : H} {Q : α → H → Prop}
    (hw : Wp m h Q) (hp : Preserves R m) : Wp m h (fun a h' => Q a h' ∧ R h h') := by
  rcases hw with ⟨a, h', he, hq⟩
  exact ⟨a, h', he, hq, hp h a h' he⟩

/-! ### Generic read-only pointer primitive preservation -/

section ptr
variable {Ref T : Type} [Space H Ref T]

theorem ptr_add_ro (p : Ptr Ref) (k : Int) :
    ∀ h a h', Ptr.add (H := H) (R := Ref) (T := T) p k h = .ok (a, h') → h' = h := by
  intro h a h' he
  cases p with
  | null => simp [Ptr.add] at he
  | ref r off =>
    simp only [Ptr.add] at he
    cases hg : Space.get h r with
    | none => simp [hg] at he
    | some arr =>
      simp only [hg] at he
      split at he <;> simp_all

theorem ptr_load_ro (p : Ptr Ref) :
    ∀ h a h', Ptr.load (H := H) (R := Ref) (T := T) p h = .ok (a, h') → h' = h := by
  intro h a h' he
  cases p with
  | null => simp [Ptr.load] at he
  | ref r off =>
    simp only [Ptr.load] at he
    cases hg : Space.get h r with
    | none => simp [hg] at he
    | some arr =>
      simp only [hg] at he
      split at he <;> simp_all

theorem ptr_diff_ro [DecidableEq Ref] (p q : Ptr Ref) :
    ∀ h a h', Ptr.diff (H := H) (R := Ref) (T := T) p q h = .ok (a, h') → h' = h := by
  intro h a h' he
  cases p with
  | null => simp [Ptr.diff] at he
  | ref r1 o1 =>
    cases q with
    | null => simp [Ptr.diff] at he
    | ref r2 o2 =>
      simp only [Ptr.diff] at he
      split at he
      · cases hg : Space.get h r1 with
        | none => simp [hg] at he
        | some arr =>
          simp only [hg] at he
          split at he
          · split at he <;> simp_all
          · simp at he
      · simp at he

theorem ptr_lt_ro [DecidableEq Ref] (p q : Ptr Ref) :
    ∀ h a h', Ptr.lt (H := H) (R := Ref) (T := T) p q h = .ok (a, h') → h' = h := by
  intro h a h' he
  cases p with
  | null => simp [Ptr.lt] at he
  | ref r1 o1 =>
    cases q with
    | null => simp [Ptr.lt] at he
    | ref r2 o2 =>
      simp only [Ptr.lt] at he
      split at he
      · cases hg : Space.get h r1 with
        | none => simp [hg] at he
        | some arr =>
          simp only [hg] at he
          split at he <;> simp_all
      · simp at he

theorem ptr_store_modifies {R : H → H → Prop} (p : Ptr Ref) (v : T)
    (hmod : ∀ h r off a, p = .ref r off → Space.get h r = some a → Space.ro h r = false →
      off < a.size → R h (Space.modify h r (fun arr => arr.set! off v))) :
    Preserves R (Ptr.store (H := H) (R := Ref) (T := T) p v) := by
  intro h u h' he
  cases p with
  | null => simp [Ptr.store] at he
  | ref r off =>
    simp only [Ptr.store] at he
    cases hg : Space.get h r with
    | none => simp [hg] at he
    | some arr =>
      simp only [hg] at he
      cases hro : Space.ro h r with
      | true => simp [hro] at he
      | false =>
        simp only [hro, Bool.false_eq_true, ↓reduceIte] at he
        split at he
        · cases he
          exact hmod h r off arr rfl hg hro ‹_›
        · simp at he

end ptr
end Preserves
end OssProof
