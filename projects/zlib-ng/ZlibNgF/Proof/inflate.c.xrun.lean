import ZlibNgF.Proof.«inflate.c.sync»

/-!
# Runs of the monad `X` of `inflate()` (`ZlibNgF`)

`X = ExceptT Ex (StateT IL M)`: a mode of `inflate` runs on the locals `IL` and the heap, and ends normally (`break`),
by `goto inf_leave` (`.error .leave`) or by `return v` (`.error (.ret v)`). `SatX H l m Q`: `m` runs from locals `l`
and heap `H` without fault, and its outcome, locals and heap satisfy `Q`. The rules below decompose a mode
statement by statement; `xwhileBrk_rank` is the rule for the loops of `X` with a decreasing measure.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateX
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)

/-- The run of `m` from locals `l`. -/
def runX {α : Type} (m : X α) (l : IL) : M (Except Ex α × IL) := StateT.run (ExceptT.run m) l

/-- `m` runs from `l` on `H` without fault to an outcome, locals and heap that satisfy `Q`. -/
def SatX {α : Type} (H : Heap) (l : IL) (m : X α) (Q : Except Ex α → IL → Heap → Prop) : Prop :=
  Sat H (runX m l) (fun p H' => Q p.1 p.2 H')

theorem runX_bind {α β : Type} (m : X α) (f : α → X β) (l : IL) :
    runX (m >>= f) l = (runX m l >>= fun p => match p.1 with
      | .ok a => runX (f a) p.2
      | .error e => pure (.error e, p.2)) := by
  simp only [runX, StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  funext h
  split
  · rename_i a h' _
    rcases a with ⟨r, l'⟩
    cases r <;> rfl
  · rfl

theorem SatX.bind {α β : Type} {H : Heap} {l : IL} {m : X α} {f : α → X β} {Q : Except Ex β → IL → Heap → Prop}
    (hm : SatX H l m (fun r l' H' => match r with
      | .ok a => SatX H' l' (f a) Q
      | .error e => Q (.error e) l' H')) : SatX H l (m >>= f) Q := by
  unfold SatX at hm ⊢
  rw [runX_bind]
  refine Sat.bind (Sat.mono hm ?_)
  rintro ⟨r, l'⟩ H' q
  cases r with
  | ok a => exact q
  | error e => exact Sat.pure q

theorem SatX.pure {α : Type} {H : Heap} {l : IL} {a : α} {Q : Except Ex α → IL → Heap → Prop} (q : Q (.ok a) l H) :
    SatX H l (Pure.pure a) Q := ⟨_, H, rfl, q⟩

theorem SatX.throw {α : Type} {H : Heap} {l : IL} {e : Ex} {Q : Except Ex α → IL → Heap → Prop}
    (q : Q (.error e) l H) : SatX H l (MonadExcept.throw e : X α) Q := ⟨_, H, rfl, q⟩

theorem SatX.get {H : Heap} {l : IL} {Q : Except Ex IL → IL → Heap → Prop} (q : Q (.ok l) l H) :
    SatX H l (MonadState.get : X IL) Q := ⟨_, H, rfl, q⟩

theorem SatX.set {H : Heap} {l l' : IL} {Q : Except Ex PUnit → IL → Heap → Prop} (q : Q (.ok ⟨⟩) l' H) :
    SatX H l (MonadStateOf.set l' : X PUnit) Q := ⟨_, H, rfl, q⟩

theorem SatX.modify {H : Heap} {l : IL} {f : IL → IL} {Q : Except Ex PUnit → IL → Heap → Prop}
    (q : Q (.ok ⟨⟩) (f l) H) : SatX H l (modify f : X PUnit) Q := ⟨_, H, rfl, q⟩

theorem SatX.lift {α : Type} {H : Heap} {l : IL} {m : M α} {Q : Except Ex α → IL → Heap → Prop}
    (hm : Sat H m (fun a H' => Q (.ok a) l H')) : SatX H l (MonadLiftT.monadLift m : X α) Q := by
  obtain ⟨a, H', e, q⟩ := hm
  refine ⟨(.ok a, l), H', ?_, q⟩
  show (Except.ok <$> StateT.lift m : StateT IL M (Except Ex α)) l H = _
  simp [Functor.map, StateT.map, StateT.lift, bind_app, e]

theorem SatX.mono {α : Type} {H : Heap} {l : IL} {m : X α} {P Q : Except Ex α → IL → Heap → Prop}
    (hm : SatX H l m P) (hpq : ∀ r l' H', P r l' H' → Q r l' H') : SatX H l m Q :=
  Sat.mono hm (fun p H' q => hpq p.1 p.2 H' q)

theorem SatX.ite {α : Type} {H : Heap} {l : IL} {c : Prop} [Decidable c] {m₁ m₂ : X α}
    {Q : Except Ex α → IL → Heap → Prop} (h₁ : c → SatX H l m₁ Q) (h₂ : ¬ c → SatX H l m₂ Q) :
    SatX H l (if c then m₁ else m₂) Q := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

/-! ## Loops -/

/-- The outcome of a loop from its final status. -/
def Stop.toE : Stop → Except Ex Unit
  | .ex e => .error e
  | _ => .ok ()

/-- `while (cond) body` of `X` (`body` returns `true` for `break`) with an invariant `P` and a measure `rank` that the
body decreases; the two extra fuel units cover the last test and a `break` or exception from the body. -/
theorem xwhileBrk_rank {cond : X Bool} {body : X Bool} (P : IL → Heap → Prop) (rank : IL → Heap → Nat)
    (Q : Except Ex Unit → IL → Heap → Prop)
    (step : ∀ l h, P l h → SatX h l cond (fun test l1 h1 =>
      match test with
      | .error e => Q (.error e) l1 h1
      | .ok false => Q (.ok ()) l1 h1
      | .ok true => SatX h1 l1 body (fun res l2 h2 =>
          match res with
          | .error e => Q (.error e) l2 h2
          | .ok true => Q (.ok ()) l2 h2
          | .ok false => P l2 h2 ∧ rank l2 h2 < rank l h)))
    {l : IL} {h : Heap} (initial : P l h) (budget : rank l h + 2 < fuel) :
    SatX h l (xwhileBrk cond body) Q := by
  let loopCond := fun (locals : IL × Stop) => match locals.2 with
    | .go => do
      let (result, regs) ← StateT.run (ExceptT.run cond) locals.1
      Pure.pure (match result with
        | .ok value => (value, (regs, Stop.go))
        | .error fault => (false, (regs, Stop.ex fault)))
    | status => Pure.pure (false, (locals.1, status))
  let loopBody := fun (locals : IL × Stop) => do
    let (result, regs) ← StateT.run (ExceptT.run body) locals.1
    Pure.pure (match result with
      | .ok value => (regs, if value then Stop.brk else Stop.go)
      | .error fault => (regs, Stop.ex fault))
  have key : ∀ k n current heap, P current heap → rank current heap ≤ k → k + 2 < n →
      ∃ status regs after,
        cwhile.go loopCond loopBody n (current, Stop.go) heap = .ok ((regs, status), after) ∧
        Q (Stop.toE status) regs after := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n current heap inv bound gas
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨⟨test, regs1⟩, heap1, condRun, post⟩ := step current heap inv
      have condC : (StateT.run (ExceptT.run cond) current) heap = .ok ((test, regs1), heap1) := condRun
      cases test with
      | error fault =>
        exact ⟨.ex fault, regs1, heap1, by simp [cwhile.go, loopCond, condC, bind_app], post⟩
      | ok decision =>
        cases decision with
        | false =>
          exact ⟨.go, regs1, heap1, by simp [cwhile.go, loopCond, condC, bind_app], post⟩
        | true =>
          obtain ⟨⟨result, regs2⟩, heap2, bodyRun, bodyPost⟩ := post
          have bodyC : (StateT.run (ExceptT.run body) regs1) heap1 = .ok ((result, regs2), heap2) := bodyRun
          cases result with
          | error fault =>
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            exact ⟨.ex fault, regs2, heap2,
              by simp [cwhile.go, loopCond, loopBody, condC, bodyC, bind_app], bodyPost⟩
          | ok decision =>
            cases decision with
            | false =>
              obtain ⟨nextInv, decreases⟩ := bodyPost
              dsimp only at nextInv decreases
              obtain ⟨status, regs, after, run, post⟩ :=
                ih (rank regs2 heap2) (by omega) n regs2 heap2 nextInv (Nat.le_refl _) (by omega)
              exact ⟨status, regs, after,
                by simpa [cwhile.go, loopCond, loopBody, condC, bodyC, bind_app] using run, post⟩
            | true =>
              obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
              exact ⟨.brk, regs2, heap2,
                by simp [cwhile.go, loopCond, loopBody, condC, bodyC, bind_app], bodyPost⟩
  obtain ⟨status, regs, after, run, post⟩ := key (rank l h) fuel l h initial (Nat.le_refl _) budget
  refine ⟨(Stop.toE status, regs), after, ?_, post⟩
  unfold xwhileBrk runX
  simp only [ExceptT.run, StateT.run, ExceptT.mk, cwhile, bind_app]
  dsimp only [loopCond, loopBody] at run
  erw [run]
  cases status <;> rfl

end ZlibNgF.Proof.InflateX
