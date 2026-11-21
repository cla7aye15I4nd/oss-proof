import Lean
import ZlibNgF.ZlibNg.«deflate.c»

/-!
# What `deflate` and `deflateParams` keep (`ZlibNgF`)

`Keep m`: every run of `m` that returns keeps `DR`: the saved pointers (`Heap.savedPtrs`), `nextBlk`, which blocks are
alive, the inflate objects and the `deflate_allocs` records stay; every `deflate_state` keeps its `gzhead` field (and
no state appears or disappears); every caller `z_stream` keeps its `state` field (and none appears or disappears).

This holds of every function that `deflate` and `deflateParams` reach: they never call `malloc` / `free` (no
`allocB`, `freeB`, `storePtrSlot`, `localBlock`, `dropLocal`, carve or `zalloc` / `zfree` call is reachable), they
store into byte blocks and the arrays of a state in place, and every update of a `deflate_state` (`wrD`) or of the
caller's `z_stream` (`wrZ`) is a record update that leaves `gzhead` / `state` alone. The rules decompose a computation
(bind, `have`, join points, `if`, `match`, `for`, the loops `cwhile` and `cdoWhile`) down to the runtime primitives,
whose lemmas are proved from their definitions; `keep_tac` applies them, and every such function of the translation
gets its lemma `K.<name>`. The lemmas of `wrD` and `wrZ` have a side condition on the update function (it keeps
`gzhead`, resp. `state`), which `keep_tac` closes by `rfl` for each record update of the translation.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateKeep
open C ZlibNg.Inflate ZlibNg.Deflate

/-! ## The relation -/

/-- What every function reachable from `deflate` keeps from `h` to `h'`. -/
structure DR (h h' : Heap) : Prop where
  sp : h'.savedPtrs = h.savedPtrs
  nb : h'.nextBlk = h.nextBlk
  bl : ∀ b, (h'.bytes b).isSome = (h.bytes b).isSome
  ist : h'.istates = h.istates
  ial : h'.iallocs = h.iallocs
  dal : h'.dallocs = h.dallocs
  ds : ∀ b, (h'.dstates b).map DeflateState.gzhead = (h.dstates b).map DeflateState.gzhead
  zs : ∀ i, (h'.streams i).map ZStream.state = (h.streams i).map ZStream.state

theorem DR.refl (h : Heap) : DR h h :=
  ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem DR.trans {h1 h2 h3 : Heap} (a : DR h1 h2) (b : DR h2 h3) : DR h1 h3 :=
  ⟨b.sp.trans a.sp, b.nb.trans a.nb, fun x => (b.bl x).trans (a.bl x), b.ist.trans a.ist, b.ial.trans a.ial,
    b.dal.trans a.dal, fun x => (b.ds x).trans (a.ds x), fun x => (b.zs x).trans (a.zs x)⟩

/-- A computation of `M` whose every successful run keeps `DR`. -/
structure Keep {α : Type} (m : M α) : Prop where
  run : ∀ h r h', m h = .ok (r, h') → DR h h'

/-- `Keep` for functions into `M` (join points). -/
class KeepF (β : Type) where
  P : β → Prop

instance {α : Type} : KeepF (M α) := ⟨Keep⟩
instance {γ β : Type} [KeepF β] : KeepF (γ → β) := ⟨fun f => ∀ y, KeepF.P (f y)⟩

/-! ## Heap updates -/

/-- The bytes of a live block change. -/
theorem dr_bytes {h : Heap} {b : Nat} {a a' : Array UInt8} (hb : h.bytes b = some a) :
    DR h { h with bytes := upd h.bytes b (some a') } := by
  refine ⟨rfl, rfl, fun c => ?_, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  by_cases hc : c = b
  · subst hc; simp [hb]
  · simp [upd_ne _ _ _ _ hc]

/-- The `deflate_state` of block `b` changes, keeping its `gzhead`. -/
theorem dr_dstate {h : Heap} {b : Nat} {s s' : DeflateState} (hs : h.dstates b = some s) (hg : s'.gzhead = s.gzhead) :
    DR h { h with dstates := upd h.dstates b (some s') } := by
  refine ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl, fun c => ?_, fun _ => rfl⟩
  by_cases hc : c = b
  · subst hc; simp [hs, hg]
  · simp [upd_ne _ _ _ _ hc]

/-- The caller's `z_stream` `i` changes, keeping its `state`. -/
theorem dr_stream {h : Heap} {i : Nat} {z z' : ZStream} (hz : h.streams i = some z) (hg : z'.state = z.state) :
    DR h { h with streams := upd h.streams i (some z') } := by
  refine ⟨rfl, rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl, fun c => ?_⟩
  by_cases hc : c = i
  · subst hc; simp [hz, hg]
  · simp [upd_ne _ _ _ _ hc]

/-! ## Rules -/

theorem keep_pure {α : Type} (a : α) : Keep (pure a : M α) := ⟨fun h r h' e => by cases e; exact DR.refl h⟩

theorem keep_bind {α β : Type} {m : M α} {f : α → M β} (hm : Keep m) (hf : ∀ a, Keep (f a)) :
    Keep (m >>= f) := by
  refine ⟨fun h r h' e => ?_⟩
  simp only [bind_app] at e
  split at e
  · rename_i a h1 e1
    exact (hm.run _ _ _ e1).trans ((hf a).run _ _ _ e)
  · cases e

theorem keep_have {β α : Type} [KeepF β] (v : β) (b : β → M α) (hv : KeepF.P v)
    (hb : ∀ x, KeepF.P x → Keep (b x)) : Keep (have x := v; b x) := hb v hv

theorem keep_ub {α : Type} (s : String) : Keep (ub s : M α) := ⟨fun _ _ _ e => by cases e⟩

theorem keep_ite {α : Type} {c : Prop} [inst : Decidable c] {a b : M α} (ha : c → Keep a) (hb : ¬c → Keep b) :
    Keep (if c then a else b) := by
  cases inst with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

theorem keep_dite {α : Type} {c : Prop} [inst : Decidable c] {a : c → M α} {b : ¬c → M α} (ha : ∀ h, Keep (a h))
    (hb : ∀ h, Keep (b h)) : Keep (if h : c then a h else b h) := by
  cases inst with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-! ## Loops -/

theorem K.C.cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (hc : ∀ s, Keep (cond s))
    (hb : ∀ s, Keep (body s)) (s : σ) : Keep (cwhile cond body s) := by
  suffices H : ∀ n s, Keep (cwhile.go cond body n s) from H _ s
  intro n
  induction n with
  | zero => intro s; exact ⟨fun _ _ _ e => by cases e⟩
  | succ n ih =>
    intro s
    refine ⟨fun h r h' e => ?_⟩
    simp only [cwhile.go, bind_app] at e
    split at e
    · rename_i p h1 e1
      obtain ⟨c, s1⟩ := p
      refine ((hc s).run _ _ _ e1).trans ?_
      cases c with
      | true =>
        simp only [ite_true, bind_app] at e
        split at e
        · rename_i s2 h2 e2
          exact ((hb s1).run _ _ _ e2).trans ((ih s2).run _ _ _ e)
        · cases e
      | false => cases e; exact DR.refl _
    · cases e

theorem K.C.cdoWhile {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (hb : ∀ s, Keep (body s))
    (hc : ∀ s, Keep (cond s)) (s : σ) : Keep (cdoWhile body cond s) := by
  suffices H : ∀ n s, Keep (cdoWhile.go body cond n s) from H _ s
  intro n
  induction n with
  | zero => intro s; exact ⟨fun _ _ _ e => by cases e⟩
  | succ n ih =>
    intro s
    refine ⟨fun h r h' e => ?_⟩
    simp only [cdoWhile.go, bind_app] at e
    split at e
    · rename_i s1 h1 e1
      refine ((hb s).run _ _ _ e1).trans ?_
      split at e
      · rename_i p h2 e2
        obtain ⟨c, s2⟩ := p
        refine ((hc s1).run _ _ _ e2).trans ?_
        cases c with
        | true => exact (ih s2).run _ _ _ e
        | false => cases e; exact DR.refl _
      · cases e
    · cases e

theorem keep_forIn_list {α β : Type} (l : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, Keep (f a b)) : Keep (forIn l b f) := by
  induction l generalizing b with
  | nil => exact keep_pure b
  | cons x l ih =>
    rw [List.forIn_cons]
    refine keep_bind (hf x b) fun r => ?_
    cases r with
    | done c => exact keep_pure c
    | yield c => exact ih c

theorem keep_forIn_array {α β : Type} (xs : Array α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, Keep (f a b)) : Keep (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact keep_forIn_list _ b f hf

theorem keep_forIn_range {β : Type} (r : Std.Legacy.Range) (b : β) (f : Nat → β → M (ForInStep β))
    (hf : ∀ a b, Keep (f a b)) : Keep (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact keep_forIn_list _ b f hf

/-! ## Primitives that only read -/

set_option hygiene false in
/-- The run of a primitive that only reads leaves the heap. -/
macro "rd_tac" : tactic => `(tactic| (repeat' split at e) <;> first | (cases e; exact DR.refl _) | cases e)

theorem K.C.ldStream (p : StreamPtr) : Keep (ldStream p) := ⟨fun h r h' e => by unfold _root_.C.ldStream at e; rd_tac⟩
theorem K.C.ldHeader (p : HeaderPtr) : Keep (ldHeader p) := ⟨fun h r h' e => by unfold _root_.C.ldHeader at e; rd_tac⟩
theorem K.C.ldDState (p : StatePtr) : Keep (ldDState p) := ⟨fun h r h' e => by unfold _root_.C.ldDState at e; rd_tac⟩
theorem K.C.ldDAllocs (p : DAllocsPtr) : Keep (ldDAllocs p) :=
  ⟨fun h r h' e => by unfold _root_.C.ldDAllocs at e; rd_tac⟩
theorem K.C.addrOf (p : BPtr) : Keep (addrOf p) := ⟨fun h r h' e => by unfold _root_.C.addrOf at e; rd_tac⟩
theorem K.C.strLitRef (s : String) : Keep (strLitRef s) := ⟨fun h r h' e => by unfold _root_.C.strLitRef at e; rd_tac⟩
theorem K.C.uninitLocals (k : Nat) : Keep (uninitLocals k) :=
  ⟨fun h r h' e => by unfold _root_.C.uninitLocals at e; rd_tac⟩

section generic
variable {R T : Type} [Space Heap R T]
theorem K.C.Ptr.add (p : Ptr R) (k : Int) : Keep (Ptr.add p k) := ⟨fun h r h' e => by unfold _root_.C.Ptr.add at e; rd_tac⟩
theorem K.C.Ptr.load (p : Ptr R) : Keep (Ptr.load p : M T) := ⟨fun h r h' e => by unfold _root_.C.Ptr.load at e; rd_tac⟩
theorem K.C.Ptr.diff [DecidableEq R] (p q : Ptr R) : Keep (Ptr.diff p q) :=
  ⟨fun h r h' e => by unfold _root_.C.Ptr.diff at e; rd_tac⟩
theorem K.C.Ptr.lt [DecidableEq R] (p q : Ptr R) : Keep (Ptr.lt p q) := ⟨fun h r h' e => by unfold _root_.C.Ptr.lt at e; rd_tac⟩
end generic

/-! ## Record updates of the state and the stream -/

/-- `wrD st f` with an `f` that keeps `gzhead`. -/
theorem K.ZlibNg.Deflate.wrD (st : StatePtr) (f : DeflateState → DeflateState) (hf : ∀ s, (f s).gzhead = s.gzhead) :
    Keep (_root_.ZlibNg.Deflate.wrD st f) := ⟨fun h r h' e => by
  simp only [_root_.ZlibNg.Deflate.wrD, bind_app] at e
  cases st with
  | none => simp [_root_.C.ldDState] at e
  | some b =>
    cases hs : h.dstate b with
    | none => simp [_root_.C.ldDState, hs] at e
    | some s =>
      simp only [_root_.C.ldDState, _root_.C.stDState, hs] at e
      cases e
      exact dr_dstate (Heap.dstate_some hs) (hf s)⟩

/-- `wrZ strm f` with an `f` that keeps `state`. -/
theorem K.ZlibNg.Inflate.wrZ (strm : StreamPtr) (f : ZStream → ZStream) (hf : ∀ z, (f z).state = z.state) :
    Keep (_root_.ZlibNg.Inflate.wrZ strm f) := ⟨fun h r h' e => by
  simp only [_root_.ZlibNg.Inflate.wrZ, bind_app] at e
  cases strm with
  | none => simp [_root_.C.ldStream] at e
  | some i =>
    cases hz : h.streams i with
    | none => simp [_root_.C.ldStream, hz] at e
    | some z =>
      simp only [_root_.C.ldStream, _root_.C.stStream, hz] at e
      cases e
      exact dr_stream hz (hf z)⟩

/-- `*desc = t` keeps `gzhead`. -/
theorem descSel_set_gzhead (d : ZlibNg.Trees.DescSel) (s : DeflateState) (t : TreeDesc) :
    (d.set s t).gzhead = s.gzhead := by
  cases d <;> rfl

/-! ## Stores through a `Space` -/

/-- Replacing an array of a `Space` keeps `DR`. -/
class SpaceKeep (R T : Type) [Space Heap R T] : Prop where
  put : ∀ (h : Heap) (r : R) (a a' : Array T), Space.get h r = some a → Space.ro h r = false → DR h (Space.put h r a')

instance : SpaceKeep BRef UInt8 where
  put h r a a' hg hro := by
    cases r with
    | heap b => exact dr_bytes (a := a) hg
    | const _ => simp [Space.ro, Heap.isRo] at hro
    | str _ => simp [Space.ro, Heap.isRo] at hro

instance : SpaceKeep CtRef Ct where
  put h r a a' hg hro := by
    cases r with
    | dyn_ltree b =>
      show DR h (Heap.putCts h _ a')
      simp only [Heap.putCts]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _
    | dyn_dtree b =>
      show DR h (Heap.putCts h _ a')
      simp only [Heap.putCts]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _
    | bl_tree b =>
      show DR h (Heap.putCts h _ a')
      simp only [Heap.putCts]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _
    | static_ltree => simp [Space.ro, Heap.roCts] at hro
    | static_dtree => simp [Space.ro, Heap.roCts] at hro

instance : SpaceKeep DWRef UInt32 where
  put h r a a' hg hro := by
    cases r with
    | pq_leaves b =>
      show DR h (Heap.putDW h _ a')
      simp only [Heap.putDW]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _
    | pq_scratch b =>
      show DR h (Heap.putDW h _ a')
      simp only [Heap.putDW]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _

instance : SpaceKeep DHRef UInt16 where
  put h r a a' hg hro := by
    cases r with
    | bl_count b =>
      show DR h (Heap.putDH h _ a')
      simp only [Heap.putDH]
      split
      · rename_i s hs; exact dr_dstate hs rfl
      · exact DR.refl _

instance : SpaceKeep URef UInt32 where
  put h r a a' hg hro := by simp [Space.ro, Heap.isRoU32] at hro

instance : SpaceKeep IRef Int32 where
  put h r a a' hg hro := by simp [Space.ro] at hro

section generic
variable {R T : Type} [Space Heap R T] [SpaceKeep R T]

theorem dr_modify {h : Heap} {r : R} {a : Array T} (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    (f : Array T → Array T) : DR h (Space.modify h r f) := by
  rw [Space.modify_eq h r a f hg hro]
  exact SpaceKeep.put h r a (f a) hg hro

theorem K.C.Ptr.store (p : Ptr R) (v : T) : Keep (Ptr.store p v) := ⟨fun h r h' e => by
  unfold _root_.C.Ptr.store at e
  split at e
  · cases e
  · split at e
    · cases e
    · rename_i a hg
      split at e
      · cases e
      · rename_i hro
        split at e
        · cases e
          exact dr_modify hg (by simpa using hro) _
        · cases e⟩

end generic

theorem K.C.Ptr.memset {R : Type} [Space Heap R UInt8] [SpaceKeep R UInt8] (dst : Ptr R) (byte : UInt8) (n : Nat) :
    Keep (Ptr.memset dst byte n) := ⟨fun h r h' e => by
  unfold _root_.C.Ptr.memset at e
  split at e
  · cases e
  · split at e
    · cases e
    · rename_i a hg
      split at e
      · cases e
      · rename_i hro
        split at e
        · cases e
          exact dr_modify hg (by simpa using hro) _
        · cases e⟩

theorem K.C.Ptr.memcpy {R : Type} [DecidableEq R] [Space Heap R UInt8] [SpaceKeep R UInt8] (dst src : Ptr R)
    (n : Nat) : Keep (Ptr.memcpy dst src n) := ⟨fun h r h' e => by
  unfold _root_.C.Ptr.memcpy at e
  split at e
  · cases e
  · cases e
  · split at e
    · rename_i a as_ hg hs
      split at e
      · cases e
      · rename_i hro
        split at e
        · split at e
          · cases e
          · cases e
            exact dr_modify hg (by simpa using hro) _
        · cases e
    · cases e⟩

theorem K.C.Ptr.memmove {R : Type} [DecidableEq R] [Space Heap R UInt8] [SpaceKeep R UInt8] (dst src : Ptr R)
    (n : Nat) : Keep (Ptr.memmove dst src n) := ⟨fun h r h' e => by
  unfold _root_.C.Ptr.memmove at e
  split at e
  · cases e
  · cases e
  · split at e
    · rename_i a as_ hg hs
      split at e
      · cases e
      · rename_i hro
        split at e
        · cases e
          exact dr_modify hg (by simpa using hro) _
        · cases e
    · cases e⟩

/-! ## The decomposition tactic -/

open Lean Meta Elab Tactic in
/-- One step of `keep_tac` on the main goal: close it by a hypothesis, introduce a binder, or decompose a `Keep` goal
by the head of its computation (bind, pure, `have`, a join point, `if` / `match`, a `for` loop, a function's `K.`
lemma, or the definition). -/
def keepStep : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let t ← whnf (← instantiateMVars (← g.getType))
    if t.isForall then
      let (_, g') ← g.intro1
      replaceMainGoal [g']
      return
    let fn := t.getAppFn
    unless fn.isConstOf ``Keep do throwError "keep_step: unexpected goal {t}"
    let e := (t.appArg!).headBeta.consumeMData
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let dt ← instantiateMVars d.type
      if dt.getAppFn == fn && dt.getAppNumArgs == t.getAppNumArgs && dt.appArg!.consumeMData == e then
        g.assign (mkFVar d.fvarId)
        replaceMainGoal []
        return
    let g ← g.replaceTargetDefEq (mkApp t.appFn! e)
    let applyC (n : Name) : TacticM Unit := do
      let gs ← g.apply (← mkConstWithFreshMVarLevels n)
      replaceMainGoal gs
    -- `have x := v; b x`: a join point gets its `KeepF` hypothesis, a value is substituted
    let haveStep (ty v f : Expr) : TacticM Unit := do
      let inst? ← try some <$> synthInstance (mkApp (mkConst ``KeepF) ty) catch _ => pure none
      match inst? with
      | some _ =>
        let pf ← mkAppOptM ``keep_have #[ty, none, none, v, f]
        let gs ← g.apply pf
        replaceMainGoal gs
      | none =>
        let g' ← g.replaceTargetDefEq (mkApp t.appFn! (f.beta #[v]))
        replaceMainGoal [g']
    match e with
    | .letE n ty v b _ => haveStep ty v (mkLambda n .default ty b)
    | _ =>
      let hd := e.getAppFn
      if hd.isConstOf ``letFun && e.getAppNumArgs == 4 then
        let args := e.getAppArgs
        haveStep args[0]! args[2]! args[3]!
        return
      if hd.isFVar then
        for d in (← getLCtx) do
          if d.isImplementationDetail then continue
          let dt ← instantiateMVars d.type
          if dt.isAppOf ``KeepF.P && dt.appArg!.consumeMData == hd then
            let gs ← g.apply (mkFVar d.fvarId)
            replaceMainGoal gs
            return
        throwError "keep_step: no KeepF hypothesis for {hd}"
      if hd.isProj || hd.isConstOf ``ForIn.forIn then
        try applyC ``keep_forIn_array
        catch _ =>
          try applyC ``keep_forIn_list
          catch _ => applyC ``keep_forIn_range
        return
      let some n := hd.constName? | throwError "keep_step: head {hd}"
      if n == ``Bind.bind then applyC ``keep_bind
      else if n == ``Pure.pure then applyC ``keep_pure
      else if n == ``C.ub then applyC ``keep_ub
      else if n == ``ite then applyC ``keep_ite
      else if n == ``dite then applyC ``keep_dite
      else if (← isMatcher n) then
        replaceMainGoal [g]
        evalTactic (← `(tactic| split))
      else
        let k := `ZlibNgF.Proof.DeflateKeep.K ++ n
        if (← getEnv).contains k && (← Term.getDeclName?) != some k then applyC k
        else
          let g' ← unfoldTarget g n
          replaceMainGoal [g']

open Lean Elab Tactic in
elab "keep_step" : tactic => keepStep

open Lean Meta Elab Tactic in
/-- Decompose `Keep` goals down to the primitives, goal by goal; a side condition (of `wrD` / `wrZ`, or of a primitive)
is closed by `rfl` or `decide`, or left as a goal. -/
elab "keep_tac" : tactic => do
  let mut todo ← getGoals
  let mut stuck : List MVarId := []
  for _ in [0:1000000] do
    match todo with
    | [] => break
    | g :: rest =>
      if ← g.isAssigned then
        todo := rest
        continue
      setGoals [g]
      let ok ← try keepStep; pure true catch _ => pure false
      if ok then
        todo := (← getGoals) ++ rest
      else
        setGoals [g]
        let ok2 ← try evalTactic (← `(tactic| first | rfl | decide | exact descSel_set_gzhead _ _ _)); pure true catch _ => pure false
        todo := rest
        unless ok2 do stuck := stuck ++ [g]
  setGoals (stuck ++ todo)

/-! ## Every function that `deflate` and `deflateParams` reach

Each lemma is the decomposition of the function down to the lemmas above (`keep_tac`); a callee with a lemma of its own
is not unfolded again. -/

section translation
open ZlibNg.Zbuild ZlibNg.Crc32Braid ZlibNg.Adler32C ZlibNg.DeflateP ZlibNg.Trees ZlibNg.TreesEmit
open ZlibNg.InsertStringP ZlibNg.InsertString ZlibNg.Compare256 ZlibNg.DeflateMedium ZlibNg.DeflateQuick

theorem K.ZlibNg.Inflate.rdZ {α : Type} (strm : StreamPtr) (f : ZStream → α) :
    Keep (_root_.ZlibNg.Inflate.rdZ strm f) := by keep_tac
theorem K.ZlibNg.Zutil.zError (err : Int32) :
    Keep (_root_.ZlibNg.Zutil.zError err) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do1 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do1 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do2 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do2 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do4 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do4 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.loadU64 (p : BPtr) (i : Nat) :
    Keep (_root_.ZlibNg.Adler32P.loadU64 p i) := by keep_tac
theorem K.ZlibNg.Adler32P.storeU64 (dst : BPtr) (v : UInt64) :
    Keep (_root_.ZlibNg.Adler32P.storeU64 dst v) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_copy_align (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (_MAX_LEN : Int32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_copy_align adler dst buf len sum2 _MAX_LEN COPY) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_swar (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_swar adler dst buf len sum2 COPY) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_copy_tail (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (REBASE : Int32) (_MAX_LEN : Int32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_copy_tail adler dst buf len sum2 REBASE _MAX_LEN COPY) := by keep_tac
theorem K.ZlibNg.Adler32C.adler32_copy_c (adler : UInt32) (dst : BPtr) (src : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Adler32C.adler32_copy_c adler dst src len) := by keep_tac
theorem K.ZlibNg.Crc32P.crcTab (i : UInt64) :
    Keep (_root_.ZlibNg.Crc32P.crcTab i) := by keep_tac
theorem K.ZlibNg.Crc32P.CRC_DO1 (c : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Crc32P.CRC_DO1 c buf i) := by keep_tac
theorem K.ZlibNg.Crc32P.CRC_DO2 (c : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Crc32P.CRC_DO2 c buf i) := by keep_tac
theorem K.ZlibNg.Crc32P.CRC_DO4 (c : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Crc32P.CRC_DO4 c buf i) := by keep_tac
theorem K.ZlibNg.Crc32P.CRC_DO8 (c : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Crc32P.CRC_DO8 c buf i) := by keep_tac
theorem K.ZlibNg.Crc32P.crc32_copy_small (crc : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (MAX_LEN : Int32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Crc32P.crc32_copy_small crc dst buf len MAX_LEN COPY) := by keep_tac
theorem K.ZlibNg.Crc32Braid.braidTab (k i : Nat) :
    Keep (_root_.ZlibNg.Crc32Braid.braidTab k i) := by keep_tac
theorem K.ZlibNg.Crc32Braid.loadWordAt (words : BPtr) (wordIdx : Nat) :
    Keep (_root_.ZlibNg.Crc32Braid.loadWordAt words wordIdx) := by keep_tac
theorem K.ZlibNg.Crc32Braid.crc_word (data : UInt64) :
    Keep (_root_.ZlibNg.Crc32Braid.crc_word data) := by keep_tac
theorem K.ZlibNg.Crc32Braid.crc32_braid (crc : UInt32) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Crc32Braid.crc32_braid crc buf len) := by keep_tac
theorem K.ZlibNg.Crc32Braid.crc32_copy_braid (crc : UInt32) (dst : BPtr) (src : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Crc32Braid.crc32_copy_braid crc dst src len) := by keep_tac
theorem K.ZlibNg.Crc32.crc32_small (crc : UInt32) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Crc32.crc32_small crc buf len) := by keep_tac

theorem K.ZlibNg.Deflate.zng_ctz32 (value : UInt32) :
    Keep (_root_.ZlibNg.Deflate.zng_ctz32 value) := by keep_tac
theorem K.ZlibNg.Deflate.zng_ctz64 (value : UInt64) :
    Keep (_root_.ZlibNg.Deflate.zng_ctz64 value) := by keep_tac
theorem K.ZlibNg.Deflate.zng_first_diff_byte64 (diff : UInt64) :
    Keep (_root_.ZlibNg.Deflate.zng_first_diff_byte64 diff) := by keep_tac
theorem K.ZlibNg.Deflate.zng_first_bytes_mask64 (n : UInt32) :
    Keep (_root_.ZlibNg.Deflate.zng_first_bytes_mask64 n) := by keep_tac
theorem K.ZlibNg.Deflate.rdD {α : Type} (st : StatePtr) (f : DeflateState → α) :
    Keep (_root_.ZlibNg.Deflate.rdD st f) := by keep_tac
theorem K.ZlibNg.Deflate.dstateOf (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.dstateOf strm) := by keep_tac
theorem K.ZlibNg.Deflate.dynLtreeP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.dynLtreeP st) := by keep_tac
theorem K.ZlibNg.Deflate.dynDtreeP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.dynDtreeP st) := by keep_tac
theorem K.ZlibNg.Deflate.blTreeP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.blTreeP st) := by keep_tac
theorem K.ZlibNg.Deflate.blCountP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.blCountP st) := by keep_tac
theorem K.ZlibNg.Deflate.pqLeavesP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.pqLeavesP st) := by keep_tac
theorem K.ZlibNg.Deflate.pqScratchP (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.pqScratchP st) := by keep_tac
theorem K.ZlibNg.Deflate.ctGet (p : CtPtr) (i : Int) :
    Keep (_root_.ZlibNg.Deflate.ctGet p i) := by keep_tac
theorem K.ZlibNg.Deflate.ctSet (p : CtPtr) (i : Int) (v : Ct) :
    Keep (_root_.ZlibNg.Deflate.ctSet p i v) := by keep_tac
theorem K.ZlibNg.Deflate.ctFc (p : CtPtr) (i : Int) :
    Keep (_root_.ZlibNg.Deflate.ctFc p i) := by keep_tac
theorem K.ZlibNg.Deflate.ctDl (p : CtPtr) (i : Int) :
    Keep (_root_.ZlibNg.Deflate.ctDl p i) := by keep_tac
theorem K.ZlibNg.Deflate.ctSetFc (p : CtPtr) (i : Int) (v : UInt16) :
    Keep (_root_.ZlibNg.Deflate.ctSetFc p i v) := by keep_tac
theorem K.ZlibNg.Deflate.ctSetDl (p : CtPtr) (i : Int) (v : UInt16) :
    Keep (_root_.ZlibNg.Deflate.ctSetDl p i v) := by keep_tac
theorem K.ZlibNg.Deflate.put_byte (st : StatePtr) (c : UInt8) :
    Keep (_root_.ZlibNg.Deflate.put_byte st c) := by keep_tac
theorem K.ZlibNg.Deflate.put_short (st : StatePtr) (w : UInt16) :
    Keep (_root_.ZlibNg.Deflate.put_short st w) := by keep_tac
theorem K.ZlibNg.Deflate.put_short_msb (st : StatePtr) (w : UInt16) :
    Keep (_root_.ZlibNg.Deflate.put_short_msb st w) := by keep_tac
theorem K.ZlibNg.Deflate.put_uint32 (st : StatePtr) (dw : UInt32) :
    Keep (_root_.ZlibNg.Deflate.put_uint32 st dw) := by keep_tac
theorem K.ZlibNg.Deflate.put_uint32_msb (st : StatePtr) (dw : UInt32) :
    Keep (_root_.ZlibNg.Deflate.put_uint32_msb st dw) := by keep_tac
theorem K.ZlibNg.Deflate.put_uint64 (st : StatePtr) (lld : UInt64) :
    Keep (_root_.ZlibNg.Deflate.put_uint64 st lld) := by keep_tac
theorem K.ZlibNg.Deflate.W_BITS (s : DeflateState) :
    Keep (_root_.ZlibNg.Deflate.W_BITS s) := by keep_tac
theorem K.ZlibNg.Deflate.d_code (dist : UInt32) :
    Keep (_root_.ZlibNg.Deflate.d_code dist) := by keep_tac
theorem K.ZlibNg.SlideHash.slide_hash_c_chain (table : BPtr) (entries : UInt32) (wsize : UInt16) :
    Keep (_root_.ZlibNg.SlideHash.slide_hash_c_chain table entries wsize) := by keep_tac
theorem K.ZlibNg.SlideHash.slide_hash_c (st : StatePtr) :
    Keep (_root_.ZlibNg.SlideHash.slide_hash_c st) := by keep_tac
theorem K.ZlibNg.SlideHash.slide_hash_head_c (st : StatePtr) :
    Keep (_root_.ZlibNg.SlideHash.slide_hash_head_c st) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_val (st : StatePtr) (str val : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_val st str val) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_val_head (st : StatePtr) (str val : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_val_head st str val) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth (st : StatePtr) (window : BPtr) (str : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth st window str) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_head (st : StatePtr) (window : BPtr) (str : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_head st window str) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_one (headp prevp : BPtr) (w_mask : UInt32) (window : BPtr) (idx : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_one headp prevp w_mask window idx) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_roll (st : StatePtr) (window : BPtr) (str : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_roll st window str) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_batch_static (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_batch_static st window str count) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_stepped_static (st : StatePtr) (window : BPtr) (str count max_inserts : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_stepped_static st window str count max_inserts) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_batch_head_static (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_batch_head_static st window str count) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_roll_batch_static (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_roll_batch_static st window str count) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_skip (st : StatePtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_skip st str count) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_batch_tail_static (st : StatePtr) (window : BPtr) (str count tail : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_batch_tail_static st window str count tail) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_roll_batch_tail_static (st : StatePtr) (window : BPtr) (str count tail : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_roll_batch_tail_static st window str count tail) := by keep_tac
theorem K.ZlibNg.InsertString.insert_knuth_batch (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertString.insert_knuth_batch st window str count) := by keep_tac
theorem K.ZlibNg.InsertString.insert_knuth_stepped (st : StatePtr) (window : BPtr) (str count step : UInt32) :
    Keep (_root_.ZlibNg.InsertString.insert_knuth_stepped st window str count step) := by keep_tac
theorem K.ZlibNg.InsertString.insert_roll_batch (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertString.insert_roll_batch st window str count) := by keep_tac
theorem K.ZlibNg.InsertString.insert_knuth_batch_head (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertString.insert_knuth_batch_head st window str count) := by keep_tac
theorem K.ZlibNg.InsertString.call_insert_batch (f : InsertBatchFn) (st : StatePtr) (window : BPtr) (str count : UInt32) :
    Keep (_root_.ZlibNg.InsertString.call_insert_batch f st window str count) := by keep_tac
theorem K.ZlibNg.InsertStringP.insert_knuth_spread_static (st : StatePtr) (window : BPtr) (str count max_inserts : UInt32) :
    Keep (_root_.ZlibNg.InsertStringP.insert_knuth_spread_static st window str count max_inserts) := by keep_tac
theorem K.ZlibNg.Compare256.compare256_8_static (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.Compare256.compare256_8_static src0 src1) := by keep_tac
theorem K.ZlibNg.Compare256.compare256_64_static (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.Compare256.compare256_64_static src0 src1) := by keep_tac
theorem K.ZlibNg.Compare256.compare256_8 (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.Compare256.compare256_8 src0 src1) := by keep_tac
theorem K.ZlibNg.Compare256.compare256_64 (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.Compare256.compare256_64 src0 src1) := by keep_tac
theorem K.ZlibNg.Compare256.compare256_c (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.Compare256.compare256_c src0 src1) := by keep_tac
theorem K.ZlibNg.Compare256.zng_memcmp_8_local (src0 : BPtr) (v : UInt64) :
    Keep (_root_.ZlibNg.Compare256.zng_memcmp_8_local src0 v) := by keep_tac
theorem K.ZlibNg.Compare256.LM.GOTO_NEXT_CHAIN (e : LMEnv) (v : LMVars) :
    Keep (_root_.ZlibNg.Compare256.LM.GOTO_NEXT_CHAIN e v) := by keep_tac
theorem K.ZlibNg.Compare256.LM.goto_next_chain_outer (e : LMEnv) (v : LMVars) :
    Keep (_root_.ZlibNg.Compare256.LM.goto_next_chain_outer e v) := by keep_tac
theorem K.ZlibNg.Compare256.LM.short_walk (e : LMEnv) (first_mask : UInt64) (v : LMVars) (cand_start : UInt64) :
    Keep (_root_.ZlibNg.Compare256.LM.short_walk e first_mask v cand_start) := by keep_tac
theorem K.ZlibNg.Compare256.LM.short_filter (e : LMEnv) (v : LMVars) :
    Keep (_root_.ZlibNg.Compare256.LM.short_filter e v) := by keep_tac
theorem K.ZlibNg.Compare256.LM.long_filter (e : LMEnv) (v : LMVars) :
    Keep (_root_.ZlibNg.Compare256.LM.long_filter e v) := by keep_tac
theorem K.ZlibNg.Compare256.LM.offset_search_block (e : LMEnv) (v : LMVars) (len : UInt32) :
    Keep (_root_.ZlibNg.Compare256.LM.offset_search_block e v len) := by keep_tac
theorem K.ZlibNg.Compare256.LM.short_match_accept (e : LMEnv) (v : LMVars) (len : UInt32) :
    Keep (_root_.ZlibNg.Compare256.LM.short_match_accept e v len) := by keep_tac
theorem K.ZlibNg.Compare256.LM.loop_body (e : LMEnv) (v : LMVars) :
    Keep (_root_.ZlibNg.Compare256.LM.loop_body e v) := by keep_tac
theorem K.ZlibNg.Compare256.LONGEST_MATCH (slow roll : Bool) (st : StatePtr) (cur_match : UInt32) :
    Keep (_root_.ZlibNg.Compare256.LONGEST_MATCH slow roll st cur_match) := by keep_tac
theorem K.ZlibNg.Compare256.longest_match_c (st : StatePtr) (cur_match : UInt32) :
    Keep (_root_.ZlibNg.Compare256.longest_match_c st cur_match) := by keep_tac
theorem K.ZlibNg.Compare256.longest_match_slow_knuth_c (st : StatePtr) (cur_match : UInt32) :
    Keep (_root_.ZlibNg.Compare256.longest_match_slow_knuth_c st cur_match) := by keep_tac
theorem K.ZlibNg.Compare256.longest_match_slow_roll_c (st : StatePtr) (cur_match : UInt32) :
    Keep (_root_.ZlibNg.Compare256.longest_match_slow_roll_c st cur_match) := by keep_tac
theorem K.ZlibNg.Compare256.call_longest_match (f : LongestMatchFn) (st : StatePtr) (cur_match : UInt32) :
    Keep (_root_.ZlibNg.Compare256.call_longest_match f st cur_match) := by keep_tac
theorem K.ZlibNg.TreesEmit.send_bits (st : StatePtr) (t_val : UInt64) (t_len : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.send_bits st t_val t_len bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.send_bits_merge (_st : StatePtr) (t_val : UInt64) (t_len : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.send_bits_merge _st t_val t_len bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.send_bits_flush (st : StatePtr) (bi_buf : UInt64) (bi_valid : UInt32) (pending : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.send_bits_flush st bi_buf bi_valid pending) := by keep_tac
theorem K.ZlibNg.TreesEmit.send_code (st : StatePtr) (c : Int) (tree : CtPtr) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.send_code st c tree bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.send_code_merge (st : StatePtr) (c : Int) (tree : CtPtr) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.send_code_merge st c tree bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.bi_windup (st : StatePtr) :
    Keep (_root_.ZlibNg.TreesEmit.bi_windup st) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_emit_lit (st : StatePtr) (ltree : CtPtr) (c : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_emit_lit st ltree c bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_assemble_dist (ltree dtree : CtPtr) (lc dist : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_assemble_dist ltree dtree lc dist) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_emit_dist (st : StatePtr) (ltree dtree : CtPtr) (lc dist : UInt32) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_emit_dist st ltree dtree lc dist bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_emit_end_block (st : StatePtr) (ltree : CtPtr) (_last : Int32) (bi_buf : UInt64) (bi_valid : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_emit_end_block st ltree _last bi_buf bi_valid) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_tr_emit_lit (st : StatePtr) (ltree : CtPtr) (c : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_tr_emit_lit st ltree c) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_tr_emit_dist (st : StatePtr) (ltree dtree : CtPtr) (lc dist : UInt32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_tr_emit_dist st ltree dtree lc dist) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_tr_emit_tree (st : StatePtr) (type : Int32) (last : Int32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_tr_emit_tree st type last) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_tr_emit_align (st : StatePtr) :
    Keep (_root_.ZlibNg.TreesEmit.zng_tr_emit_align st) := by keep_tac
theorem K.ZlibNg.TreesEmit.zng_tr_emit_end_block (st : StatePtr) (ltree : CtPtr) (last : Int32) :
    Keep (_root_.ZlibNg.TreesEmit.zng_tr_emit_end_block st ltree last) := by keep_tac
theorem K.ZlibNg.Trees.bi_reverse (code : UInt16) (len : Int32) :
    Keep (_root_.ZlibNg.Trees.bi_reverse code len) := by keep_tac
theorem K.ZlibNg.Trees.lget {α : Type} [Inhabited α] (a : Array α) (i : Int32) :
    Keep (_root_.ZlibNg.Trees.lget a i) := by keep_tac
theorem K.ZlibNg.Trees.lset {α : Type} (a : Array α) (i : Int32) (v : α) :
    Keep (_root_.ZlibNg.Trees.lset a i v) := by keep_tac
theorem K.ZlibNg.Trees.descDynTree (st : StatePtr) (d : DescSel) :
    Keep (_root_.ZlibNg.Trees.descDynTree st d) := by keep_tac
theorem K.ZlibNg.Trees.descStat (st : StatePtr) (d : DescSel) :
    Keep (_root_.ZlibNg.Trees.descStat st d) := by keep_tac
theorem K.ZlibNg.Trees.blCountGet (st : StatePtr) (i : Int) :
    Keep (_root_.ZlibNg.Trees.blCountGet st i) := by keep_tac
theorem K.ZlibNg.Trees.blCountSet (st : StatePtr) (i : Int) (v : UInt16) :
    Keep (_root_.ZlibNg.Trees.blCountSet st i v) := by keep_tac
theorem K.ZlibNg.Trees.dwGet (p : DWPtr) (i : Int) :
    Keep (_root_.ZlibNg.Trees.dwGet p i) := by keep_tac
theorem K.ZlibNg.Trees.dwSet (p : DWPtr) (i : Int) (v : UInt32) :
    Keep (_root_.ZlibNg.Trees.dwSet p i v) := by keep_tac
theorem K.ZlibNg.Trees.init_block (st : StatePtr) :
    Keep (_root_.ZlibNg.Trees.init_block st) := by keep_tac
theorem K.ZlibNg.Trees.pq_radix_pass (src dst : DWPtr) (n shift : Int32) (count : Array UInt16) :
    Keep (_root_.ZlibNg.Trees.pq_radix_pass src dst n shift count) := by keep_tac
theorem K.ZlibNg.Trees.pq_take (leaves : DWPtr) (li nleaves : Int32) (internals : DWPtr) (ihead itail : Int32) :
    Keep (_root_.ZlibNg.Trees.pq_take leaves li nleaves internals ihead itail) := by keep_tac
theorem K.ZlibNg.Trees.gen_bitlen (st : StatePtr) (desc : DescSel) (sorted : DWPtr) (nleaves root : Int32) :
    Keep (_root_.ZlibNg.Trees.gen_bitlen st desc sorted nleaves root) := by keep_tac
theorem K.ZlibNg.Trees.gen_codes (tree : CtPtr) (max_code : Int32) (bl_count : DHPtr) :
    Keep (_root_.ZlibNg.Trees.gen_codes tree max_code bl_count) := by keep_tac
theorem K.ZlibNg.Trees.build_tree (st : StatePtr) (desc : DescSel) :
    Keep (_root_.ZlibNg.Trees.build_tree st desc) := by keep_tac
theorem K.ZlibNg.Trees.scan_tree (st : StatePtr) (tree : CtPtr) (max_code : Int32) :
    Keep (_root_.ZlibNg.Trees.scan_tree st tree max_code) := by keep_tac
theorem K.ZlibNg.Trees.send_tree (st : StatePtr) (tree : CtPtr) (max_code : Int32) :
    Keep (_root_.ZlibNg.Trees.send_tree st tree max_code) := by keep_tac
theorem K.ZlibNg.Trees.build_bl_tree (st : StatePtr) :
    Keep (_root_.ZlibNg.Trees.build_bl_tree st) := by keep_tac
theorem K.ZlibNg.Trees.send_all_trees (st : StatePtr) (lcodes dcodes blcodes : Int32) :
    Keep (_root_.ZlibNg.Trees.send_all_trees st lcodes dcodes blcodes) := by keep_tac
theorem K.ZlibNg.Trees.zng_tr_stored_block (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) :
    Keep (_root_.ZlibNg.Trees.zng_tr_stored_block st buf stored_len last) := by keep_tac
theorem K.ZlibNg.Trees.zng_tr_flush_bits (st : StatePtr) :
    Keep (_root_.ZlibNg.Trees.zng_tr_flush_bits st) := by keep_tac
theorem K.ZlibNg.Trees.zng_tr_align (st : StatePtr) :
    Keep (_root_.ZlibNg.Trees.zng_tr_align st) := by keep_tac
theorem K.ZlibNg.Trees.compress_block (st : StatePtr) (ltree dtree : CtPtr) :
    Keep (_root_.ZlibNg.Trees.compress_block st ltree dtree) := by keep_tac
theorem K.ZlibNg.Trees.detect_data_type (st : StatePtr) :
    Keep (_root_.ZlibNg.Trees.detect_data_type st) := by keep_tac
theorem K.ZlibNg.Trees.zng_tr_flush_block (st : StatePtr) (buf : BPtr) (stored_len : UInt32) (last : Int32) :
    Keep (_root_.ZlibNg.Trees.zng_tr_flush_block st buf stored_len last) := by keep_tac
theorem K.ZlibNg.DeflateP.zng_tr_tally_lit (st : StatePtr) (c : UInt8) :
    Keep (_root_.ZlibNg.DeflateP.zng_tr_tally_lit st c) := by keep_tac
theorem K.ZlibNg.DeflateP.zng_tr_tally_dist (st : StatePtr) (dist len : UInt32) :
    Keep (_root_.ZlibNg.DeflateP.zng_tr_tally_dist st dist len) := by keep_tac
theorem K.ZlibNg.DeflateP.flush_pending_inline (strm : StreamPtr) :
    Keep (_root_.ZlibNg.DeflateP.flush_pending_inline strm) := by keep_tac
theorem K.ZlibNg.DeflateP.flush_pending (strm : StreamPtr) :
    Keep (_root_.ZlibNg.DeflateP.flush_pending strm) := by keep_tac
theorem K.ZlibNg.DeflateP.read_buf (strm : StreamPtr) (buf : BPtr) (size : UInt32) :
    Keep (_root_.ZlibNg.DeflateP.read_buf strm buf size) := by keep_tac
theorem K.ZlibNg.DeflateP.max_match_continues (window : BPtr) (strstart dist : UInt32) :
    Keep (_root_.ZlibNg.DeflateP.max_match_continues window strstart dist) := by keep_tac
theorem K.ZlibNg.DeflateP.FLUSH_BLOCK (st : StatePtr) (window : BPtr) (last : Int32) :
    Keep (_root_.ZlibNg.DeflateP.FLUSH_BLOCK st window last) := by keep_tac
theorem K.ZlibNg.Deflate.fill_window_slide (st : StatePtr) (window : BPtr) (level : Int32) :
    Keep (_root_.ZlibNg.Deflate.fill_window_slide st window level) := by keep_tac
theorem K.ZlibNg.Deflate.fill_window_read (st : StatePtr) (strm : StreamPtr) (insert_batch : InsertBatchFn) (window : BPtr) (level : Int32) :
    Keep (_root_.ZlibNg.Deflate.fill_window_read st strm insert_batch window level) := by keep_tac
theorem K.ZlibNg.Deflate.fill_window (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.fill_window st) := by keep_tac
theorem K.ZlibNg.DeflateStored.strmOf (st : StatePtr) :
    Keep (_root_.ZlibNg.DeflateStored.strmOf st) := by keep_tac
theorem K.ZlibNg.DeflateStored.headerBytes (st : StatePtr) :
    Keep (_root_.ZlibNg.DeflateStored.headerBytes st) := by keep_tac
theorem K.ZlibNg.DeflateStored.leftOf (st : StatePtr) :
    Keep (_root_.ZlibNg.DeflateStored.leftOf st) := by keep_tac
theorem K.ZlibNg.DeflateStored.stored_trip (st : StatePtr) (window : BPtr) (flush : Int32) (min_block : UInt32) (last : Int32) :
    Keep (_root_.ZlibNg.DeflateStored.stored_trip st window flush min_block last) := by keep_tac
theorem K.ZlibNg.DeflateStored.stored_update_window (st : StatePtr) (window : BPtr) (w_size used : UInt32) (last : Int32) :
    Keep (_root_.ZlibNg.DeflateStored.stored_update_window st window w_size used last) := by keep_tac
theorem K.ZlibNg.DeflateStored.deflate_stored (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateStored.deflate_stored st flush) := by keep_tac
theorem K.ZlibNg.DeflateQuick.strmOf (st : StatePtr) :
    Keep (_root_.ZlibNg.DeflateQuick.strmOf st) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_end_block (st : StatePtr) (strstart : UInt32) (last : Int32) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_end_block st strstart last static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_start_block (st : StatePtr) (strstart lookahead : UInt32) (last : Int32) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_start_block st strstart lookahead last static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_flush_pending (st : StatePtr) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_flush_pending st static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_emit_lit (st : StatePtr) (lit : UInt8) (strstart lookahead : UInt32) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_emit_lit st lit strstart lookahead static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_emit_dist (st : StatePtr) (match_len dist : UInt32) (strstart lookahead : UInt32) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_emit_dist st match_len dist strstart lookahead static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_cont_trip (st : StatePtr) (window : BPtr) (static_emit : Int32) (cont_dist : UInt32) (strstart lookahead : UInt32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_cont_trip st window static_emit cont_dist strstart lookahead) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_try_match (st : StatePtr) (window : BPtr) (static_emit : Int32) (strstart lookahead str_val : UInt32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_try_match st window static_emit strstart lookahead str_val) := by keep_tac
theorem K.ZlibNg.DeflateQuick.quick_trip (st : StatePtr) (window : BPtr) (flush : Int32) (last : UInt32) (static_emit : Int32) (strstart lookahead : UInt32) :
    Keep (_root_.ZlibNg.DeflateQuick.quick_trip st window flush last static_emit strstart lookahead) := by keep_tac
theorem K.ZlibNg.DeflateQuick.deflate_quick_impl (st : StatePtr) (flush : Int32) (static_emit : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.deflate_quick_impl st flush static_emit) := by keep_tac
theorem K.ZlibNg.DeflateQuick.deflate_quick (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateQuick.deflate_quick st flush) := by keep_tac
theorem K.ZlibNg.DeflateFast.deflate_fast_cont_trip (st : StatePtr) (window : BPtr) (max_inserts cont_dist : UInt32) (bflush : Bool) :
    Keep (_root_.ZlibNg.DeflateFast.deflate_fast_cont_trip st window max_inserts cont_dist bflush) := by keep_tac
theorem K.ZlibNg.DeflateFast.deflate_fast_trip (st : StatePtr) (flush : Int32) (window : BPtr) (max_inserts : UInt32) (bflush : Bool) (match_len : UInt32) :
    Keep (_root_.ZlibNg.DeflateFast.deflate_fast_trip st flush window max_inserts bflush match_len) := by keep_tac
theorem K.ZlibNg.DeflateFast.deflate_fast (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateFast.deflate_fast st flush) := by keep_tac
theorem K.ZlibNg.DeflateMedium.memcmp (s1 s2 : BPtr) (n : Nat) :
    Keep (_root_.ZlibNg.DeflateMedium.memcmp s1 s2 n) := by keep_tac
theorem K.ZlibNg.DeflateMedium.insert_match (st : StatePtr) (window : BPtr) (match_ : Match) (max_insert_count : UInt32) :
    Keep (_root_.ZlibNg.DeflateMedium.insert_match st window match_ max_insert_count) := by keep_tac
theorem K.ZlibNg.DeflateMedium.find_best_match (st : StatePtr) (hash_head : UInt32) (max_dist : Int32) :
    Keep (_root_.ZlibNg.DeflateMedium.find_best_match st hash_head max_dist) := by keep_tac
theorem K.ZlibNg.DeflateMedium.fizzle_matches (window : BPtr) (current next : Match) (max_dist : Int32) :
    Keep (_root_.ZlibNg.DeflateMedium.fizzle_matches window current next max_dist) := by keep_tac
theorem K.ZlibNg.DeflateMedium.deflate_medium_cont_trip (st : StatePtr) (window : BPtr) (max_insert_count cont_dist : UInt32) (bflush : Bool) :
    Keep (_root_.ZlibNg.DeflateMedium.deflate_medium_cont_trip st window max_insert_count cont_dist bflush) := by keep_tac
theorem K.ZlibNg.DeflateMedium.deflate_medium_trip (fizzle : Bool) (st : StatePtr) (flush : Int32) (window : BPtr) (max_insert_count : UInt32) (max_dist : Int32) (current_match next_match : Match) :
    Keep (_root_.ZlibNg.DeflateMedium.deflate_medium_trip fizzle st flush window max_insert_count max_dist current_match next_match) := by keep_tac
theorem K.ZlibNg.DeflateMedium.deflate_medium_tpl (fizzle : Bool) (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateMedium.deflate_medium_tpl fizzle st flush) := by keep_tac
theorem K.ZlibNg.DeflateMedium.deflate_medium (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateMedium.deflate_medium st flush) := by keep_tac
theorem K.ZlibNg.DeflateMedium.deflate_medium_fizzle (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateMedium.deflate_medium_fizzle st flush) := by keep_tac
theorem K.ZlibNg.DeflateSlow.deflate_slow_trip (st : StatePtr) (flush : Int32) (longest_match : LongestMatchFn) (insert_batch : InsertBatchFn) (window : BPtr) (level : Int32) (match_discard match_floor : UInt32) :
    Keep (_root_.ZlibNg.DeflateSlow.deflate_slow_trip st flush longest_match insert_batch window level match_discard match_floor) := by keep_tac
theorem K.ZlibNg.DeflateSlow.deflate_slow (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateSlow.deflate_slow st flush) := by keep_tac
theorem K.ZlibNg.DeflateRle.compare256_rle_64 (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.DeflateRle.compare256_rle_64 src0 src1) := by keep_tac
theorem K.ZlibNg.DeflateRle.compare256_rle (src0 src1 : BPtr) :
    Keep (_root_.ZlibNg.DeflateRle.compare256_rle src0 src1) := by keep_tac
theorem K.ZlibNg.DeflateRle.rle_trip (st : StatePtr) (window : BPtr) (flush : Int32) (lookahead strstart match_len : UInt32) :
    Keep (_root_.ZlibNg.DeflateRle.rle_trip st window flush lookahead strstart match_len) := by keep_tac
theorem K.ZlibNg.DeflateRle.deflate_rle (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateRle.deflate_rle st flush) := by keep_tac
theorem K.ZlibNg.DeflateHuff.huff_trip (st : StatePtr) (window : BPtr) (flush : Int32) (lookahead strstart : UInt32) :
    Keep (_root_.ZlibNg.DeflateHuff.huff_trip st window flush lookahead strstart) := by keep_tac
theorem K.ZlibNg.DeflateHuff.deflate_huff (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.DeflateHuff.deflate_huff st flush) := by keep_tac
theorem K.ZlibNg.Deflate.config (level : Int32) :
    Keep (_root_.ZlibNg.Deflate.config level) := by keep_tac
theorem K.ZlibNg.Deflate.call_compress (f : CompressFn) (st : StatePtr) (flush : Int32) :
    Keep (_root_.ZlibNg.Deflate.call_compress f st flush) := by keep_tac
theorem K.ZlibNg.Deflate.RANK (f : Int32) :
    Keep (_root_.ZlibNg.Deflate.RANK f) := by keep_tac
theorem K.ZlibNg.Deflate.CLEAR_HASH (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.CLEAR_HASH st) := by keep_tac
theorem K.ZlibNg.Deflate.ERR_RETURN (strm : StreamPtr) (err : Int32) :
    Keep (_root_.ZlibNg.Deflate.ERR_RETURN strm err) := by keep_tac
theorem K.ZlibNg.Deflate.lm_set_level (st : StatePtr) (level : Int32) :
    Keep (_root_.ZlibNg.Deflate.lm_set_level st level) := by keep_tac
theorem K.ZlibNg.Deflate.deflateStateCheck (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.deflateStateCheck strm) := by keep_tac
theorem K.ZlibNg.Deflate.HCRC_UPDATE (strm : StreamPtr) (st : StatePtr) (beg : UInt32) :
    Keep (_root_.ZlibNg.Deflate.HCRC_UPDATE strm st beg) := by keep_tac
theorem K.ZlibNg.Deflate.pendingReturn (st : StatePtr) :
    Keep (_root_.ZlibNg.Deflate.pendingReturn st) := by keep_tac
theorem K.ZlibNg.Deflate.headersInit (s0 : DeflateState) (st : StatePtr) (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.headersInit s0 st strm) := by keep_tac
theorem K.ZlibNg.Deflate.headersGzip (st : StatePtr) (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.headersGzip st strm) := by keep_tac
theorem K.ZlibNg.Deflate.headersExtra (st : StatePtr) (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.headersExtra st strm) := by keep_tac
theorem K.ZlibNg.Deflate.headersString (st : StatePtr) (strm : StreamPtr) (str : GzHeader → BPtr) :
    Keep (_root_.ZlibNg.Deflate.headersString st strm str) := by keep_tac
theorem K.ZlibNg.Deflate.deflateHeaders (st : StatePtr) (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Deflate.deflateHeaders st strm) := by keep_tac
theorem K.ZlibNg.Deflate.deflate (strm : StreamPtr) (flush : Int32) :
    Keep (_root_.ZlibNg.Deflate.deflate strm flush) := by keep_tac
theorem K.ZlibNg.Deflate.deflateParams (strm : StreamPtr) (level strategy : Int32) :
    Keep (_root_.ZlibNg.Deflate.deflateParams strm level strategy) := by keep_tac
end translation

end ZlibNgF.Proof.DeflateKeep
