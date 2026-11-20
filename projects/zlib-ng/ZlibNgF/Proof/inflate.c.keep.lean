import Lean
import ZlibNgF.Spec.Common.Inflate
import ZlibNgF.ZlibNg.«infback.c»

/-!
# What every inflate-side function keeps (`ZlibNgF`)

`Keep m`: every run of `m` that returns keeps `KR`: no deflate object changes (`Heap.dstates`, `Heap.dallocs`), the
static bytes stay, `nextBlk` does not shrink, and `FreshBlocks` and `ObjBound` are kept. The rules decompose a
computation (bind, `have`, join points, `if`, `match`, `for`, the loops `cwhile`, `cdoWhile` and `xwhileBrk`) down to
the runtime primitives, whose lemmas are proved from their definitions; `keep_tac` applies them, and every
inflate-side function of the translation gets its lemma `K.<name>` (the call-back loop `inflateBack` excepted: its
call-backs are the caller's code). `iframe_up` turns the `Frame` of a call into the `IFrame` of the goals.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateKeep
open C ZlibNgF.Spec ZlibNg.Inflate

/-! ## The relation -/

/-- What every inflate-side primitive keeps from `h` to `h'`. -/
structure KR (h h' : Heap) : Prop where
  ds : h'.dstates = h.dstates
  da : h'.dallocs = h.dallocs
  cs : h'.consts = h.consts
  nb : h.nextBlk ≤ h'.nextBlk
  fresh : FreshBlocks h → FreshBlocks h'
  ob : ObjBound h → ObjBound h'

theorem KR.refl (h : Heap) : KR h h := ⟨rfl, rfl, rfl, Nat.le_refl _, id, id⟩

theorem KR.trans {h1 h2 h3 : Heap} (a : KR h1 h2) (b : KR h2 h3) : KR h1 h3 :=
  ⟨b.ds.trans a.ds, b.da.trans a.da, b.cs.trans a.cs, Nat.le_trans a.nb b.nb, fun f => b.fresh (a.fresh f),
    fun o => b.ob (a.ob o)⟩

/-- A computation of `M` whose every successful run keeps `KR`. -/
structure Keep {α : Type} (m : M α) : Prop where
  run : ∀ h r h', m h = .ok (r, h') → KR h h'

/-- A computation of `X` whose every successful run (from any locals) keeps `KR`. -/
structure KeepX {α : Type} (x : X α) : Prop where
  run : ∀ l, Keep (StateT.run (ExceptT.run x) l)

/-- `Keep` for functions into `M` / `X` (join points). -/
class KeepF (β : Type) where
  P : β → Prop

instance {α : Type} : KeepF (M α) := ⟨Keep⟩
instance {α : Type} : KeepF (X α) := ⟨KeepX⟩
instance {γ β : Type} [KeepF β] : KeepF (γ → β) := ⟨fun f => ∀ y, KeepF.P (f y)⟩

/-! ## Heap updates -/

theorem space_get_bref (h : Heap) (r : BRef) : Space.get h r = Heap.getBytes h r := rfl

/-- Nothing that `KR` looks at changed. -/
theorem kr_same {h h' : Heap} (ds : h'.dstates = h.dstates) (da : h'.dallocs = h.dallocs)
    (is : h'.istates = h.istates) (ia : h'.iallocs = h.iallocs) (bs : h'.bytes = h.bytes)
    (cs : h'.consts = h.consts) (nb : h'.nextBlk = h.nextBlk) : KR h h' := by
  refine ⟨ds, da, cs, by omega, fun f c hc => ?_, fun o r d hd => ?_⟩
  · rw [is, ia, bs]; exact f c (by omega)
  · apply o r d
    cases r <;> simp_all [space_get_bref, Heap.getBytes]

theorem fresh_lt {h : Heap} (f : FreshBlocks h) {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a) :
    b < h.nextBlk := by
  refine Nat.lt_of_not_le fun hle => ?_
  rw [(f b hle).2.2] at hb; cases hb

/-- The bytes of a live block change to an array no longer than before. -/
theorem kr_bytes {h h' : Heap} {b : Nat} {a a' : Array UInt8} (hb : h.bytes b = some a) (hs : a'.size ≤ a.size)
    (ds : h'.dstates = h.dstates) (da : h'.dallocs = h.dallocs)
    (is : h'.istates = h.istates) (ia : h'.iallocs = h.iallocs) (bs : h'.bytes = upd h.bytes b (some a'))
    (cs : h'.consts = h.consts) (nb : h'.nextBlk = h.nextBlk) : KR h h' := by
  refine ⟨ds, da, cs, by omega, fun f c hc => ?_, fun o r d hd => ?_⟩
  · have hcb : c ≠ b := by have := fresh_lt f hb; omega
    rw [is, ia, bs, upd_ne _ _ _ _ hcb]; exact f c (by omega)
  · cases r with
    | heap c =>
      simp only [space_get_bref, Heap.getBytes, bs] at hd
      by_cases hcb : c = b
      · subst hcb; rw [upd_same] at hd; cases hd
        have := o (.heap c) a (by simp [space_get_bref, Heap.getBytes, hb]); omega
      · rw [upd_ne _ _ _ _ hcb] at hd; exact o (.heap c) d (by simpa [space_get_bref, Heap.getBytes] using hd)
    | const c => exact o (.const c) d (by simpa [space_get_bref, Heap.getBytes, cs] using hd)
    | str i => exact o (.str i) d (by simpa [space_get_bref, Heap.getBytes] using hd)

/-- A block ends. -/
theorem kr_free {h h' : Heap} {b : Nat}
    (ds : h'.dstates = h.dstates) (da : h'.dallocs = h.dallocs)
    (is : h'.istates = h.istates) (ia : h'.iallocs = h.iallocs) (bs : h'.bytes = upd h.bytes b none)
    (cs : h'.consts = h.consts) (nb : h'.nextBlk = h.nextBlk) : KR h h' := by
  refine ⟨ds, da, cs, by omega, fun f c hc => ?_, fun o r d hd => ?_⟩
  · rw [is, ia, bs]
    by_cases hcb : c = b
    · subst hcb; rw [upd_same]; exact ⟨(f c (by omega)).1, (f c (by omega)).2.1, rfl⟩
    · rw [upd_ne _ _ _ _ hcb]; exact f c (by omega)
  · cases r with
    | heap c =>
      simp only [space_get_bref, Heap.getBytes, bs] at hd
      by_cases hcb : c = b
      · subst hcb; rw [upd_same] at hd; cases hd
      · rw [upd_ne _ _ _ _ hcb] at hd; exact o (.heap c) d (by simpa [space_get_bref, Heap.getBytes] using hd)
    | const c => exact o (.const c) d (by simpa [space_get_bref, Heap.getBytes, cs] using hd)
    | str i => exact o (.str i) d (by simpa [space_get_bref, Heap.getBytes] using hd)

/-- A new block at `nextBlk`. -/
theorem kr_alloc {h h' : Heap} {a : Array UInt8} (hs : a.size < 2 ^ 63)
    (ds : h'.dstates = h.dstates) (da : h'.dallocs = h.dallocs)
    (is : h'.istates = h.istates) (ia : h'.iallocs = h.iallocs) (bs : h'.bytes = upd h.bytes h.nextBlk (some a))
    (cs : h'.consts = h.consts) (nb : h'.nextBlk = h.nextBlk + 1) : KR h h' := by
  refine ⟨ds, da, cs, by omega, fun f c hc => ?_, fun o r d hd => ?_⟩
  · rw [is, ia, bs, upd_ne _ _ _ _ (by omega)]; exact f c (by omega)
  · cases r with
    | heap c =>
      simp only [space_get_bref, Heap.getBytes, bs] at hd
      by_cases hcb : c = h.nextBlk
      · subst hcb; rw [upd_same] at hd; cases hd; exact hs
      · rw [upd_ne _ _ _ _ hcb] at hd; exact o (.heap c) d (by simpa [space_get_bref, Heap.getBytes] using hd)
    | const c => exact o (.const c) d (by simpa [space_get_bref, Heap.getBytes, cs] using hd)
    | str i => exact o (.str i) d (by simpa [space_get_bref, Heap.getBytes] using hd)

/-- A typed inflate object of a live block changes. -/
theorem kr_obj {h h' : Heap} {b : Nat} {a : Array UInt8} (hb : h.bytes b = some a)
    (ds : h'.dstates = h.dstates) (da : h'.dallocs = h.dallocs)
    (is : ∀ c, c ≠ b → h'.istates c = h.istates c) (ia : ∀ c, c ≠ b → h'.iallocs c = h.iallocs c)
    (bs : h'.bytes = h.bytes) (cs : h'.consts = h.consts) (nb : h'.nextBlk = h.nextBlk) : KR h h' := by
  refine ⟨ds, da, cs, by omega, fun f c hc => ?_, fun o r d hd => ?_⟩
  · have hcb : c ≠ b := by have := fresh_lt f hb; omega
    rw [is c hcb, ia c hcb, bs]; exact f c (by omega)
  · apply o r d
    cases r <;> simp_all [space_get_bref, Heap.getBytes]

/-! ## Rules -/

theorem keep_pure {α : Type} (a : α) : Keep (pure a : M α) := ⟨fun h r h' e => by cases e; exact KR.refl h⟩

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

theorem keepX_have {β α : Type} [KeepF β] (v : β) (b : β → X α) (hv : KeepF.P v)
    (hb : ∀ x, KeepF.P x → KeepX (b x)) : KeepX (have x := v; b x) := hb v hv

theorem keep_ub {α : Type} (s : String) : Keep (ub s : M α) := ⟨fun _ _ _ e => by cases e⟩

theorem keep_fail {α : Type} (f : Fault) : Keep ((fun _ => .error f) : M α) := ⟨fun _ _ _ e => by cases e⟩

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

theorem keepX_ite {α : Type} {c : Prop} [inst : Decidable c] {a b : X α} (ha : c → KeepX a) (hb : ¬c → KeepX b) :
    KeepX (if c then a else b) := by
  cases inst with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

theorem keepX_dite {α : Type} {c : Prop} [inst : Decidable c] {a : c → X α} {b : ¬c → X α} (ha : ∀ h, KeepX (a h))
    (hb : ∀ h, KeepX (b h)) : KeepX (if h : c then a h else b h) := by
  cases inst with
  | isFalse h => exact hb h
  | isTrue h => exact ha h

/-! ## Rules of `X` -/

theorem keepX_of {α : Type} {x : X α} (h : ∀ l h0 r h', StateT.run (ExceptT.run x) l h0 = .ok (r, h') → KR h0 h') :
    KeepX x := ⟨fun l => ⟨fun h0 r h' e => h l h0 r h' e⟩⟩

theorem keepX_pure {α : Type} (a : α) : KeepX (pure a : X α) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _

theorem keepX_bind {α β : Type} {m : X α} {f : α → X β} (hm : KeepX m) (hf : ∀ a, KeepX (f a)) :
    KeepX (m >>= f) := by
  refine keepX_of fun l h0 r h' e => ?_
  simp only [StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind] at e
  split at e
  · rename_i p h1 e1
    obtain ⟨a, l1⟩ := p
    refine ((hm.run l).run _ _ _ e1).trans ?_
    cases a with
    | ok a => exact ((hf a).run l1).run _ _ _ e
    | error x => cases e; exact KR.refl _
  · cases e

theorem K.MonadLiftT.monadLift {α : Type} {m : M α} (hm : Keep m) : KeepX (MonadLiftT.monadLift m : X α) := by
  refine keepX_of fun l h0 r h' e => ?_
  change (Except.ok <$> StateT.lift m : StateT IL M (Except Ex α)) l h0 = _ at e
  simp only [Functor.map, StateT.map, StateT.lift, bind_app] at e
  rcases hmh : m h0 with _ | ⟨a, h1⟩
  · rw [hmh] at e; cases e
  · rw [hmh] at e; cases e; exact hm.run _ _ _ hmh

theorem K.MonadState.get : KeepX (MonadState.get : X IL) := keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.MonadStateOf.get : KeepX (MonadStateOf.get : X IL) := keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.getThe : KeepX (getThe IL : X IL) := keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.MonadStateOf.set (l : IL) : KeepX (MonadStateOf.set l : X PUnit) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.MonadState.set (l : IL) : KeepX (MonadState.set l : X PUnit) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.modify (f : IL → IL) : KeepX (modify f : X PUnit) := keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.modifyGet {β : Type} (f : IL → β × IL) : KeepX (modifyGet f : X β) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.MonadExcept.throw {α : Type} (x : Ex) : KeepX (MonadExcept.throw x : X α) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _
theorem K.throwThe {α : Type} (x : Ex) : KeepX (throwThe Ex x : X α) :=
  keepX_of fun _ _ _ _ e => by cases e; exact KR.refl _

theorem K.MonadExcept.tryCatch {α : Type} {m : X α} {hd : Ex → X α} (hm : KeepX m) (hh : ∀ x, KeepX (hd x)) :
    KeepX (tryCatch m hd) := by
  refine keepX_of fun l h0 r h' e => ?_
  simp only [_root_.MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run,
    ExceptT.mk, StateT.run, bind, StateT.bind] at e
  split at e
  · rename_i p h1 e1
    obtain ⟨a, l1⟩ := p
    refine ((hm.run l).run _ _ _ e1).trans ?_
    cases a with
    | ok a => cases e; exact KR.refl _
    | error x => exact ((hh x).run l1).run _ _ _ e
  · cases e

theorem K.StateT.run {α : Type} {x : X α} (hx : KeepX x) (l : IL) : Keep (StateT.run (ExceptT.run x) l) :=
  hx.run l

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
      | false => cases e; exact KR.refl _
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
        | false => cases e; exact KR.refl _
      · cases e
    · cases e

/-! ## Primitives -/

set_option hygiene false in
/-- The run of a primitive that only reads leaves the heap. -/
macro "rd_tac" : tactic => `(tactic| (repeat' split at e) <;> first | (cases e; exact KR.refl _) | cases e)

theorem K.C.ldStream (p : StreamPtr) : Keep (ldStream p) := ⟨fun h r h' e => by unfold _root_.C.ldStream at e; rd_tac⟩
theorem K.C.ldHeader (p : HeaderPtr) : Keep (ldHeader p) := ⟨fun h r h' e => by unfold _root_.C.ldHeader at e; rd_tac⟩
theorem K.C.ldState (p : StatePtr) : Keep (ldState p) := ⟨fun h r h' e => by unfold _root_.C.ldState at e; rd_tac⟩
theorem K.C.ldAllocs (p : AllocsPtr) : Keep (ldAllocs p) := ⟨fun h r h' e => by unfold _root_.C.ldAllocs at e; rd_tac⟩
theorem K.C.addrOf (p : BPtr) : Keep (addrOf p) := ⟨fun h r h' e => by unfold _root_.C.addrOf at e; rd_tac⟩
theorem K.C.strLitRef (s : String) : Keep (strLitRef s) := ⟨fun h r h' e => by unfold _root_.C.strLitRef at e; rd_tac⟩
theorem K.C.uninitLocals (k : Nat) : Keep (uninitLocals k) := ⟨fun h r h' e => by unfold _root_.C.uninitLocals at e; rd_tac⟩
theorem K.C.carveCheck (p : BPtr) (size align : Nat) : Keep (carveCheck p size align) :=
  ⟨fun h r h' e => by unfold _root_.C.carveCheck at e; rd_tac⟩
theorem K.C.loadPtrSlot (p : BPtr) : Keep (loadPtrSlot p) := ⟨fun h r h' e => by unfold _root_.C.loadPtrSlot at e; rd_tac⟩

section generic
variable {R T : Type} [Space Heap R T]
theorem K.C.Ptr.add (p : Ptr R) (k : Int) : Keep (Ptr.add p k) := ⟨fun h r h' e => by unfold _root_.C.Ptr.add at e; rd_tac⟩
theorem K.C.Ptr.load (p : Ptr R) : Keep (Ptr.load p : M T) := ⟨fun h r h' e => by unfold _root_.C.Ptr.load at e; rd_tac⟩
theorem K.C.Ptr.diff [DecidableEq R] (p q : Ptr R) : Keep (Ptr.diff p q) :=
  ⟨fun h r h' e => by unfold _root_.C.Ptr.diff at e; rd_tac⟩
theorem K.C.Ptr.lt [DecidableEq R] (p q : Ptr R) : Keep (Ptr.lt p q) := ⟨fun h r h' e => by unfold _root_.C.Ptr.lt at e; rd_tac⟩
end generic

theorem K.C.stStream (p : StreamPtr) (z : ZStream) : Keep (stStream p z) := ⟨fun h r h' e => by
  unfold _root_.C.stStream at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl)⟩
theorem K.C.stHeader (p : HeaderPtr) (g : GzHeader) : Keep (stHeader p g) := ⟨fun h r h' e => by
  unfold _root_.C.stHeader at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl)⟩
theorem K.C.newStream (z : ZStream) : Keep (newStream z) := ⟨fun h r h' e => by
  unfold _root_.C.newStream at e; cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl⟩
theorem K.C.dropStream (p : StreamPtr) : Keep (dropStream p) := ⟨fun h r h' e => by
  unfold _root_.C.dropStream at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl)⟩
theorem K.C.storePtrSlot (p v : BPtr) : Keep (storePtrSlot p v) := ⟨fun h r h' e => by
  unfold _root_.C.storePtrSlot at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl)⟩

theorem K.C.stState (p : StatePtr) (s : InflateState) : Keep (stState p s) := ⟨fun h r h' e => by
  unfold _root_.C.stState at e
  split at e
  · cases e
  · rename_i b
    split at e
    · rename_i hs
      cases e
      simp only [Heap.istate] at hs
      split at hs
      · rename_i a hb
        exact kr_obj hb rfl rfl (fun c hc => upd_ne _ _ _ _ hc) (fun _ _ => rfl) rfl rfl rfl
      · cases hs
    · cases e⟩

theorem K.C.stAllocs (p : AllocsPtr) (a : InflateAllocs) : Keep (stAllocs p a) := ⟨fun h r h' e => by
  unfold _root_.C.stAllocs at e
  split at e
  · cases e
  · rename_i b
    split at e
    · rename_i hs
      cases e
      simp only [Heap.iallocsOf] at hs
      split at hs
      · rename_i a hb
        exact kr_obj hb rfl rfl (fun _ _ => rfl) (fun c hc => upd_ne _ _ _ _ hc) rfl rfl rfl
      · cases hs
    · cases e⟩

theorem K.C.freeB (p : BPtr) : Keep (freeB p) := ⟨fun h r h' e => by
  unfold _root_.C.freeB at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact KR.refl _) | (cases e; exact kr_free rfl rfl rfl rfl rfl rfl rfl)⟩

theorem K.C.dropLocal (p : BPtr) : Keep (dropLocal p) := ⟨fun h r h' e => by
  unfold _root_.C.dropLocal at e
  repeat' split at e
  all_goals first | (cases e; done) | (cases e; exact kr_free rfl rfl rfl rfl rfl rfl rfl)⟩

/-- `malloc` of fewer than `2^63` bytes. -/
theorem keep_allocB (n : Nat) (hn : n < 2 ^ 63) : Keep (allocB n) := ⟨fun h r h' e => by
  unfold _root_.C.allocB at e
  split at e
  · cases e; exact kr_alloc (by simpa using hn) rfl rfl rfl rfl rfl rfl rfl
  · cases e; exact kr_same rfl rfl rfl rfl rfl rfl rfl⟩

theorem K.C.localBlock (n : Nat) (hn : n < 2 ^ 63) : Keep (localBlock n) := ⟨fun h r h' e => by
  unfold _root_.C.localBlock at e
  cases e; exact kr_alloc (by simpa using hn) rfl rfl rfl rfl rfl rfl rfl⟩

theorem K.ZlibNg.Inflate.callZalloc (f : FnPtr) (opq : BPtr) (size : UInt32) : Keep (callZalloc f opq 1 size) := by
  unfold _root_.ZlibNg.Inflate.callZalloc
  split
  · unfold ZlibNg.Zutil.zcalloc
    refine keep_allocB _ ?_
    have := size.toNat_lt
    have e1 : ((1 : UInt32).toUInt64 * size.toUInt64).toNat = size.toNat := by simp
    rw [e1]; omega
  · exact keep_ub _
  · exact keep_ub _

theorem K.C.cutBytes (b off : Nat) : Keep (cutBytes b off) := ⟨fun h r h' e => by
  unfold _root_.C.cutBytes at e
  split at e
  · rename_i a hb
    cases e
    exact kr_bytes hb (by simp; omega) rfl rfl rfl rfl rfl rfl rfl
  · cases e⟩

theorem keep_self : Keep ((fun h => .ok (h, h)) : M Heap) := ⟨fun h r h' e => by cases e; exact KR.refl _⟩

/-! ## Carves -/

theorem carveCheck_ok {p : BPtr} {size align : Nat} {h h1 : Heap} {b : Nat}
    (e : carveCheck p size align h = .ok (b, h1)) :
    h1 = h ∧ ∃ off a, p = .ref (.heap b) off ∧ h.bytes b = some a := by
  unfold _root_.C.carveCheck at e
  split at e
  · rename_i b' off
    split at e
    · rename_i a ha
      split at e
      · split at e
        · cases e; exact ⟨rfl, off, a, rfl, ha⟩
        · cases e
      · cases e
    · cases e
  · cases e

theorem K.C.carveState (p : BPtr) : Keep (carveState p) := ⟨fun h r h' e => by
  unfold _root_.C.carveState at e
  simp only [bind_app] at e
  rcases hc : _root_.C.carveCheck p SIZEOF_INFLATE_STATE ALIGNOF_INFLATE_STATE h with _ | ⟨b, h1⟩
  · rw [hc] at e; cases e
  · obtain ⟨rfl, off, a, rfl, ha⟩ := carveCheck_ok hc
    rw [hc] at e
    simp only [Bind.bind] at e
    by_cases hst : (h1.istates.get b).isSome = true
    · simp [hst, ub] at e
    · simp only [hst, Bool.false_eq_true, ↓reduceIte] at e
      simp only [_root_.C.cutBytes, ha] at e
      cases e
      refine (kr_bytes (h' := { h1 with bytes := upd h1.bytes b (some (a.extract 0 off)) }) (a' := a.extract 0 off)
        ha (by simp; omega) rfl rfl rfl rfl rfl rfl rfl).trans ?_
      exact kr_obj (b := b) (a := a.extract 0 off) (by simp) rfl rfl (fun c hc => upd_ne _ _ _ _ hc)
        (fun _ _ => rfl) rfl rfl rfl⟩

theorem K.C.carveAllocs (p : BPtr) : Keep (carveAllocs p) := ⟨fun h r h' e => by
  unfold _root_.C.carveAllocs at e
  simp only [bind_app] at e
  rcases hc : _root_.C.carveCheck p SIZEOF_INFLATE_ALLOCS ALIGNOF_INFLATE_ALLOCS h with _ | ⟨b, h1⟩
  · rw [hc] at e; cases e
  · obtain ⟨rfl, off, a, rfl, ha⟩ := carveCheck_ok hc
    rw [hc] at e
    simp only [Bind.bind] at e
    by_cases hst : (h1.iallocs.get b).isSome = true
    · simp [hst, ub] at e
    · simp only [hst, Bool.false_eq_true, ↓reduceIte] at e
      simp only [_root_.C.cutBytes, ha] at e
      cases e
      refine (kr_bytes (h' := { h1 with bytes := upd h1.bytes b (some (a.extract 0 off)) }) (a' := a.extract 0 off)
        ha (by simp; omega) rfl rfl rfl rfl rfl rfl rfl).trans ?_
      exact kr_obj (b := b) (a := a.extract 0 off) (by simp) rfl rfl (fun _ _ => rfl)
        (fun c hc => upd_ne _ _ _ _ hc) rfl rfl rfl⟩

/-! ## Stores through a `Space` -/

/-- Replacing an array of a `Space` by one of the same size keeps `KR`. -/
class SpaceKeep (R T : Type) [Space Heap R T] : Prop where
  put : ∀ (h : Heap) (r : R) (a a' : Array T), Space.get h r = some a → Space.ro h r = false → a'.size = a.size →
    KR h (Space.put h r a')

instance : SpaceKeep BRef UInt8 where
  put h r a a' hg hro hs := by
    cases r with
    | heap b => exact kr_bytes (a := a) hg (by omega) rfl rfl rfl rfl rfl rfl rfl
    | const _ => simp [Space.ro, Heap.isRo] at hro
    | str _ => simp [Space.ro, Heap.isRo] at hro

theorem bytes_of_istate {h : Heap} {b : Nat} {s : InflateState} (hs : h.istate b = some s) :
    ∃ a, h.bytes b = some a := by
  simp only [Heap.istate] at hs
  split at hs
  · rename_i a hb; exact ⟨a, hb⟩
  · cases hs

instance : SpaceKeep CodeRef Code where
  put h r a a' hg hro hs := by
    cases r with
    | codes b =>
      simp only [Space.get, Heap.getCodes] at hg
      cases hst : h.istate b with
      | none => rw [hst] at hg; cases hg
      | some s =>
        obtain ⟨d, hd⟩ := bytes_of_istate hst
        simp only [Space.put, Heap.putCodes]
        split
        · exact kr_obj hd rfl rfl (fun c hc => upd_ne _ _ _ _ hc) (fun _ _ => rfl) rfl rfl rfl
        · exact KR.refl _
    | lenfix => simp [Space.ro, Heap.roCodes] at hro
    | distfix => simp [Space.ro, Heap.roCodes] at hro

instance : SpaceKeep WRef UInt16 where
  put h r a a' hg hro hs := by
    cases r with
    | lens b =>
      simp only [Space.get, Heap.getWords] at hg
      cases hst : h.istate b with
      | none => rw [hst] at hg; cases hg
      | some s =>
        obtain ⟨d, hd⟩ := bytes_of_istate hst
        simp only [Space.put, Heap.putWords]
        split
        · exact kr_obj hd rfl rfl (fun c hc => upd_ne _ _ _ _ hc) (fun _ _ => rfl) rfl rfl rfl
        · exact KR.refl _
    | work b =>
      simp only [Space.get, Heap.getWords] at hg
      cases hst : h.istate b with
      | none => rw [hst] at hg; cases hg
      | some s =>
        obtain ⟨d, hd⟩ := bytes_of_istate hst
        simp only [Space.put, Heap.putWords]
        split
        · exact kr_obj hd rfl rfl (fun c hc => upd_ne _ _ _ _ hc) (fun _ _ => rfl) rfl rfl rfl
        · exact KR.refl _

instance : SpaceKeep URef UInt32 where
  put h r a a' hg hro hs := by simp [Space.ro, Heap.isRoU32] at hro

theorem forIn_size {β : Type} (f : Nat → Array β → Array β) (hf : ∀ i b, (f i b).size = b.size) :
    ∀ (l : List Nat) (a : Array β),
      (forIn (m := Id) l a (fun i r => ForInStep.yield (f i r))).run.size = a.size := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons x l ih => intro a; simp only [List.forIn_cons]; exact (ih _).trans (hf _ _)

theorem loop_size {β : Type} (a : Array β) (n : Nat) (f : Nat → Array β → Array β)
    (hf : ∀ i b, (f i b).size = b.size) :
    (Id.run do
      let mut out := a
      for i in [0:n] do
        out := f i out
      return out).size = a.size := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  exact forIn_size f hf _ a

section generic
variable {R T : Type} [Space Heap R T] [SpaceKeep R T]

theorem kr_modify {h : Heap} {r : R} {a : Array T} (hg : Space.get h r = some a) (hro : Space.ro h r = false)
    (f : Array T → Array T) (hs : (f a).size = a.size) : KR h (Space.modify h r f) := by
  rw [Space.modify_eq h r a f hg hro]
  exact SpaceKeep.put h r a (f a) hg hro hs

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
          exact kr_modify hg (by simpa using hro) _ (by simp)
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
          exact kr_modify hg (by simpa using hro) _
            (loop_size a n (fun i out => out.set! (_ + i) byte) (fun _ _ => by simp))
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
            exact kr_modify hg (by simpa using hro) _
              (loop_size a n (fun i out => out.set! (_ + i) as_[_ + i]!) (fun _ _ => by simp))
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
          exact kr_modify hg (by simpa using hro) _
            (loop_size a n (fun i out => out.set! (_ + i) as_[_ + i]!) (fun _ _ => by simp))
        · cases e
    · cases e⟩

/-! ## `for` loops -/

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

/-! ## The decomposition tactic -/

open Lean Meta Elab Tactic in
/-- One step of `keep_tac` on the main goal: close it by a hypothesis, introduce a binder, or decompose a `Keep` /
`KeepX` goal by the head of its computation (bind, pure, `have`, a join point, `if` / `match`, a `for` loop, a
primitive's `K.` lemma, or the definition). -/
def keepStep : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let t ← whnf (← instantiateMVars (← g.getType))
    if t.isForall then
      let (_, g') ← g.intro1
      replaceMainGoal [g']
      return
    let fn := t.getAppFn
    let isM := fn.isConstOf ``Keep
    let isX := fn.isConstOf ``KeepX
    unless isM || isX do throwError "keep_step: unexpected goal {t}"
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
        let lem := if isM then ``keep_have else ``keepX_have
        let pf ← mkAppOptM lem #[ty, none, none, v, f]
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
          if (dt.isAppOf ``KeepX) && dt.appArg!.consumeMData == hd && e.getAppNumArgs == 1 then
            let pf ← mkAppM ``KeepX.run #[mkFVar d.fvarId, e.appArg!]
            g.assign pf
            replaceMainGoal []
            return
        throwError "keep_step: no KeepF hypothesis for {hd}"
      if hd.isProj || hd.isConstOf ``ForIn.forIn then
        try applyC ``keep_forIn_array
        catch _ =>
          try applyC ``keep_forIn_list
          catch _ => applyC ``keep_forIn_range
        return
      let some n := hd.constName? | throwError "keep_step: head {hd}"
      if n == ``Bind.bind then applyC (if isM then ``keep_bind else ``keepX_bind)
      else if n == ``Pure.pure then applyC (if isM then ``keep_pure else ``keepX_pure)
      else if n == ``C.ub then applyC ``keep_ub
      else if n == ``ite then applyC (if isM then ``keep_ite else ``keepX_ite)
      else if n == ``dite then applyC (if isM then ``keep_dite else ``keepX_dite)
      else if (← isMatcher n) then
        replaceMainGoal [g]
        evalTactic (← `(tactic| split))
      else
        let k := `ZlibNgF.Proof.InflateKeep.K ++ n
        if (← getEnv).contains k && (← Term.getDeclName?) != some k then applyC k
        else
          let g' ← unfoldTarget g n
          replaceMainGoal [g']

open Lean Elab Tactic in
elab "keep_step" : tactic => keepStep

open Lean Meta Elab Tactic in
/-- Decompose `Keep` / `KeepX` goals down to the primitives, goal by goal; a side condition of a primitive is closed
by `decide` or left as a goal. -/
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
        let ok2 ← try evalTactic (← `(tactic| decide)); pure true catch _ => pure false
        todo := rest
        unless ok2 do stuck := stuck ++ [g]
  setGoals (stuck ++ todo)

/-! ## Loops of `X` -/

theorem K.ZlibNg.Inflate.xwhileBrk {cond body : X Bool} (hc : KeepX cond) (hb : KeepX body) :
    KeepX (xwhileBrk cond body) := ⟨fun l => by
  unfold _root_.ZlibNg.Inflate.xwhileBrk
  simp only [_root_.ExceptT.run, _root_.ExceptT.mk, _root_.StateT.run]
  keep_tac
  all_goals first | exact hc.run _ | exact hb.run _⟩

/-! ## Every inflate-side function of the translation

Each lemma is the decomposition of the function down to the lemmas above (`keep_tac`); a callee with a lemma of its own
is not unfolded again. -/

section translation
open ZlibNg.Zbuild ZlibNg.InflateP ZlibNg.Chunkset ZlibNg.Inffast ZlibNg.Inftrees ZlibNg.Infback
open ZlibNg.Crc32Braid ZlibNg.Adler32C

theorem K.ZlibNg.Zbuild.ALIGN_DIFF (ptr : BPtr) (align : UInt64) :
    Keep (_root_.ZlibNg.Zbuild.ALIGN_DIFF ptr align) := by keep_tac
theorem K.ZlibNg.Zutil.zError (err : Int32) :
    Keep (_root_.ZlibNg.Zutil.zError err) := by keep_tac
theorem K.ZlibNg.Zutil.zcfree («opaque» ptr : BPtr) :
    Keep (_root_.ZlibNg.Zutil.zcfree «opaque» ptr) := by keep_tac
theorem K.ZlibNg.Zutil.ALIGN_DIFF (ptr : BPtr) (align : UInt32) :
    Keep (_root_.ZlibNg.Zutil.ALIGN_DIFF ptr align) := by keep_tac
theorem K.ZlibNg.Zutil.zng_free_aligned (ptr : BPtr) :
    Keep (_root_.ZlibNg.Zutil.zng_free_aligned ptr) := by keep_tac
theorem K.ZlibNg.Adler32P.loadU64 (p : BPtr) (i : Nat) :
    Keep (_root_.ZlibNg.Adler32P.loadU64 p i) := by keep_tac
theorem K.ZlibNg.Adler32P.storeU64 (dst : BPtr) (v : UInt64) :
    Keep (_root_.ZlibNg.Adler32P.storeU64 dst v) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do1 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do1 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do2 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do2 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.adler_do4 (adler sum2 : UInt32) (buf : BPtr) (i : Int) :
    Keep (_root_.ZlibNg.Adler32P.adler_do4 adler sum2 buf i) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_copy_align (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (_MAX_LEN : Int32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_copy_align adler dst buf len sum2 _MAX_LEN COPY) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_swar (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_swar adler dst buf len sum2 COPY) := by keep_tac
theorem K.ZlibNg.Adler32P.adler32_copy_tail (adler : UInt32) (dst : BPtr) (buf : BPtr) (len : UInt64)
    (sum2 : UInt32) (REBASE : Int32) (_MAX_LEN : Int32) (COPY : Int32) :
    Keep (_root_.ZlibNg.Adler32P.adler32_copy_tail adler dst buf len sum2 REBASE _MAX_LEN COPY) := by keep_tac
theorem K.ZlibNg.Adler32C.adler32_c (adler : UInt32) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Adler32C.adler32_c adler buf len) := by keep_tac
theorem K.ZlibNg.Adler32C.adler32_copy_c (adler : UInt32) (dst : BPtr) (src : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Adler32C.adler32_copy_c adler dst src len) := by keep_tac
theorem K.ZlibNg.Adler32.adler32_z (adler : UInt64) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Adler32.adler32_z adler buf len) := by keep_tac
theorem K.ZlibNg.Adler32.adler32 (adler : UInt64) (buf : BPtr) (len : UInt32) :
    Keep (_root_.ZlibNg.Adler32.adler32 adler buf len) := by keep_tac
theorem K.ZlibNg.Adler32.adler32_combine_ (adler1 adler2 : UInt32) (len2 : Int64) :
    Keep (_root_.ZlibNg.Adler32.adler32_combine_ adler1 adler2 len2) := by keep_tac
theorem K.ZlibNg.Adler32.adler32_combine (adler1 adler2 : UInt64) (len2 : Int64) :
    Keep (_root_.ZlibNg.Adler32.adler32_combine adler1 adler2 len2) := by keep_tac
theorem K.ZlibNg.Adler32.adler32_combine64 (adler1 adler2 : UInt64) (len2 : Int64) :
    Keep (_root_.ZlibNg.Adler32.adler32_combine64 adler1 adler2 len2) := by keep_tac
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
theorem K.ZlibNg.Crc32CombP.x2nTab (i : UInt32) :
    Keep (_root_.ZlibNg.Crc32CombP.x2nTab i) := by keep_tac
theorem K.ZlibNg.Crc32CombP.multmodp (a b : UInt32) :
    Keep (_root_.ZlibNg.Crc32CombP.multmodp a b) := by keep_tac
theorem K.ZlibNg.Crc32CombP.x2nmodp (n : Int64) (k : UInt32) :
    Keep (_root_.ZlibNg.Crc32CombP.x2nmodp n k) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_ (crc1 crc2 : UInt32) (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_ crc1 crc2 len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_gen_ (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_gen_ len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_op_ (crc1 crc2 op : UInt32) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_op_ crc1 crc2 op) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine (crc1 crc2 : UInt64) (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine crc1 crc2 len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine64 (crc1 crc2 : UInt64) (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine64 crc1 crc2 len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_gen (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_gen len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_gen64 (len2 : Int64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_gen64 len2) := by keep_tac
theorem K.ZlibNg.Crc32Comb.crc32_combine_op (crc1 crc2 op : UInt64) :
    Keep (_root_.ZlibNg.Crc32Comb.crc32_combine_op crc1 crc2 op) := by keep_tac
theorem K.ZlibNg.Crc32.crc32_small (crc : UInt32) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Crc32.crc32_small crc buf len) := by keep_tac
theorem K.ZlibNg.Crc32.crc32_z (crc : UInt64) (buf : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Crc32.crc32_z crc buf len) := by keep_tac
theorem K.ZlibNg.Crc32.crc32 (crc : UInt64) (buf : BPtr) (len : UInt32) :
    Keep (_root_.ZlibNg.Crc32.crc32 crc buf len) := by keep_tac
theorem K.ZlibNg.Chunkset.chunkmemset_4 (from_ : BPtr) :
    Keep (_root_.ZlibNg.Chunkset.chunkmemset_4 from_) := by keep_tac
theorem K.ZlibNg.Chunkset.chunkmemset_8 (from_ : BPtr) :
    Keep (_root_.ZlibNg.Chunkset.chunkmemset_8 from_) := by keep_tac
theorem K.ZlibNg.Chunkset.loadchunk (s : BPtr) :
    Keep (_root_.ZlibNg.Chunkset.loadchunk s) := by keep_tac
theorem K.ZlibNg.Chunkset.storechunk (out : BPtr) (chunk : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.storechunk out chunk) := by keep_tac
theorem K.ZlibNg.Chunkset.CHUNKCOPY (out from_ : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.CHUNKCOPY out from_ len) := by keep_tac
theorem K.ZlibNg.Chunkset.CHUNKUNROLL (out : BPtr) (dist len : UInt32) :
    Keep (_root_.ZlibNg.Chunkset.CHUNKUNROLL out dist len) := by keep_tac
theorem K.ZlibNg.Chunkset.GET_CHUNK_MAG (buf : BPtr) (chunk_rem dist : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.GET_CHUNK_MAG buf chunk_rem dist) := by keep_tac
theorem K.ZlibNg.Chunkset.storeChunkBytes (out : BPtr) (chunk : UInt64) (start n : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.storeChunkBytes out chunk start n) := by keep_tac
theorem K.ZlibNg.Chunkset.CHUNKMEMSET (out from_ : BPtr) (len : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.CHUNKMEMSET out from_ len) := by keep_tac
theorem K.ZlibNg.Chunkset.CHUNKMEMSET_SAFE (out from_ : BPtr) (len left : UInt64) :
    Keep (_root_.ZlibNg.Chunkset.CHUNKMEMSET_SAFE out from_ len left) := by keep_tac
theorem K.ZlibNg.Chunkset.CHUNKCOPY_SAFE (out from_ : BPtr) (len : UInt64) (safe : BPtr) :
    Keep (_root_.ZlibNg.Chunkset.CHUNKCOPY_SAFE out from_ len safe) := by keep_tac
theorem K.ZlibNg.InflateP.EXTRA_BITS (old : UInt64) (here : Code) (op : UInt32) :
    Keep (_root_.ZlibNg.InflateP.EXTRA_BITS old here op) := by keep_tac
theorem K.ZlibNg.InflateP.load_64_bits (in_ : BPtr) (bits : UInt32) :
    Keep (_root_.ZlibNg.InflateP.load_64_bits in_ bits) := by keep_tac
theorem K.ZlibNg.InflateP.chunkcopy_safe (out from_ : BPtr) (len : UInt64) (safe : BPtr) :
    Keep (_root_.ZlibNg.InflateP.chunkcopy_safe out from_ len safe) := by keep_tac
theorem K.ZlibNg.Inffast.REFILL (l : FL) :
    Keep (_root_.ZlibNg.Inffast.REFILL l) := by keep_tac
theorem K.ZlibNg.Inffast.DROPBITS (l : FL) (n : UInt32) :
    Keep (_root_.ZlibNg.Inffast.DROPBITS l n) := by keep_tac
theorem K.ZlibNg.Inffast.BITS (l : FL) (n : UInt32) :
    Keep (_root_.ZlibNg.Inffast.BITS l n) := by keep_tac
theorem K.ZlibNg.Inffast.SET_BAD (c : FC) (msg : String) :
    Keep (_root_.ZlibNg.Inffast.SET_BAD c msg) := by keep_tac
theorem K.ZlibNg.Inffast.putLit (l : FL) :
    Keep (_root_.ZlibNg.Inffast.putLit l) := by keep_tac
theorem K.ZlibNg.Inffast.lookupLen (c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.lookupLen c l) := by keep_tac
theorem K.ZlibNg.Inffast.stepTop (c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.stepTop c l) := by keep_tac
theorem K.ZlibNg.Inffast.stepDolen (_c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.stepDolen _c l) := by keep_tac
theorem K.ZlibNg.Inffast.stepCommon (c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.stepCommon c l) := by keep_tac
theorem K.ZlibNg.Inffast.stepDodist (c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.stepDodist c l) := by keep_tac
theorem K.ZlibNg.Inffast.trip (c : FC) (l : FL) :
    Keep (_root_.ZlibNg.Inffast.trip c l) := by keep_tac
theorem K.ZlibNg.Inffast.INFLATE_FAST (safeMode : Bool) (strm : StreamPtr) (start : UInt32) :
    Keep (_root_.ZlibNg.Inffast.INFLATE_FAST safeMode strm start) := by keep_tac
theorem K.ZlibNg.ChunksetC.chunkmemset_safe_c (out from_ : BPtr) (len left : UInt64) :
    Keep (_root_.ZlibNg.ChunksetC.chunkmemset_safe_c out from_ len left) := by keep_tac
theorem K.ZlibNg.ChunksetC.inflate_fast_c (strm : StreamPtr) (start : UInt32) :
    Keep (_root_.ZlibNg.ChunksetC.inflate_fast_c strm start) := by keep_tac
theorem K.ZlibNg.ChunksetC.inflate_fast_safe_c (strm : StreamPtr) (start : UInt32) :
    Keep (_root_.ZlibNg.ChunksetC.inflate_fast_safe_c strm start) := by keep_tac
theorem K.ZlibNg.Inftrees.aget {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    Keep (_root_.ZlibNg.Inftrees.aget a i) := by keep_tac
theorem K.ZlibNg.Inftrees.aset {α : Type} (a : Array α) (i : Nat) (v : α) :
    Keep (_root_.ZlibNg.Inftrees.aset a i v) := by keep_tac
theorem K.ZlibNg.Inftrees.oneRow (k : UInt16) :
    Keep (_root_.ZlibNg.Inftrees.oneRow k) := by keep_tac
theorem K.ZlibNg.Inftrees.count_lengths (lens : WPtr) (codes : Int32) :
    Keep (_root_.ZlibNg.Inftrees.count_lengths lens codes) := by keep_tac
theorem K.ZlibNg.Inftrees.U16Src.at (s : U16Src) (i : Nat) :
    Keep (_root_.ZlibNg.Inftrees.U16Src.at s i) := by keep_tac
theorem K.ZlibNg.Inftrees.stCode (p : CodePtr) (i : Int) (c : Code) :
    Keep (_root_.ZlibNg.Inftrees.stCode p i c) := by keep_tac
theorem K.ZlibNg.Inftrees.zng_inflate_table (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr)
    (bits : UInt32) (work : WPtr) :
    Keep (_root_.ZlibNg.Inftrees.zng_inflate_table type lens codes table bits work) := by keep_tac
theorem K.ZlibNg.Inflate.rdS {α : Type} (st : StatePtr) (f : InflateState → α) :
    Keep (_root_.ZlibNg.Inflate.rdS st f) := by keep_tac
theorem K.ZlibNg.Inflate.wrS (st : StatePtr) (f : InflateState → InflateState) :
    Keep (_root_.ZlibNg.Inflate.wrS st f) := by keep_tac
theorem K.ZlibNg.Inflate.rdZ {α : Type} (strm : StreamPtr) (f : ZStream → α) :
    Keep (_root_.ZlibNg.Inflate.rdZ strm f) := by keep_tac
theorem K.ZlibNg.Inflate.wrZ (strm : StreamPtr) (f : ZStream → ZStream) :
    Keep (_root_.ZlibNg.Inflate.wrZ strm f) := by keep_tac
theorem K.ZlibNg.Inflate.lensP (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.lensP st) := by keep_tac
theorem K.ZlibNg.Inflate.workP (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.workP st) := by keep_tac
theorem K.ZlibNg.Inflate.codesP (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.codesP st) := by keep_tac
theorem K.ZlibNg.Inflate.callZfree (f : FnPtr) (opq ptr : BPtr) :
    Keep (_root_.ZlibNg.Inflate.callZfree f opq ptr) := by keep_tac
theorem K.ZlibNg.Inflate.stateOf (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.stateOf strm) := by keep_tac
theorem K.ZlibNg.Inflate.inf_chksum_cpy (strm : StreamPtr) (dst src : BPtr) (copy : UInt32) :
    Keep (_root_.ZlibNg.Inflate.inf_chksum_cpy strm dst src copy) := by keep_tac
theorem K.ZlibNg.Inflate.inf_chksum (strm : StreamPtr) (src : BPtr) (len : UInt32) :
    Keep (_root_.ZlibNg.Inflate.inf_chksum strm src len) := by keep_tac
theorem K.ZlibNg.Inflate.inflateStateCheck (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateStateCheck strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateResetKeep (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateResetKeep strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateReset (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateReset strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateReset2 (strm : StreamPtr) (windowBits : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateReset2 strm windowBits) := by keep_tac
theorem K.ZlibNg.Inflate.HINT_ALIGNED_64 (p : BPtr) :
    Keep (_root_.ZlibNg.Inflate.HINT_ALIGNED_64 p) := by keep_tac
theorem K.ZlibNg.Inflate.alloc_inflate (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.alloc_inflate strm) := by keep_tac
theorem K.ZlibNg.Inflate.free_inflate (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.free_inflate strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateInit2 (strm : StreamPtr) (windowBits : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateInit2 strm windowBits) := by keep_tac
theorem K.ZlibNg.Inflate.CHECK_VER_STSIZE (version : BPtr) (stream_size : Int32) :
    Keep (_root_.ZlibNg.Inflate.CHECK_VER_STSIZE version stream_size) := by keep_tac
theorem K.ZlibNg.Inflate.inflateInit_ (strm : StreamPtr) (version : BPtr) (stream_size : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateInit_ strm version stream_size) := by keep_tac
theorem K.ZlibNg.Inflate.inflateInit2_ (strm : StreamPtr) (windowBits : Int32) (version : BPtr) (stream_size : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateInit2_ strm windowBits version stream_size) := by keep_tac
theorem K.ZlibNg.Inflate.inflatePrime (strm : StreamPtr) (bits : Int32) (value : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflatePrime strm bits value) := by keep_tac
theorem K.ZlibNg.Inflate.fixedtables (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.fixedtables st) := by keep_tac
theorem K.ZlibNg.Inflate.updatewindow (strm : StreamPtr) (end_ : BPtr) (len : UInt32) (cksum : Int32) :
    Keep (_root_.ZlibNg.Inflate.updatewindow strm end_ len cksum) := by keep_tac
theorem K.ZlibNg.Inflate.LOAD (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.LOAD c) := by keep_tac
theorem K.ZlibNg.Inflate.RESTORE (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.RESTORE c) := by keep_tac
theorem K.ZlibNg.Inflate.INITBITS  :
    KeepX (_root_.ZlibNg.Inflate.INITBITS) := by keep_tac
theorem K.ZlibNg.Inflate.PULLBYTE  :
    KeepX (_root_.ZlibNg.Inflate.PULLBYTE) := by keep_tac
theorem K.ZlibNg.Inflate.NEEDBITS (n : UInt32) :
    KeepX (_root_.ZlibNg.Inflate.NEEDBITS n) := by keep_tac
theorem K.ZlibNg.Inflate.BITS (n : UInt32) :
    KeepX (_root_.ZlibNg.Inflate.BITS n) := by keep_tac
theorem K.ZlibNg.Inflate.DROPBITS (n : UInt32) :
    KeepX (_root_.ZlibNg.Inflate.DROPBITS n) := by keep_tac
theorem K.ZlibNg.Inflate.BYTEBITS  :
    KeepX (_root_.ZlibNg.Inflate.BYTEBITS) := by keep_tac
theorem K.ZlibNg.Inflate.SET_BAD (c : Ctx) (msg : String) :
    Keep (_root_.ZlibNg.Inflate.SET_BAD c msg) := by keep_tac
theorem K.ZlibNg.Inflate.CRC_DO1_B (c : UInt32) (b : UInt64) :
    Keep (_root_.ZlibNg.Inflate.CRC_DO1_B c b) := by keep_tac
theorem K.ZlibNg.Inflate.CRC2 (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.CRC2 c) := by keep_tac
theorem K.ZlibNg.Inflate.CRC4 (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.CRC4 c) := by keep_tac
theorem K.ZlibNg.Inflate.hcrcOn (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.hcrcOn st) := by keep_tac
theorem K.ZlibNg.Inflate.setMode (st : StatePtr) (m : UInt32) :
    Keep (_root_.ZlibNg.Inflate.setMode st m) := by keep_tac
theorem K.ZlibNg.Inflate.headOf (st : StatePtr) :
    Keep (_root_.ZlibNg.Inflate.headOf st) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_DONE (_c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_DONE _c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LENGTH (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LENGTH c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_CHECK (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_CHECK c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LIT (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LIT c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_MATCH (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_MATCH c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_DISTEXT (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_DISTEXT c) := by keep_tac
theorem K.ZlibNg.Inflate.decodeSym (c : Ctx) (tab : CodePtr) (nbits : UInt32) (first : Code → Bool) :
    KeepX (_root_.ZlibNg.Inflate.decodeSym c tab nbits first) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_DIST (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_DIST c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LENEXT (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LENEXT c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LEN (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LEN c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LEN_ (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LEN_ c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_CODELENS (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_CODELENS c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_LENLENS (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_LENLENS c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_TABLE (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_TABLE c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_COPY (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_COPY c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_COPY_ (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_COPY_ c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_STORED (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_STORED c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_TYPEDO (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_TYPEDO c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_TYPE (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_TYPE c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_DICT (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_DICT c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_DICTID (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_DICTID c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_HCRC (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_HCRC c) := by keep_tac
theorem K.ZlibNg.Inflate.headerString (c : Ctx) (field : GzHeader → BPtr) (maxOf : GzHeader → UInt32) :
    KeepX (_root_.ZlibNg.Inflate.headerString c field maxOf) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_COMMENT (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_COMMENT c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_NAME (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_NAME c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_EXTRA (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_EXTRA c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_EXLEN (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_EXLEN c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_OS (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_OS c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_TIME (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_TIME c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_FLAGS (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_FLAGS c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_HEAD (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_HEAD c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate_BAD (_c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.inflate_BAD _c) := by keep_tac
theorem K.ZlibNg.Inflate.dispatch (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.dispatch c) := by keep_tac
theorem K.ZlibNg.Inflate.infLeave (c : Ctx) :
    KeepX (_root_.ZlibNg.Inflate.infLeave c) := by keep_tac
theorem K.ZlibNg.Inflate.inflate (strm : StreamPtr) (flush : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflate strm flush) := by keep_tac
theorem K.ZlibNg.Inflate.inflateEnd (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateEnd strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateGetDictionary (strm : StreamPtr) (dictionary : BPtr) (hasLen : Bool) :
    Keep (_root_.ZlibNg.Inflate.inflateGetDictionary strm dictionary hasLen) := by keep_tac
theorem K.ZlibNg.Inflate.inflateSetDictionary (strm : StreamPtr) (dictionary : BPtr) (dictLength : UInt32) :
    Keep (_root_.ZlibNg.Inflate.inflateSetDictionary strm dictionary dictLength) := by keep_tac
theorem K.ZlibNg.Inflate.inflateGetHeader (strm : StreamPtr) (head : HeaderPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateGetHeader strm head) := by keep_tac
theorem K.ZlibNg.Inflate.syncsearch (have_ : UInt32) (buf : BPtr) (len : UInt32) :
    Keep (_root_.ZlibNg.Inflate.syncsearch have_ buf len) := by keep_tac
theorem K.ZlibNg.Inflate.inflateSync (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateSync strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateSyncPoint (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateSyncPoint strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateCopy (dest source : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateCopy dest source) := by keep_tac
theorem K.ZlibNg.Inflate.inflateUndermine (_strm : StreamPtr) (_subvert : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateUndermine _strm _subvert) := by keep_tac
theorem K.ZlibNg.Inflate.inflateValidate (strm : StreamPtr) (check : Int32) :
    Keep (_root_.ZlibNg.Inflate.inflateValidate strm check) := by keep_tac
theorem K.ZlibNg.Inflate.inflateMark (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateMark strm) := by keep_tac
theorem K.ZlibNg.Inflate.inflateCodesUsed (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Inflate.inflateCodesUsed strm) := by keep_tac
theorem K.ZlibNg.Infback.inflateBackInit (strm : StreamPtr) (windowBits : Int32) (window : BPtr) :
    Keep (_root_.ZlibNg.Infback.inflateBackInit strm windowBits window) := by keep_tac
theorem K.ZlibNg.Infback.inflateBackInit_ (strm : StreamPtr) (windowBits : Int32) (window : BPtr)
    (version : BPtr) (stream_size : Int32) :
    Keep (_root_.ZlibNg.Infback.inflateBackInit_ strm windowBits window version stream_size) := by keep_tac
theorem K.ZlibNg.Infback.inflateBackEnd (strm : StreamPtr) :
    Keep (_root_.ZlibNg.Infback.inflateBackEnd strm) := by keep_tac
theorem K.ZlibNg.Uncompr.uncompress2_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr)
    (sourceLen : Option UInt64) :
    Keep (_root_.ZlibNg.Uncompr.uncompress2_z dest destLen source sourceLen) := by keep_tac
theorem K.ZlibNg.Uncompr.uncompress2 (dest : BPtr) (destLen : Option UInt64) (source : BPtr)
    (sourceLen : Option UInt64) :
    Keep (_root_.ZlibNg.Uncompr.uncompress2 dest destLen source sourceLen) := by keep_tac
theorem K.ZlibNg.Uncompr.uncompress (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    Keep (_root_.ZlibNg.Uncompr.uncompress dest destLen source sourceLen) := by keep_tac
theorem K.ZlibNg.Uncompr.uncompress_z (dest : BPtr) (destLen : Option UInt64) (source : BPtr) (sourceLen : UInt64) :
    Keep (_root_.ZlibNg.Uncompr.uncompress_z dest destLen source sourceLen) := by keep_tac


end translation

/-! ## Frames -/

/-- A call that keeps `KR` and has the frame `Frame` has the frame `IFrame`. -/
theorem iframe_up {α : Type} {m : M α} {h : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (hk : Keep m)
    (p : ∃ r h', C.run m h = .ok (r, h') ∧ Frame h h' S B G W) :
    ∃ r h', C.run m h = .ok (r, h') ∧ IFrame h h' S B G W := by
  obtain ⟨r, h', e, f⟩ := p
  exact ⟨r, h', e, f, (hk.run _ _ _ e).ds, (hk.run _ _ _ e).da⟩

end ZlibNgF.Proof.InflateKeep
