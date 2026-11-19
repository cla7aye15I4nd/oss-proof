import ZlibNgF.Proof.«infback.c.pull»
import ZlibNgF.Proof.«inflate.c.table-modes»

/-!
# `inflateBack`: the call-back macro `ROOM` (`ZlibNgF`)

`ROOM()` with a full window stores `state->whave` and calls `out()` on the whole window. The store changes only the
library's state, so the caller's invariant `I` survives it (`BackCallbacks.stable`); `out()` keeps what `BackKeep`
names and `I` of the current chunk.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackRoom
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS istates_of istate_withS wrS_app ldState_withS rdS_withS)

/-- A store of the state record `b` is in the frame of the library. -/
theorem frame_withS (H : Heap) (i b : Nat) (S : InflateState) (W : List (BPtr × Nat)) :
    Frame H (withS H b S) [i] [b] [] W := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun b' _ hb' => ⟨?_, rfl⟩, fun b' _ _ d hd => ⟨d, hd, rfl, fun _ _ _ => rfl⟩,
    fun _ _ _ hn => hn, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  show upd H.istates b (some S) b' = _
  rw [upd_ne _ _ _ _ (by simpa using hb')]

/-- `InB` reads only `have` and `next`. -/
theorem InB.locals {I : Heap → BPtr → Nat → Nat → Prop} {H : Heap} {l l' : IL} {t : Nat} (h : InB I H l t)
    (e1 : l'.have_ = l.have_) (e2 : l'.next = l.next) : InB I H l' t := by
  obtain ⟨p, m, hI, hle, hat⟩ := h
  exact ⟨p, m, hI, by rw [e1]; exact hle, fun h0 => by rw [e1, e2]; exact hat (by rw [← e1]; exact h0)⟩

/-- `InB` survives a change that keeps `I`. -/
theorem InB.heap {I : Heap → BPtr → Nat → Nat → Prop} {H H' : Heap} {l : IL} {t : Nat} (h : InB I H l t)
    (hI : ∀ p m, I H p m t → I H' p m t) : InB I H' l t := by
  obtain ⟨p, m, hI0, hle, hat⟩ := h
  exact ⟨p, m, hI _ _ hI0, hle, hat⟩

/-- `ROOM()`: with room left, nothing; otherwise `put = window`, `left = wsize`, `state->whave = left`, and one
`out()` call on the window, which either lets the decoder go on or ends the call (`ret = Z_BUF_ERROR`). -/
theorem room_ok {i b : Nat} {w : BPtr} {n : Nat} {inCb : InCb} {inDesc : BPtr} {outCb : OutCb} {outDesc : BPtr}
    {I : Heap → BPtr → Nat → Nat → Prop} (cb : BackCallbacks i b w n inCb inDesc outCb outDesc I) (c : BCtx)
    (hcO : c.outCb = outCb) (hcD : c.outDesc = outDesc) (hst : c.st = some b) {H : Heap} {l : IL} {t : Nat}
    {S : InflateState} (hS : H.istate b = some S) (hw : S.window = .val w) (hn : S.wsize.toNat = n)
    (hin : InB I H l t) {Q : Except Ex Unit → IL → Heap → Prop}
    (k1 : l.left ≠ 0 → Q (.ok ()) l H)
    (k2 : l.left = 0 → ∀ (r : Int32) H', BackKeep (withS H b { S with whave := S.wsize }) H' i b w →
      InB I H' { l with put := w, left := S.wsize } t →
      (r ≠ 0 → Q (.error .leave) { l with put := w, left := S.wsize, ret := Z_BUF_ERROR } H') ∧
      (r = 0 → Q (.ok ()) { l with put := w, left := S.wsize } H')) :
    SatX H l (ROOM c) Q := by
  unfold ROOM
  refine SatX.bind (SatX.get ?_)
  dsimp only
  by_cases h0 : l.left = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    rw [hst]
    have hrd : ∀ {α : Type} (g : InflateState → α), ZlibNg.Inflate.rdS (some b) g H = .ok (g S, H) := by
      intro α g; simp [ZlibNg.Inflate.rdS, bind_app, InflateInv.ldState_app hS]
    refine SatX.bind (liftEq (hrd _) ?_)
    dsimp only
    rw [hw]
    refine SatX.bind (liftEq rfl ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (liftEq (hrd _) ?_)
    refine SatX.bind (SatX.modify ?_)
    refine SatX.bind (SatX.get ?_)
    refine SatX.bind (SatX.lift (Sat.of_eq (wrS_app hS _) ?_))
    refine SatX.bind (SatX.get ?_)
    dsimp only
    obtain ⟨p, m, hI, -, -⟩ := id hin
    have hI1 : I (withS H b { S with whave := S.wsize }) p m t :=
      cb.stable H _ p m t hI (frame_withS H i b _ [(w, n)]) rfl
    obtain ⟨r, H2, e, hI2, hkeep⟩ := cb.output _ S.wsize p m t (Nat.le_of_eq hn) hI1
    refine SatX.bind (SatX.lift (Sat.of_eq (by rw [hcO, hcD]; exact e) ?_))
    dsimp only
    have hin2 : InB I H2 { l with put := w, left := S.wsize } t := by
      refine InB.heap (H := H) (InB.locals hin rfl rfl) ?_
      · intro p' m' hI'
        have hI1' : I (withS H b { S with whave := S.wsize }) p' m' t :=
          cb.stable H _ p' m' t hI' (frame_withS H i b _ [(w, n)]) rfl
        obtain ⟨r', H2', e', hI2', -⟩ := cb.output _ S.wsize p' m' t (Nat.le_of_eq hn) hI1'
        rw [e] at e'
        cases e'
        exact hI2'
    obtain ⟨kL, kO⟩ := k2 h0 r H2 hkeep hin2
    by_cases hr : r = 0
    · have hr' : (r != 0) = false := by simp [hr]
      simp only [hr', Bool.false_eq_true, ↓reduceIte]
      exact SatX.pure (kO hr)
    · have hr' : (r != 0) = true := by simpa using hr
      simp only [hr', ↓reduceIte]
      exact SatX.bind (SatX.modify (SatX.throw (kL hr)))
  · have h0' : (l.left == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte]
    exact SatX.pure (k1 h0)

end ZlibNgF.Proof.InfbackRoom
