import ZlibF.Proof.«inflate.c.meaning-trip-body»
import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.meaning-stop-short»

/-!
# inflate.c: why a trip of the mode loop leaves (zlib rows)

`TripMeaning` keeps the format meaning at a leave (`LoopMatches`) and drops its cause. The cause
is what `StopShort` needs: a leave for want of input holds bits that do not complete the field
its mode waits for (`LeaveShort`), so a trip that left that way has not read a whole valid stream
(`LoopMatches.starved_not_end`). `LeaveCause` names the causes: a code other than `Z_OK` in `ret`
(`DONE` sets `Z_STREAM_END`), a `Z_BLOCK` or `Z_TREES` stop, no output room at the start of the
trip, or no input with `LeaveShort`. `CauseAt` is the cause row of a group of modes, for every
trip from `LoopMatches` that leaves.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The cause of a leave from the trip start registers `l` to the leave registers `l'`, heap `h'`. -/
def LeaveCause (c : Ctx) (h' : Heap) (l l' : IL) : Prop :=
  l'.ret ≠ Z_OK ∨ c.flush = Z_BLOCK ∨ c.flush = Z_TREES ∨ l.left = 0 ∨
    (l'.have_ = 0 ∧ LeaveShort c h' l')

/-- Every trip from a state with `P` that leaves states its cause. -/
def CauseAt (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (P : InflateState → Prop) : Prop :=
  ∀ h l, CallSide c r l h → LoopMatches c f h l →
    (∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → P s) →
    ∀ l' h', runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h') → LeaveCause c h' l l'

theorem LeaveCause.of_step {c : Ctx} {h' : Heap} {l l' : IL}
    (step : (l'.have_ = 0 ∧ LeaveShort c h' l') ∨ c.flush = Z_TREES ∨ l.left = 0) :
    LeaveCause c h' l l' := by
  rcases step with s | s | s
  · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
  · exact Or.inr (Or.inr (Or.inl s))
  · exact Or.inr (Or.inr (Or.inr (Or.inl s)))

/-- A run that is equal to a known one ends the same way. -/
theorem same_leave {p : X Unit} {l l' l1 : IL} {h h' h1 : Heap} {result : Except Ex Unit}
    (run : runX p l h = .ok ((.error Ex.leave, l'), h')) (run1 : runX p l h = .ok ((result, l1), h1)) :
    result = .error Ex.leave ∧ l1 = l' ∧ h1 = h' := by
  have same := run1.symm.trans run
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  exact ⟨same.1.1, same.1.2, same.2⟩

/-- Stored blocks (`STORED`, `COPY_`, `COPY`). -/
theorem cause_stored (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) E.st E.hs
    (window_bounds j.good.inv.win)
  rcases mode zs s E.st E.hs with m | m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningBlock.stored_step loop E.strm E.hz (at_state (P := fun s => s.mode = STORED) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_STORED E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · exact LeaveCause.of_step cause
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_start_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY_) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY_start E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl s)))
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl s)))
    · rw [e] at e'; cases e'

/-- `TYPE`/`TYPEDO` before the last block. -/
theorem cause_type_open (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  obtain ⟨m, _⟩ := mode zs s E.st E.hs
  rcases m with m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.type_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPE E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inl s)
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.typedo_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPEDO E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact Or.inr (Or.inr (Or.inr (Or.inr s)))
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'

/-- `DONE`: `Z_STREAM_END` in `ret`. -/
theorem cause_done (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DONE) := by
  intro h l side _ mode l' h' run
  obtain ⟨zs, z, s, E, _⟩ := side.env
  have run1 := (inflate_dispatch_DONE E l (mode zs s E.st E.hs)).trans (inflate_DONE_run c l h)
  obtain ⟨_, rfl, rfl⟩ := same_leave run run1
  exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

end Zlib.Inflate.Proofs
