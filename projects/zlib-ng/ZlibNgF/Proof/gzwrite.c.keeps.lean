import ZlibNgF.Proof.«gzwrite.c.printf»
import ZlibNgF.Proof.«gzwrite.c.compdone»

/-!
# The write-side calls keep the invariant of a write handle (`ZlibNgF`)

With `gz_comp_spec`, the write-side calls keep `GzInvWS` (`KeepsW`) given `DeflateGz` only: `gzwrite`, `gzfwrite`,
`gzputc`, `gzputs` and `gzflush` in the step form of `GzWStep`; `gzprintf` and `gzvprintf` with a format string
outside the blocks of the file (`SPrintfO`, `SVprintfO`). `gwrite_steps_of` gives `GWriteSteps` from `DeflateGz` and
the steps not proved here: `gzsetparams`, and `gzprintf` / `gzvprintf` in the form of `SPrintf` / `SVprintf`, which
does not exclude a format string inside the file's own blocks.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

section Steps
variable (w : World) (h : Heap) (w' : World) (h' : Heap) (f : GzPtr)

/-- `gzprintf` with a format string outside the blocks of the file. -/
def SPrintfO : Prop := ∃ fmt r, CStr h fmt ∧ OutsideGz w h f fmt ∧ GzRun (gzprintf f fmt) w h r w' h'

/-- `gzvprintf` with a format string outside the blocks of the file. -/
def SVprintfO : Prop := ∃ fmt r, CStr h fmt ∧ OutsideGz w h f fmt ∧ GzRun (gzvprintf f fmt) w h r w' h'

end Steps

theorem keeps_of_call {α : Type} {m : G α} {w w' : World} {h h' : Heap} {b : Nat} {r : α}
    (hm : GSat w h m (CallPost w h b)) (e : GzRun m w h r w' h') : GzInvWS w' h' (some b) := by
  obtain ⟨r2, w2, h2, e2, q⟩ := hm.run
  obtain ⟨-, rfl, rfl⟩ := gdet e e2
  exact q.1

theorem gzwrite_keepsW (G : DeflateGz) : KeepsW SWrite := by
  intro w h w' h' f hv ⟨buf, len, r, hin, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzwrite_spec gz_comp_spec G hv hs buf len hin) e

theorem gzfwrite_keepsW (G : DeflateGz) : KeepsW SFwrite := by
  intro w h w' h' f hv ⟨buf, size, nitems, r, hin, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzfwrite_spec gz_comp_spec G hv hs buf size nitems hin) e

theorem gzputc_keepsW (G : DeflateGz) : KeepsW SPutc := by
  intro w h w' h' f hv ⟨c, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzputc_spec gz_comp_spec G hv hs c) e

theorem gzputs_keepsW (G : DeflateGz) : KeepsW SPuts := by
  intro w h w' h' f hv ⟨p, r, hp, ho, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzputs_spec gz_comp_spec G hv hs p hp ho) e

theorem gzflush_keepsW (G : DeflateGz) : KeepsW SFlush := by
  intro w h w' h' f hv ⟨fl, r, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzflush_spec gz_comp_spec G hv hs fl) e

theorem gzprintf_keepsW (G : DeflateGz) : KeepsW SPrintfO := by
  intro w h w' h' f hv ⟨fmt, r, hf, ho, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzprintf_spec gz_comp_spec G hv hs fmt hf ho) e

theorem gzvprintf_keepsW (G : DeflateGz) : KeepsW SVprintfO := by
  intro w h w' h' f hv ⟨fmt, r, hf, ho, e⟩
  obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
  exact keeps_of_call (gzvprintf_spec gz_comp_spec G hv hs fmt hf ho) e

/-- **What the write side owes**, from `DeflateGz` and the steps not proved here. -/
theorem gwrite_steps_of (G : DeflateGz) (P : KeepsW SPrintf) (V : KeepsW SVprintf) (SP : KeepsW SSetparams) :
    GWriteSteps := by
  refine ⟨fun w h w' h' f hv x => ?_⟩
  rcases x with x | x | x | x | x | x | x | x
  · exact gzwrite_keepsW G _ _ _ _ _ hv x
  · exact gzfwrite_keepsW G _ _ _ _ _ hv x
  · exact gzputc_keepsW G _ _ _ _ _ hv x
  · exact gzputs_keepsW G _ _ _ _ _ hv x
  · exact P _ _ _ _ _ hv x
  · exact V _ _ _ _ _ hv x
  · exact gzflush_keepsW G _ _ _ _ _ hv x
  · exact SP _ _ _ _ _ hv x

end ZlibNgF.Proof.GzWrite
