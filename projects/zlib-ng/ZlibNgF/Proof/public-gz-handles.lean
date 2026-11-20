import ZlibNgF.Proof.«gzlib.c.handles»
import ZlibNgF.Proof.«gzread.c.wrap»
import ZlibNgF.Proof.«gzread.c.pushback»
import ZlibNgF.Proof.«gzread.c.gets»
import ZlibNgF.Proof.«gzread.c.fetch»
import ZlibNgF.Proof.«gzread.c.read»
import ZlibNgF.Proof.«gzwrite.c.keeps»
import ZlibNgF.Proof.«gzwrite.c.close»
import ZlibNgF.Proof.«deflate.c.gzneeds»

/-!
# What every gz goal uses (`ZlibNgF`)

The read-side calls keep the read invariant with `LookIdle` (`greadPending`, from the specifications of `gz_skip`,
`gz_read` and `gz_fetch` with their `LookIdle` companions), and the write-side calls keep the write invariant
(`gwriteSteps`, from the obligations of the deflate side `deflateGz`). Together they give the induction over reachable
files (`handleI`), from which the goal of each gz function follows (`public-gzlib`, `public-gzread`,
`public-gzwrite`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- The read-side calls keep the read invariant with `LookIdle`. -/
theorem greadPending : GReadPending :=
  ⟨read_keepsRI gz_read_spec gz_read_idle, fread_keepsRI gz_read_spec gz_read_idle,
    getc_keepsRI gz_read_spec gz_read_idle, getc__keepsRI gz_read_spec gz_read_idle,
    ungetc_keepsRI gz_skip_spec gz_skip_idle, gets_keepsRI gz_fetch_spec gz_skip_spec gz_fetch_idle gz_skip_idle⟩

/-- The write-side calls keep the write invariant. -/
theorem gwriteSteps : GWriteSteps := GzWrite.gwrite_steps_of ZlibNgF.Proof.DeflateGz.deflateGz

/-- An accepted file is `NULL`, a read handle with `LookIdle`, or a write handle. -/
theorem handleI {w : World} {h : Heap} {f : GzPtr} (hh : GzHandle w h f) :
    f = none ∨ (GzInvR w h f ∧ LookIdle w h f) ∨ GzInvWS w h f := by
  rcases hh with rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (greachI gwriteSteps greadPending hr)

/-- A run that satisfies a step of the file changes only what the frame names. -/
theorem frame_of {α : Type} {m : G α} {w : World} {h : Heap} {b : Nat} {wr : List (BPtr × Nat)}
    {P : α → World → Heap → Prop} (hm : GSat w h m (fun r W H => P r W H ∧ GStep w h W H b wr)) :
    ∃ r w' h', GzRun m w h r w' h' ∧ GzFrame w h w' h' (some b) wr := by
  obtain ⟨r, W, H, e, -, g⟩ := hm.run
  exact ⟨r, W, H, e, g.frame⟩

end ZlibNgF.Proof.GzPublic
