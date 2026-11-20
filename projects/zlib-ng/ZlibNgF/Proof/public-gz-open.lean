import ZlibNgF.Proof.«gzlib.c.handles»
import ZlibNgF.Proof.«gzread.c.wrap»
import ZlibNgF.Proof.«gzread.c.pushback»
import ZlibNgF.Proof.«gzread.c.gets»
import ZlibNgF.Proof.«gzread.c.fetch»
import ZlibNgF.Proof.«gzwrite.c.keeps»

/-!
# The gz goals from the statements still open (`ZlibNgF`)

`GzOpen` collects the statements about internal functions that the gz goals use and that are not theorems yet: the
specifications of `gz_skip` and `gz_read` with their `LookIdle` companions (`gzread.c.readspec`), and the obligations
of the deflate side (`DeflateGz`). Everything else the goals use is proved: from `GzOpen` follow `GReadPending` and
`GWriteSteps`, so the induction over reachable files (`handleI`), and the goal of each gz function on an accepted file
(`public-gzlib`, `public-gzread`, `public-gzwrite`). `gzclose` and `gzclose_w` also take what `gzclose_w` does on a
write handle (`CloseW`), which has no statement elsewhere yet.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- **The statements still open** that the gz goals use. -/
structure GzOpen : Prop where
  skip : GzSkipSpec
  skipIdle : GzSkipIdle
  read : GzReadSpec
  readIdle : GzReadIdle
  deflate : DeflateGz

/-- The read-side calls keep the read invariant with `LookIdle`. -/
theorem greadPending_of (O : GzOpen) : GReadPending :=
  ⟨read_keepsRI O.read O.readIdle, fread_keepsRI O.read O.readIdle, getc_keepsRI O.read O.readIdle,
    getc__keepsRI O.read O.readIdle, ungetc_keepsRI O.skip O.skipIdle,
    gets_keepsRI gz_fetch_spec O.skip gz_fetch_idle O.skipIdle⟩

/-- The write-side calls keep the write invariant. -/
theorem gwriteSteps_of (O : GzOpen) : GWriteSteps := GzWrite.gwrite_steps_of O.deflate

/-- An accepted file is `NULL`, a read handle with `LookIdle`, or a write handle. -/
theorem handleI (O : GzOpen) {w : World} {h : Heap} {f : GzPtr} (hh : GzHandle w h f) :
    f = none ∨ (GzInvR w h f ∧ LookIdle w h f) ∨ GzInvWS w h f := by
  rcases hh with rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (greachI (gwriteSteps_of O) (greadPending_of O) hr)

/-- What `gzclose_w` does on a write handle: it returns, changes only what the frame names, and releases the file. -/
def CloseW : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState), GzWF w h → GzInvWS w h (some b) → w.gz h b = some s →
    ∃ r w' h', GzRun (gzclose_w (some b)) w h r w' h' ∧ GzFrame w h w' h' (some b) [] ∧ GzReleased w h w' h' (some b)

/-- A run that satisfies a step of the file changes only what the frame names. -/
theorem frame_of {α : Type} {m : G α} {w : World} {h : Heap} {b : Nat} {wr : List (BPtr × Nat)}
    {P : α → World → Heap → Prop} (hm : GSat w h m (fun r W H => P r W H ∧ GStep w h W H b wr)) :
    ∃ r w' h', GzRun m w h r w' h' ∧ GzFrame w h w' h' (some b) wr := by
  obtain ⟨r, W, H, e, -, g⟩ := hm.run
  exact ⟨r, W, H, e, g.frame⟩

end ZlibNgF.Proof.GzPublic
