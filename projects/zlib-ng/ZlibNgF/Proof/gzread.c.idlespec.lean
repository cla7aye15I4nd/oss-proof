import ZlibNgF.Proof.«gzread.c.readspec»

/-!
# Runs of gz computations (`ZlibNgF`)

`GSat.withRun`: a `GSat` statement also names the run it describes, so that statements about runs (`GzSkipIdle`,
`GzFetchIdle`, `GzReadIdle` of `gzread.c.readspec`) apply to it.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNg.Gz ZlibNgF.Proof.GzSat

/-- A run that satisfies `P` is a run of the computation. -/
theorem GSat.withRun {α : Type} {w : World} {h : Heap} {m : G α} {P : α → World → Heap → Prop}
    (hm : GSat w h m P) : GSat w h m (fun r W H => P r W H ∧ GzRun m w h r W H) := by
  obtain ⟨r, W, H, e, p⟩ := hm
  exact ⟨r, W, H, e, p, e⟩

end ZlibNgF.Proof.GzMode
