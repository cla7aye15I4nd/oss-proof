import ZlibNgF.Proof.«gzread.c.readspec»

/-!
# `LookIdle` across `gz_fetch`, `gz_skip` and `gz_read` (`ZlibNgF`)

Statements only, next to the specifications of `gzread.c.readspec`: each of the three internal calls, started on a read
handle with `LookIdle` (fewer than two bytes of input while looking with transparent reading allowed), leaves
`LookIdle`. `gzgetc`, `gzungetc` and `gzgets` take them as hypotheses until they are proved.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-- **`gz_fetch`** keeps `LookIdle` on a read handle with `x.have == 0`. -/
def GzFetchIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap),
    GzInvR w h (some b) → LookIdle w h (some b) → w.gz h b = some s → s.«have» = 0 →
    GzRun (gz_fetch (some b)) w h r W H → LookIdle W H (some b)

/-- **`gz_skip`** keeps `LookIdle` from the mid-call state with a pending skip. -/
def GzSkipIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap),
    GzMid w h b s → LookIdle w h (some b) → s.skip ≠ 0 →
    GzRun (gz_skip (some b)) w h r W H → LookIdle W H (some b)

/-- **`gz_read`** keeps `LookIdle` on a read handle. -/
def GzReadIdle : Prop :=
  ∀ (w : World) (h : Heap) (b : Nat) (buf : BPtr) (len r : UInt64) (W : World) (H : Heap),
    GzInvR w h (some b) → LookIdle w h (some b) → GzOut w h (some b) buf len.toNat →
    GzRun (gz_read (some b) buf len) w h r W H → LookIdle W H (some b)

/-- A run that satisfies `P` is a run of the computation. -/
theorem GSat.withRun {α : Type} {w : World} {h : Heap} {m : G α} {P : α → World → Heap → Prop}
    (hm : GSat w h m P) : GSat w h m (fun r W H => P r W H ∧ GzRun m w h r W H) := by
  obtain ⟨r, W, H, e, p⟩ := hm
  exact ⟨r, W, H, e, p, e⟩

end ZlibNgF.Proof.GzMode
