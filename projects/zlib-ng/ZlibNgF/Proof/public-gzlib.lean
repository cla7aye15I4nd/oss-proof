import ZlibNgF.Proof.«public-gz-handles»

/-!
# Goals of `gzlib.c` (`ZlibNgF`)

`gzbuffer`, `gzseek`, `gzseek64`, `gzrewind`, `gztell`, `gztell64`, `gzoffset`, `gzoffset64`, `gzeof`, `gzerror`,
`gzclearerr` (and `gzdirect`, `gzclose_r` of `gzread.c`) are proved on every handle in `gzlib.c.handles` from
`gwriteSteps` and `greadPending`. `gzclose` calls `gzclose_r` or `gzclose_w` by the mode of the file; `gzclose_w` on
a write handle is `GzWrite.closeW_of deflateGz`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.DeflateGz (deflateGz)

theorem gzbuffer_safety : Goal.gzbuffer_safety :=
  GzMode.gzbuffer_safety_of gwriteSteps greadPending

theorem gzseek_safety : Goal.gzseek_safety :=
  GzMode.gzseek_safety_of gwriteSteps greadPending

theorem gzseek64_safety : Goal.gzseek64_safety :=
  GzMode.gzseek64_safety_of gwriteSteps greadPending

theorem gzrewind_safety : Goal.gzrewind_safety :=
  GzMode.gzrewind_safety_of gwriteSteps greadPending

theorem gztell_safety : Goal.gztell_safety :=
  GzMode.gztell_safety_of gwriteSteps greadPending

theorem gztell64_safety : Goal.gztell64_safety :=
  GzMode.gztell64_safety_of gwriteSteps greadPending

theorem gzoffset_safety : Goal.gzoffset_safety :=
  GzMode.gzoffset_safety_of gwriteSteps greadPending

theorem gzoffset64_safety : Goal.gzoffset64_safety :=
  GzMode.gzoffset64_safety_of gwriteSteps greadPending

theorem gzeof_safety : Goal.gzeof_safety :=
  GzMode.gzeof_safety_of gwriteSteps greadPending

theorem gzerror_safety : Goal.gzerror_safety :=
  GzMode.gzerror_safety_of gwriteSteps greadPending

theorem gzclearerr_safety : Goal.gzclearerr_safety :=
  GzMode.gzclearerr_safety_of gwriteSteps greadPending

/-! ## `gzclose` -/

theorem gzclose_eq_r {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hm : s.mode = GZ_READ)
    {r : Int32} {w' : World} {h' : Heap} (e : GzRun (gzclose_r (some b)) w h r w' h') :
    GzRun (gzclose (some b)) w h r w' h' := by
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simpa [gzclose, rdG_app' hs, hm] using e

theorem gzclose_eq_w {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (hm : s.mode = GZ_WRITE)
    {r : Int32} {w' : World} {h' : Heap} (e : GzRun (gzclose_w (some b)) w h r w' h') :
    GzRun (gzclose (some b)) w h r w' h' := by
  simp only [GzRun, C.run, StateT.run] at e ⊢
  simpa [gzclose, rdG_app' hs, hm, write_ne_read] using e

theorem gzclose_safety : Goal.gzclose_safety := by
  intro w h f hwf hh
  rcases handleI hh with rfl | hv | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none [], fun _ _ e => by cases e⟩
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1.1
    obtain ⟨r, w', h', e, fr, rel⟩ := gzclose_r_read hs sh hn (modeOf hs hv.1.2.1)
    exact ⟨r, w', h', gzclose_eq_r hs (modeOf hs hv.1.2.1) e, fr, rel⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, fr, rel⟩ := GzWrite.closeW_of deflateGz w h b s hwf hv hs
    exact ⟨r, w', h', gzclose_eq_w hs (modeOf hs hv.2.1) e, fr, rel⟩

end ZlibNgF.Proof.GzPublic
