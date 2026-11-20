import ZlibNgF.Proof.«public-gz-open»

/-!
# Goals of `gzread.c` (`ZlibNgF`)

On a read handle with `LookIdle` each call returns with a step of the file (`gzread_call`, `gzfread_call`,
`gzgetc_read`, `gzungetc_read`, `gzgets_read`); on a write handle it returns at the mode test without a change.
`gzdirect` and `gzclose_r` are proved on every handle in `gzlib.c.handles`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode

theorem gzread_safety_of (O : GzOpen) : Goal.gzread_safety := by
  intro w h f buf len _ hh hout
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzread_call O.read O.readIdle hv hi buf len hout).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzread_write hs (modeOf hs hv.2.1) buf len, gzframe_refl w h _ _⟩

theorem gzfread_safety_of (O : GzOpen) : Goal.gzfread_safety := by
  intro w h f buf size nitems _ hh hout
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · by_cases hz : size = 0
    · exact ⟨0, w, h, by simp [GzRun, C.run, StateT.run, gzfread, hz], gzframe_refl w h none _⟩
    · exact ⟨0, w, h, by simp [GzRun, C.run, StateT.run, gzfread, hz], gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzfread_call O.read O.readIdle hv hi buf size nitems hout).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzfread_write hs (modeOf hs hv.2.1) buf size nitems, gzframe_refl w h _ _⟩

theorem gzgetc_safety_of (O : GzOpen) : Goal.gzgetc_safety := by
  intro w h f _ hh
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzgetc_read O.read O.readIdle hv hi).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzgetc_write hs (modeOf hs hv.2.1), gzframe_refl w h _ _⟩

theorem gzgetc__safety_of (O : GzOpen) : Goal.gzgetc__safety := by
  intro w h f _ hh
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzgetc__read O.read O.readIdle hv hi).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzgetc__write hs (modeOf hs hv.2.1), gzframe_refl w h _ _⟩

theorem gzungetc_safety_of (O : GzOpen) : Goal.gzungetc_safety := by
  intro w h f c _ hh
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzungetc_read O.skip O.skipIdle hv hi c).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzungetc_write hs (modeOf hs hv.2.1) c, gzframe_refl w h _ _⟩

theorem gzgets_safety_of (O : GzOpen) : Goal.gzgets_safety := by
  intro w h f buf len _ hh hbuf
  rcases handleI O hh with rfl | ⟨hv, hi⟩ | hv
  · exact ⟨.null, w, h, by simp [GzRun, C.run, StateT.run, gzgets], gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    exact frame_of ((gzgets_read gz_fetch_spec O.skip gz_fetch_idle O.skipIdle hv hi buf len
      fun h1 => (hbuf h1).symm).mono fun _ _ _ q => ⟨q.1, q.2.2⟩)
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzgets_write hs (modeOf hs hv.2.1) buf len, gzframe_refl w h _ _⟩

theorem gzdirect_safety_of (O : GzOpen) : Goal.gzdirect_safety :=
  GzMode.gzdirect_safety_of (gwriteSteps_of O) (greadPending_of O)

theorem gzclose_r_safety_of (O : GzOpen) : Goal.gzclose_r_safety :=
  GzMode.gzclose_r_safety_of (gwriteSteps_of O) (greadPending_of O)

end ZlibNgF.Proof.GzPublic
