import ZlibNgF.Proof.«public-gz-handles»

/-!
# Goals of `gzwrite.c` (`ZlibNgF`)

On a write handle each call returns with a step of the file (`gzwrite_spec`, `gzfwrite_spec`, `gzputc_spec`,
`gzputs_spec`, `gzprintf_spec`, `gzvprintf_spec`, `gzflush_spec`, `gzsetparams_spec`, with the obligations of the
deflate side `deflateGz`); on a read handle it returns at the mode test without a change. `gzclose_w` on a write
handle releases the file (`GzWrite.closeW_of deflateGz`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzPublic
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWrite
open ZlibNgF.Proof.DeflateGz (deflateGz)

/-- A public write call on a write handle changes only what the frame names. -/
theorem frame_call {α : Type} {m : G α} {w : World} {h : Heap} {b : Nat} (hm : GSat w h m (CallPost w h b)) :
    ∃ r w' h', GzRun m w h r w' h' ∧ GzFrame w h w' h' (some b) [] :=
  frame_of hm

theorem gzwrite_safety : Goal.gzwrite_safety := by
  intro w h f buf len _ hh hin
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzwrite_read hs (modeOf hs hv.2.1) buf len, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzwrite_spec gz_comp_spec deflateGz hv hs buf len hin)

theorem gzfwrite_safety : Goal.gzfwrite_safety := by
  intro w h f buf size nitems _ hh hin
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · by_cases hz : size = 0
    · exact ⟨0, w, h, by simp [GzRun, C.run, StateT.run, gzfwrite, hz], gzframe_refl w h none _⟩
    · exact ⟨0, w, h, by simp [GzRun, C.run, StateT.run, gzfwrite, hz], gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzfwrite_read hs (modeOf hs hv.2.1) buf size nitems, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzfwrite_spec gz_comp_spec deflateGz hv hs buf size nitems hin)

theorem gzputc_safety : Goal.gzputc_safety := by
  intro w h f c _ hh
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzputc_read hs (modeOf hs hv.2.1) c, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzputc_spec gz_comp_spec deflateGz hv hs c)

theorem gzputs_safety : Goal.gzputs_safety := by
  intro w h f p _ hh hp ho
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzputs_read hs (modeOf hs hv.2.1) p, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzputs_spec gz_comp_spec deflateGz hv hs p hp ho)

theorem gzvprintf_safety : Goal.gzvprintf_safety := by
  intro w h f fmt _ hh hf ho
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzvprintf_read hs (modeOf hs hv.2.1) fmt, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzvprintf_spec gz_comp_spec deflateGz hv hs fmt hf ho)

theorem gzprintf_safety : Goal.gzprintf_safety := by
  intro w h f fmt _ hh hf ho
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzprintf_read hs (modeOf hs hv.2.1) fmt, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzprintf_spec gz_comp_spec deflateGz hv hs fmt hf ho)

theorem gzflush_safety : Goal.gzflush_safety := by
  intro w h f fl _ hh
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzflush_read hs (modeOf hs hv.2.1) fl, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzflush_spec gz_comp_spec deflateGz hv hs fl)

theorem gzsetparams_safety : Goal.gzsetparams_safety := by
  intro w h f l st _ hh
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, w, h, gzsetparams_read hs (modeOf hs hv.2.1) l st, gzframe_refl w h _ _⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact frame_call (gzsetparams_spec deflateGz hv hs l st)

/-! ## `gzclose_w` -/

theorem gzclose_w_read {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hm : s.mode = GZ_READ) : GzRun (gzclose_w (some b)) w h ZlibNg.Inflate.Z_STREAM_ERROR w h := by
  simp [GzRun, C.run, StateT.run, gzclose_w, rdG_app' hs, hm, read_ne_write]

theorem gzclose_w_safety : Goal.gzclose_w_safety := by
  intro w h f hwf hh
  rcases handleI hh with rfl | ⟨hv, -⟩ | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none [], fun ⟨_, _, e, _⟩ => by cases e⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    have hr := modeOf hs hv.2.1
    refine ⟨_, w, h, gzclose_w_read hs hr, gzframe_refl w h _ [], fun ⟨b', s', e, hs', hm⟩ => ?_⟩
    cases e; rw [hs] at hs'; cases hs'
    exact absurd (hm.symm.trans hr) write_ne_read
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, fr, rel⟩ := GzWrite.closeW_of deflateGz w h b s hwf hv hs
    exact ⟨r, w', h', e, fr, fun _ => rel⟩

end ZlibNgF.Proof.GzPublic
