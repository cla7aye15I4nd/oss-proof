import ZlibNgF.Proof.«gzread.c.close»
import ZlibNgF.Proof.«gzlib.c.seek64»
import ZlibNgF.Proof.«gzread.c.lookspec»

/-!
# The induction over reachable files, and the goals proved on every handle (`ZlibNgF`)

`greachI (W : GWriteSteps) (R : GReadPending) : GzReachable w h f → (GzInvR w h f ∧ LookIdle w h f) ∨ GzInvWS w h f`
(`LookIdle` is a between-call fact carried next to the read invariant). Each goal of a read-side call follows from `GWriteSteps` (what the write side owes) and `GReadPending` (the read-side calls whose
preservation of the read invariant is not proved yet).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## The induction -/

/-- The read-side calls whose preservation of the invariant (with `LookIdle`) is not proved yet. -/
structure GReadPending : Prop where
  read : KeepsRI SRead
  fread : KeepsRI SFread
  getc : KeepsRI SGetc
  getc_ : KeepsRI SGetc_
  ungetc : KeepsRI SUngetc
  gets : KeepsRI SGets

theorem step_keeps (W : GWriteSteps) (R : GReadPending) {w : World} {h : Heap} {w' : World} {h' : Heap} {f : GzPtr}
    (hv : (GzInvR w h f ∧ LookIdle w h f) ∨ GzInvWS w h f) (hs : GzStep w h w' h' f) :
    (GzInvR w' h' f ∧ LookIdle w' h' f) ∨ GzInvWS w' h' f := by
  rcases hv with ⟨hv, hi⟩ | hv
  · left
    rcases hs with x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x
    · exact buffer_keepsI _ _ _ _ _ hv hi x
    · exact R.read _ _ _ _ _ hv hi x
    · exact R.fread _ _ _ _ _ hv hi x
    · exact R.getc _ _ _ _ _ hv hi x
    · exact R.getc_ _ _ _ _ _ hv hi x
    · exact R.ungetc _ _ _ _ _ hv hi x
    · exact R.gets _ _ _ _ _ hv hi x
    · exact direct_keepsRI _ _ _ _ _ hv hi x
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inl x)
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inl x))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inl x)))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inr (Or.inl x))))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x)))))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x))))))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x)))))))
    · exact wstep_keepsRI _ _ _ _ _ hv hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr x)))))))
    · exact seek64R_keepsI _ _ _ _ _ hv hi x
    · exact seekR_keepsI _ _ _ _ _ hv hi x
    · exact rewind_keepsRI _ _ _ _ _ hv hi x
    · exact tell64_keepsI _ _ _ _ _ hv hi x
    · exact tell_keepsI _ _ _ _ _ hv hi x
    · exact offset64_keepsI _ _ _ _ _ hv hi x
    · exact offset_keepsI _ _ _ _ _ hv hi x
    · exact eof_keepsI _ _ _ _ _ hv hi x
    · exact error_keepsI _ _ _ _ _ hv hi x
    · exact clearerr_keepsI _ _ _ _ _ hv hi x
  · right
    rcases hs with x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x
    · exact buffer_keeps.2 _ _ _ _ _ hv x
    · exact read_keepsW _ _ _ _ _ hv x
    · exact fread_keepsW _ _ _ _ _ hv x
    · exact getc_keepsW _ _ _ _ _ hv x
    · exact getc__keepsW _ _ _ _ _ hv x
    · exact ungetc_keepsW _ _ _ _ _ hv x
    · exact gets_keepsW _ _ _ _ _ hv x
    · exact direct_keepsW _ _ _ _ _ hv x
    · exact W.step _ _ _ _ _ hv (Or.inl x)
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inl x))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inl x)))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inr (Or.inl x))))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x)))))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x))))))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x)))))))
    · exact W.step _ _ _ _ _ hv (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr x)))))))
    · exact seek64W_keeps _ _ _ _ _ hv x
    · exact seekW_keeps _ _ _ _ _ hv x
    · exact rewind_keepsW _ _ _ _ _ hv x
    · exact tell64_keeps.2 _ _ _ _ _ hv x
    · exact tell_keeps.2 _ _ _ _ _ hv x
    · exact offset64_keeps.2 _ _ _ _ _ hv x
    · exact offset_keeps.2 _ _ _ _ _ hv x
    · exact eof_keeps.2 _ _ _ _ _ hv x
    · exact error_keeps.2 _ _ _ _ _ hv x
    · exact clearerr_keeps.2 _ _ _ _ _ hv x

/-- A successful opening call leaves a read or a write handle. -/
theorem open_keeps {m : G GzPtr} {w : World} {h : Heap} {f : GzPtr} {w' : World} {h' : Heap}
    (hs : GSat w h m (GzOpen.OpenPost w h)) (e : GzRun m w h f w' h') (hne : f ≠ none) :
    GzInvR w' h' f ∨ GzInvWS w' h' f := by
  obtain ⟨hv, hwf⟩ := GzOpenPublic.open_inv hs e hne
  obtain ⟨b, s, rfl, hs', sh, hn⟩ := hv
  rcases sh.mode with hm | hm
  · exact Or.inl ⟨⟨b, s, rfl, hs', sh, hn⟩, ⟨b, s, rfl, hs', hm⟩, GzWFr.of hwf⟩
  · exact Or.inr ⟨⟨b, s, rfl, hs', sh, hn⟩, ⟨b, s, rfl, hs', hm⟩, GzWFw.of hwf⟩

/-- A successful opening call leaves no buffers, so `LookIdle` holds on a read handle. -/
theorem open_keepsI {m : G GzPtr} {w : World} {h : Heap} {f : GzPtr} {w' : World} {h' : Heap}
    (hs : GSat w h m (GzOpen.OpenPost w h)) (e : GzRun m w h f w' h') (hne : f ≠ none) :
    (GzInvR w' h' f ∧ LookIdle w' h' f) ∨ GzInvWS w' h' f := by
  rcases open_keeps hs e hne with hv | hv
  · left
    refine ⟨hv, ?_⟩
    obtain ⟨r, w2, h2, e2, q⟩ := hs
    have e' : m w h = .ok ((f, w'), h') := e
    rw [e2] at e'
    cases e'
    cases f with
    | none => exact absurd rfl hne
    | some b =>
      obtain ⟨-, s, hs', -, hsz, -⟩ := q.2.2 b rfl
      exact idle_of hv hs' (Or.inr (Or.inr hsz))
  · exact Or.inr hv

/-- **The induction.** A reachable file is a read handle with `LookIdle` or a write handle. -/
theorem greachI (W : GWriteSteps) (R : GReadPending) {w : World} {h : Heap} {f : GzPtr} (hr : GzReachable w h f) :
    (GzInvR w h f ∧ LookIdle w h f) ∨ GzInvWS w h f := by
  induction hr with
  | gzopen w h w' h' path mode f hwf hp hm e hne =>
    exact open_keepsI (GzOpenPublic.gzopen_spec hwf path mode (Or.inr hp) (Or.inr hm)) e hne
  | gzopen64 w h w' h' path mode f hwf hp hm e hne =>
    exact open_keepsI (GzOpenPublic.gzopen64_spec hwf path mode (Or.inr hp) (Or.inr hm)) e hne
  | gzdopen w h w' h' fd mode f hwf hm e hne =>
    exact open_keepsI (GzOpenPublic.gzdopen_spec hwf fd mode (Or.inr hm)) e hne
  | step w h w' h' f _ hs ih => exact step_keeps W R ih hs
  | caller w h w' h' f _ hc ih =>
    rcases ih with ⟨ih, hi⟩ | ih
    · exact Or.inl (caller_keepsRI _ _ _ _ _ ih hi hc)
    · exact Or.inr (caller_keepsW _ _ _ _ _ ih hc)

/-- A reachable file is a read handle or a write handle. -/
theorem greach (W : GWriteSteps) (R : GReadPending) {w : World} {h : Heap} {f : GzPtr} (hr : GzReachable w h f) :
    GzInvR w h f ∨ GzInvWS w h f :=
  (greachI W R hr).imp_left And.left

/-- An accepted file is `NULL`, a read handle or a write handle. -/
theorem handle (W : GWriteSteps) (R : GReadPending) {w : World} {h : Heap} {f : GzPtr} (hh : GzHandle w h f) :
    f = none ∨ GzInvR w h f ∨ GzInvWS w h f := by
  rcases hh with rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (greach W R hr)

/-! ## Goals of the calls proved on every handle -/

theorem gzeof_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzeof_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := GzReach.gzeof_inv ((handle W R hh).imp_right parts')
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

theorem gztell64_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gztell64_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := GzReach.gztell64_inv ((handle W R hh).imp_right parts')
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

theorem gztell_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gztell_safety := by
  intro w h f _ hh
  obtain ⟨r, e⟩ := GzReach.gztell_inv ((handle W R hh).imp_right parts')
  exact ⟨r, w, h, e, gzframe_refl w h f []⟩

theorem gzoffset64_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzoffset64_safety := by
  intro w h f hwf hh
  obtain ⟨r, fs', e, -⟩ := GzReach.gzoffset64_inv (fun _ _ _ _ _ => hwf.2.2.2.2.2.2.2.1)
    ((handle W R hh).imp_right parts')
  exact ⟨r, _, h, e, GzReach.gzframe_fs h f rfl⟩

theorem gzoffset_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzoffset_safety := by
  intro w h f hwf hh
  obtain ⟨r, fs', e, -⟩ := GzReach.gzoffset_inv (fun _ _ _ _ _ => hwf.2.2.2.2.2.2.2.1)
    ((handle W R hh).imp_right parts')
  exact ⟨r, _, h, e, GzReach.gzframe_fs h f rfl⟩

theorem gzerror_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzerror_safety := by
  intro w h f e _ hh
  obtain ⟨r, w', h', e', fr, -⟩ := GzReach.gzerror_inv e ((handle W R hh).imp_right parts')
  exact ⟨r, w', h', e', fr⟩

theorem gzbuffer_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzbuffer_safety := by
  intro w h f n _ hh
  rcases (handle W R hh).imp_right parts' with rfl | ⟨b, s, rfl, hs, sh, -⟩
  · exact ⟨-1, w, h, rfl, gzframe_refl w h none []⟩
  · rcases gzbuffer_run hs sh.mode n with ⟨-, e⟩ | ⟨-, v, -, -, e⟩
    · exact ⟨-1, w, h, e, gzframe_refl w h _ []⟩
    · exact ⟨0, _, h, e, gzframe_less (HLess.refl h) (fun _ _ => rfl) (fun _ _ e => e) (fun _ _ => rfl)
        fun c hc _ => by
          have hcb : c ≠ b := fun e => hc (by rw [e])
          simp [upd_ne _ _ _ _ hcb]⟩

theorem gzclearerr_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzclearerr_safety := by
  intro w h f _ hh
  rcases (handle W R hh).imp_right parts' with rfl | ⟨b, s, rfl, hs, sh, hn⟩
  · exact ⟨(), w, h, rfl, gzframe_refl w h none []⟩
  · refine ⟨(), _, _, gzclearerr_run hs sh.mode sh.msg (msg_ne_b hn), gzframe_less (HLess.free h s) (fun _ _ => by rw [freeMsg_streams])
      (fun k a e => by unfold freeMsg; split <;> (try split) <;> exact e) (fun c hc => freeMsg_bytes h s c ?_)
      fun c hc _ => by
          have hcb : c ≠ b := fun e => hc (by rw [e])
          simp [upd_ne _ _ _ _ hcb]⟩
    intro hm
    exact hc (ownL_owned hs c (by unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm)))

/-- The heap blocks `freeMsg` may free belong to the file. -/
theorem freeMsg_bytes_owned {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) (c : Nat)
    (hc : c ∉ GzOwned w h (some b)) : (freeMsg h s).bytes c = h.bytes c := by
  refine freeMsg_bytes h s c fun hm => hc (ownL_owned hs c ?_)
  unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm)

theorem gzrewind_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzrewind_safety := by
  intro w h f _ hh
  rcases handle W R hh with rfl | hv | hv
  · exact ⟨-1, w, h, rfl, gzframe_refl w h none []⟩
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    have hr := modeOf hs hv.2.1
    obtain ⟨z, hz⟩ := sh.strm
    rcases gzrewind_read hs hr sh.msg hn hz with e | ⟨fs', -, e⟩ | ⟨fs', -, e⟩
    · exact ⟨_, _, _, e, gzframe_refl w h _ []⟩
    · exact ⟨_, _, _, e, GzReach.gzframe_fs h _ rfl⟩
    · refine ⟨_, _, _, e, gzframe_less ((HLess.free h s).trans (HLess.av0 _ _ _)) (fun i hi => ?_)
        (fun k a e => ?_) (fun c hc => freeMsg_bytes_owned hs c hc) fun c hc _ => ?_⟩
      · have hi' := hi b s rfl hs
        simp only [avail0]; rw [upd_ne _ _ _ _ hi', freeMsg_streams]
      · show (freeMsg h s).consts k = some a
        unfold freeMsg; split <;> (try split) <;> exact e
      · have hcb : c ≠ b := fun e => hc (by rw [e])
        simp [upd_ne _ _ _ _ hcb]
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    exact ⟨_, _, _, gzrewind_write hs (modeOf hs hv.2.1), gzframe_refl w h _ []⟩

theorem gzclose_r_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzclose_r_safety := by
  intro w h f _ hh
  rcases handle W R hh with rfl | hv | hv
  · exact ⟨_, w, h, rfl, gzframe_refl w h none [], fun ⟨_, _, e, _⟩ => by cases e⟩
  · obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
    obtain ⟨r, w', h', e, fr, rel⟩ := gzclose_r_read hs sh hn (modeOf hs hv.2.1)
    exact ⟨r, w', h', e, fr, fun _ => rel⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    have hw := modeOf hs hv.2.1
    refine ⟨_, _, _, gzclose_r_write hs hw, gzframe_refl w h _ [], fun ⟨b', s', e, hs', hm⟩ => ?_⟩
    cases e; rw [hs] at hs'; cases hs'
    exact absurd (hm.symm.trans hw) read_ne_write

theorem gzseek64_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzseek64_safety := by
  intro w h f off wh _ hh
  rcases handle W R hh with rfl | hv | hv
  · exact ⟨-1, w, h, rfl, gzframe_refl w h none []⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, -, g⟩ := gzseek64_read hv hs off wh
    exact ⟨r, w', h', e, g.frame⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, -, g⟩ := gzseek64_write hv hs off wh
    exact ⟨r, w', h', e, g.frame⟩

theorem gzseek_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzseek_safety := by
  intro w h f off wh _ hh
  rcases handle W R hh with rfl | hv | hv
  · exact ⟨-1, w, h, rfl, gzframe_refl w h none []⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, -, g⟩ := gzseek_of (gzseek64_read hv hs off wh)
    exact ⟨r, w', h', e, g.frame⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, -, g⟩ := gzseek_of (gzseek64_write hv hs off wh)
    exact ⟨r, w', h', e, g.frame⟩

theorem gzdirect_safety_of (W : GWriteSteps) (R : GReadPending) : Goal.gzdirect_safety := by
  intro w h f _ hh
  rcases handle W R hh with rfl | hv | hv
  · exact ⟨0, w, h, rfl, gzframe_refl w h none []⟩
  · obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
    obtain ⟨r, w', h', e, -, g, -⟩ := (gzdirect_read hv).run
    exact ⟨r, w', h', e, g.frame⟩
  · obtain ⟨b, s, rfl, hs, -, -⟩ := hv.1
    exact ⟨_, _, _, gzdirect_write hs (modeOf hs hv.2.1), gzframe_refl w h _ []⟩

end ZlibNgF.Proof.GzMode
