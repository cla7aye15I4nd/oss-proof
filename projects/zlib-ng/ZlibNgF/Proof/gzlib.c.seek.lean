import ZlibNgF.Proof.«gzlib.c.mode»

/-!
# `gz_reset`, `gzrewind`, `gzseek64` and `gzseek` keep the invariant (`ZlibNgF`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

/-! ## `avail_in = 0` on the stream of a read handle -/

/-- The heap with `avail_in = 0` in stream `i`. -/
def avail0 (h : Heap) (i : Nat) (z : ZStream) : Heap :=
  { h with streams := upd h.streams i (some { z with avail_in := 0 }) }

theorem regHdr_avail0 {h : Heap} {i : Nat} {z : ZStream} (hz : h.streams i = some z) {hp : HeaderPtr}
    (hr : RegisteredHeader (avail0 h i z) (some i) hp) : RegisteredHeader h (some i) hp := by
  obtain ⟨sb, st, ⟨z', ⟨i', e, hz'⟩, hsb⟩, hst, hhd⟩ := hr
  cases e
  simp [avail0] at hz'
  subst hz'
  exact ⟨sb, st, ⟨z, ⟨i, rfl, hz⟩, hsb⟩, hst, hhd⟩

/-- `avail_in := 0` on the stream of a read handle keeps its fields. -/
theorem shape_avail0 {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (sh : GzShape h s) (hr : s.mode = GZ_READ)
    (hz : h.streams s.strm = some z) :
    GzShape (avail0 h s.strm z) s ∧ ownL (avail0 h s.strm z) b s = ownL h b s := by
  have hst : stBlk (avail0 h s.strm z) s = stBlk h s := by simp [stBlk, avail0, hz]
  refine ⟨?_, by simp only [ownL, hst]⟩
  have R := sh.read hr
  refine ⟨sh.mode, ownStr_keep sh.path fun _ _ => rfl, ⟨{ z with avail_in := 0 }, by simp [avail0]⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos,
    ⟨?_, sh.msg.mem⟩, fun _ => ⟨R.how, fun hsz => ?_, R.nobuf, R.skip_have, fun hz0 => ?_⟩,
    fun e => absurd (hr.symm.trans e) read_ne_write, fun hz c hc => sh.dead hz c (by rw [hst] at hc; exact hc)⟩
  · rcases sh.msg.msg with e | hm
    · exact Or.inl e
    · exact Or.inr (ownBlk_keep hm fun _ _ => rfl)
  · obtain ⟨c, base, z0, hb, hi, hz0, hhv, -, hreg, hmsg⟩ := R.bufs hsz
    rw [hz] at hz0; cases hz0
    obtain ⟨d, hd, hds⟩ := hb.fits
    obtain ⟨i, z1, sb, st, al, e, hz1, hsb, hst1, hal, core⟩ := hi
    cases e
    rw [hz] at hz1; cases hz1
    refine ⟨c, base, { z with avail_in := 0 }, ⟨hb.size, hb.buffers, hb.inp, hb.out, ⟨d, hd, hds⟩, hb.hdr⟩, ?_,
      by simp [avail0], hhv, Or.inl rfl, fun hp hr' => hreg hp (regHdr_avail0 hz hr'), hmsg⟩
    exact InflateReach.caller_inv ⟨s.strm, z, sb, st, al, rfl, hz, hsb, hst1, hal, core⟩
      ⟨s.strm, z, { z with avail_in := 0 }, sb, rfl, hz, by simp [avail0], hsb, rfl, rfl, rfl, rfl,
        fun k g _ hg => ⟨g, hg⟩, rfl, Nat.le_refl _⟩
  · obtain ⟨z0, hz0', a1, a2, -⟩ := R.fresh hz0
    rw [hz] at hz0'; cases hz0'
    exact ⟨{ z with avail_in := 0 }, by simp [avail0], a1, a2, rfl⟩

/-! ## `gz_reset` of a read handle -/

/-- The state after the stores of `gz_reset` before its `gz_error`, on a read handle. -/
def rst0 (s : GzState) : GzState := { s with «have» := 0, eof := 0, past := 0, how := LOOK, skip := 0 }

/-- The state after `gz_reset` of a read handle. -/
def rstSt (s : GzState) : GzState := { errSt (rst0 s) ZlibNg.Inflate.Z_OK with pos := 0 }

theorem freeMsg_rst0 (h : Heap) (s : GzState) : freeMsg h (rst0 s) = freeMsg h s := rfl

theorem freeMsg_bytes_b {h : Heap} {b : Nat} {s : GzState} (hn : (ownL h b s).Nodup) {d : Array UInt8}
    (hd : h.bytes b = some d) : (freeMsg h s).bytes b = some d := by
  rw [freeMsg_bytes h s b fun hc => ?_]; exact hd
  revert hc
  cases e : s.msg with
  | uninit => simp [blkOf]
  | val p =>
    cases p with
    | null => simp [blkOf]
    | ref r o =>
      cases r with
      | heap c => simp only [blkOf, List.mem_singleton]; intro e'; exact msg_ne_b hn c o e e'.symm
      | const k => simp [blkOf]
      | str k => simp [blkOf]

theorem gz_reset_read {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hs : w.gz h b = some s)
    (hr : s.mode = GZ_READ) (hm : GzMsg h s) (hn : (ownL h b s).Nodup) (hz : h.streams s.strm = some z) :
    GzRun (gz_reset (some b)) w h () { w with gzs := upd w.gzs b (some (rstSt s)) }
      (avail0 (freeMsg h s) s.strm z) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  have hdb' := freeMsg_bytes_b hn hdb
  have hz' : (freeMsg h s).streams s.strm = some z := by rw [freeMsg_streams]; exact hz
  have e := gz_error_null_app (w := { w with gzs := upd w.gzs b (some (rst0 s)) }) (gz_upd_same hs _)
    ⟨hm.msg, hm.mem⟩ (msg_ne_b hn) ZlibNg.Inflate.Z_OK
  simp only [GzRun, C.run, StateT.run]
  rw [freeMsg_rst0] at e
  simp only [rst0, InflateInv.upd_upd, hr] at e
  simp [gz_reset, rdG_app' hs, wrG_app hs, hr, wrG_upd hdb, rdG_upd hdb, InflateInv.upd_upd]
  rw [e]
  simp [wrG_upd hdb', strmOf_upd hdb', Uncompress.wrZ_app hz', InflateInv.upd_upd, rstSt, rst0, avail0, errSt, hr]

/-- The fields after `gz_reset` of a read handle. -/
theorem reset_keep {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (sh : GzShape h s) (hr : s.mode = GZ_READ)
    (hn : (ownL h b s).Nodup) (hz : h.streams s.strm = some z) :
    GzShape (avail0 (freeMsg h s) s.strm z) (rstSt s) ∧ (ownL (avail0 (freeMsg h s) s.strm z) b (rstSt s)).Nodup := by
  obtain ⟨sh1, hn1⟩ := clear_keep (b := b) sh hn
  have e1 : errSt (clrSt s) ZlibNg.Inflate.Z_OK =
      { s with eof := 0, past := 0, err := ZlibNg.Inflate.Z_OK, msg := .val .null } := by
    simp [errSt, clrSt, hr]
  rw [e1] at sh1 hn1
  have R := sh1.read hr
  have hsk : (rstSt s).skip = 0 := rfl
  have hpo : (rstSt s).pos = 0 := rfl
  have sh2 : GzShape (freeMsg h s) (rstSt s) := by
    refine ⟨sh1.mode, sh1.path, sh1.strm, sh1.want_lo, sh1.want_hi, sh1.size,
      ⟨by rw [hsk]; decide, by rw [hpo, hsk]; decide, by rw [hpo]; decide, fun _ => by rw [hpo]; decide⟩,
      ⟨sh1.msg.msg, sh1.msg.mem⟩, fun _ => ⟨Or.inl rfl, fun hsz => ?_, fun _ => rfl, fun e => absurd rfl e, fun hz => (R.fresh hz).of_strm rfl⟩,
      fun e => absurd (hr.symm.trans e) read_ne_write, fun hz => sh1.dead hz⟩
    obtain ⟨c, base, z0, hb, hi, hz0, -, hai, hreg, hmsg⟩ := R.bufs hsz
    exact ⟨c, base, z0, ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩, hi, hz0, Or.inl rfl, hai, hreg, hmsg⟩
  have hz' : (freeMsg h s).streams (rstSt s).strm = some z := by rw [freeMsg_streams]; exact hz
  obtain ⟨sh3, e3⟩ := shape_avail0 (b := b) sh2 hr hz'
  have e4 : ownL (freeMsg h s) b (rstSt s) =
      ownL (freeMsg h s) b { s with eof := 0, past := 0, err := ZlibNg.Inflate.Z_OK, msg := .val .null } := by
    simp [ownL, rstSt, errSt, rst0, stBlk]
  have e3' : ownL (avail0 (freeMsg h s) s.strm z) b (rstSt s) = ownL (freeMsg h s) b (rstSt s) := e3
  exact ⟨sh3, by rw [e3', e4]; exact hn1⟩

theorem HLess.trans {a b c : Heap} (x : HLess a b) (y : HLess b c) : HLess a c := by
  refine ⟨fun c' d e => x.bytes c' d (y.bytes c' d e), fun i z e => ?_, by rw [y.istates, x.istates],
    by rw [y.iallocs, x.iallocs], by rw [y.dstates, x.dstates], by rw [y.dallocs, x.dallocs], by rw [y.crc, x.crc],
    by rw [y.x2n, x.x2n], by rw [y.next, x.next], by rw [y.base, x.base], by rw [y.hdr, x.hdr],
    fun k a e => y.consts k a (x.consts k a e)⟩
  obtain ⟨z1, e1⟩ := x.streams i z e
  exact y.streams i z1 e1

theorem HLess.av0 (h : Heap) (i : Nat) (z : ZStream) : HLess h (avail0 h i z) := by
  refine ⟨fun _ _ e => e, fun j z' e => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
  by_cases hj : j = i
  · subst hj; exact ⟨{ z with avail_in := 0 }, by simp [avail0]⟩
  · exact ⟨z', by simp only [avail0]; rw [upd_ne _ _ _ _ hj]; exact e⟩

/-! ## `gzrewind` -/

/-- What `gzrewind` of a read handle does: nothing (an error is pending), an `lseek` that fails, or an `lseek` and
`gz_reset`. -/
theorem gzrewind_read {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hs : w.gz h b = some s)
    (hr : s.mode = GZ_READ) (hm : GzMsg h s) (hn : (ownL h b s).Nodup) (hz : h.streams s.strm = some z) :
    GzRun (gzrewind (some b)) w h (-1) w h ∨
    (∃ fs', GzOpen.FsLe w.fs fs' ∧ GzRun (gzrewind (some b)) w h (-1) { w with fs := fs' } h) ∨
    (∃ fs', GzOpen.FsLe w.fs fs' ∧ GzRun (gzrewind (some b)) w h 0
      { w with fs := fs', gzs := upd w.gzs b (some (rstSt s)) } (avail0 (freeMsg h s) s.strm z)) := by
  by_cases he : s.err ≠ ZlibNg.Inflate.Z_OK ∧ s.err ≠ ZlibNg.Inflate.Z_BUF_ERROR
  · left
    simp [GzRun, C.run, StateT.run, gzrewind, rdG_app' hs, hr, he]
  · right
    generalize hL : w.fs.lseekCall s.fd s.start SEEK_SET = L
    obtain ⟨v, fs'⟩ := L
    have hle : GzOpen.FsLe w.fs fs' := by
      have := GzOpen.lseekCall_le w.fs s.fd s.start SEEK_SET; rw [hL] at this; exact this
    have hs' : ({ w with fs := fs' } : World).gz h b = some s := hs
    by_cases hv : v = -1
    · subst hv
      left
      refine ⟨fs', hle, ?_⟩
      simp [GzRun, C.run, StateT.run, gzrewind, rdG_app' hs, hr, he, lseekG, modifyFs, hL]
    · right
      refine ⟨fs', hle, ?_⟩
      have e := gz_reset_read hs' hr hm hn hz
      simp only [GzRun, C.run, StateT.run] at e
      simp [GzRun, C.run, StateT.run, gzrewind, rdG_app' hs, hr, he, lseekG, modifyFs, hL, hv, e]

theorem keepsR_fs {w : World} {h : Heap} {f : GzPtr} (hv : GzInvR w h f) {fs' : Fs} (hle : GzOpen.FsLe w.fs fs') :
    GzInvR { w with fs := fs' } h f :=
  (keeps_outside (S := fun w h w' h' _ => w' = { w with fs := fs' } ∧ h' = h ∧ GzOpen.FsLe w.fs fs')
    fun _ _ _ _ _ _ ⟨e1, e2, e3⟩ => ⟨by rw [e1], by rw [e1]; exact e3, Or.inl e2,
      fun l => LitOk.ext l (by rw [e1]) (by rw [e2]; exact fun _ _ e => e)⟩).1 _ _ _ _ _ hv ⟨rfl, rfl, hle⟩

theorem freeMsg_av0_bytes {h : Heap} {b : Nat} {s : GzState} (hn : (ownL h b s).Nodup) (i : Nat) (z : ZStream)
    (d : Array UInt8) (hd : h.bytes b = some d) : (avail0 (freeMsg h s) i z).bytes b = some d :=
  freeMsg_bytes_b hn hd

theorem rewind_keepsR : KeepsR SRewind := by
  intro w h w' h' f hv ⟨r, e⟩
  obtain ⟨b, s, rfl, hs, sh, hn⟩ := hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨z, hz⟩ := sh.strm
  rcases gzrewind_read hs hr sh.msg hn hz with e' | ⟨fs', hle, e'⟩ | ⟨fs', hle, e'⟩ <;>
    obtain ⟨-, e1, e2⟩ := gdet e e' <;> rw [e1, e2]
  · exact hv
  · exact keepsR_fs hv hle
  · obtain ⟨sh', hn'⟩ := reset_keep sh hr hn hz
    exact (keeps_store (w := { w with fs := fs' }) hs ((HLess.free h s).trans (HLess.av0 _ _ _))
      (freeMsg_av0_bytes hn _ _) sh' hn' rfl rfl).1 (keepsR_fs hv hle)

end ZlibNgF.Proof.GzMode
