import ZlibNgF.Proof.«gzread.c.ungetc»
import ZlibNgF.Proof.«gzread.c.readspec»
import ZlibNgF.Proof.«gzread.c.idlespec»

/-!
# `gzgetc` and `gzgetc_` on a read handle (`ZlibNgF`)

The fast path takes one byte of the output buffer (`x.have--`, `x.pos++`, `x.next++`): `x.pos + 1` does not overflow
because a read handle keeps `x.pos + x.have <= GZ_OFF_MAX` (patch 0013). Otherwise `gz_read` reads one byte into the
local array `buf[1]`, whose lifetime ends at the return.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

/-- A read handle is in the state `gz_skip` accepts. -/
theorem mid_of {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b)) (hs : W.gz H b = some s) :
    GzMid W H b s := by
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have P := sh.pos
  refine ⟨hs, ?_, hout_self R, R.pos_have, R.look_pos⟩
  have := invR_seek hv hs 0 s.next s.pos s.skip s.how R.how P.1 P.2 P.3 (Or.inl rfl) (fun _ => rfl) R.look
    (by have := R.pos_have; simp; omega) (fun h1 h2 => by have := R.look_pos h1 h2; simp; omega) R.gzip_direct R.copy_in
  have es : ({ s with «have» := 0, next := s.next, pos := s.pos, skip := s.skip, how := s.how } : GzState) =
      { s with «have» := 0 } := by cases s; rfl
  rwa [es] at this

/-! ## New output count, next pointer, position and `past` -/

/-- A read handle keeps its fields when only `x.have`, `x.next`, `x.pos` and `past` change, with the positions in
range and the output inside the `out` buffer. -/
theorem shape_hp {h : Heap} {s s' : GzState} (sh : GzShape h s) (hr : s.mode = GZ_READ)
    (e : s' = { s with «have» := s'.«have», next := s'.next, pos := s'.pos, past := s'.past })
    (hp : -GZ_OFF_MAX.toInt ≤ s'.pos.toInt) (hpk : s'.pos.toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt)
    (hout : s'.«have» = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs h s c base →
      ∃ q, s'.next = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q s'.«have».toNat))
    (hsk : s.skip ≠ 0 → s'.pos.toInt + s.skip.toInt + s'.«have».toNat ≤ GZ_OFF_MAX.toInt)
    (hph : s'.pos.toInt + s'.«have».toNat ≤ GZ_OFF_MAX.toInt)
    (hlk : s.how = LOOK → s.direct ≠ 0 → s'.pos.toInt + s'.«have».toNat ≤ 0) : GzShape h s' := by
  have R := sh.read hr
  have P := sh.pos
  rw [e]
  refine ⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, sh.size,
    ⟨P.1, hpk, hp, fun e' => absurd (hr.symm.trans e') read_ne_write⟩, ⟨sh.msg.msg, sh.msg.mem⟩,
    fun _ => ⟨R.how, fun hsz => ?_, fun hsz => ?_, hsk, fun hz => (R.fresh hz).of_strm rfl, R.look, hph, hlk,
      R.gzip_direct, R.copy_in⟩, fun e' => absurd (hr.symm.trans e') read_ne_write, fun hz => sh.dead hz⟩
  · obtain ⟨c, base, z, hb, hi, hz, -, hai, hreg, hmsg⟩ := R.bufs hsz
    refine ⟨c, base, z, ⟨hb.size, hb.buffers, hb.inp, hb.out, hb.fits, hb.hdr⟩, hi, hz, ?_, hai, hreg, hmsg⟩
    rcases hout with e' | ⟨-, hq⟩
    · exact Or.inl e'
    · exact Or.inr (hq c base hb)
  · rcases hout with e' | ⟨e', -⟩
    · exact e'
    · exact absurd hsz e'

/-- The read invariant after such a store, and a step of the call. -/
theorem invR_hp {w : World} {h : Heap} {b : Nat} {s s' : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s)
    (e : s' = { s with «have» := s'.«have», next := s'.next, pos := s'.pos, past := s'.past })
    (hp : -GZ_OFF_MAX.toInt ≤ s'.pos.toInt) (hpk : s'.pos.toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt)
    (hout : s'.«have» = 0 ∨ (s.size ≠ 0 ∧ ∀ c base, GzBufs h s c base →
      ∃ q, s'.next = .val q ∧ Inside c base (inSize s) (inSize s + outSize s) q s'.«have».toNat))
    (hsk : s.skip ≠ 0 → s'.pos.toInt + s.skip.toInt + s'.«have».toNat ≤ GZ_OFF_MAX.toInt)
    (hph : s'.pos.toInt + s'.«have».toNat ≤ GZ_OFF_MAX.toInt)
    (hlk : s.how = LOOK → s.direct ≠ 0 → s'.pos.toInt + s'.«have».toNat ≤ 0) :
    GzInvR { w with gzs := upd w.gzs b (some s') } h (some b) ∧ GStep w h { w with gzs := upd w.gzs b (some s') } h b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have sh' := shape_hp sh hr e hp hpk hout hsk hph hlk
  have hn' : (ownL h b s').Nodup := by rw [e]; exact hn
  refine ⟨(keeps_store hs (HLess.refl h) (fun _ e' => e') sh' hn' (by rw [e]) (by rw [e])).1 hv, ?_⟩
  exact gstep_st hs w.fs (by rw [e]) (by rw [e]) (by rw [e]) (by rw [e])

/-! ## Owned blocks, the local array and its end -/

/-- Every block of a read handle is below `h.nextBlk`. -/
theorem owned_lt {w : World} {h : Heap} {b : Nat} (hv : GzInvR w h (some b)) :
    ∀ c ∈ GzOwned w h (some b), c < h.nextBlk := by
  obtain ⟨⟨b0, s, e0, hs, sh, hn⟩, hm, hw⟩ := hv
  cases e0
  have hr := modeOf hs hm
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hL : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_live sh hr ⟨db, hdb⟩ c hc)
  intro c hc
  simp only [GzOwned, hs, List.mem_append] at hc
  by_cases hz : s.size = 0
  · rcases hc with (((h1 | h2) | h3) | h4) | h5
    · simp at h1; subst h1; exact hL c (by simp [ownL])
    · exact hL c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr (by unfold blkOf; split at h2 <;> simp_all))))
    · exact hL c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr (by unfold blkOf; split at h3 <;> simp_all)))
    · exact (sh.dead hz c (by simp only [List.mem_append]; exact Or.inl (by unfold blkOf; split at h4 <;> simp_all))).2
    · exact (sh.dead hz c (by simp only [List.mem_append]; exact Or.inr (by unfold stBlk; exact h5))).2
  · refine hL c ?_
    simp only [ownL, hz, ite_false, List.mem_append]
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr (by unfold blkOf; split at h2 <;> simp_all)))
    · exact Or.inl (Or.inr (by unfold blkOf; split at h3 <;> simp_all))
    · exact Or.inr (Or.inl (by unfold blkOf; split at h4 <;> simp_all))
    · exact Or.inr (Or.inr (by unfold stBlk; exact h5))

/-- The heap after `localBlock n`. -/
def localArr (h : Heap) (n : Nat) : Array UInt8 :=
  Array.ofFn (n := n) (fun i => Junk.of (h.garbage (2 ^ 41 + h.nextBlk) i.val))

def localH (h : Heap) (n : Nat) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some (localArr h n)), nextBlk := h.nextBlk + 1 }

theorem localBlock_app (h : Heap) (n : Nat) : localBlock n h = .ok (.ref (.heap h.nextBlk) 0, localH h n) := rfl

theorem HExt.localB (h : Heap) (n : Nat) : HExt h (localH h n) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, by simp [localH], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ e => e⟩
  · have hne : c ≠ h.nextBlk := by omega
    simp [localH, upd_ne _ _ _ _ hne]
  · have hne : c ≠ h.nextBlk := by simp [localH] at hc; omega
    simp [localH, upd_ne _ _ _ _ hne]

/-- A frame where only blocks from `h.nextBlk` on are written writes no caller range. -/
theorem GStep.fresh_writes {w W : World} {h H : Heap} {b : Nat} {wr : List (BPtr × Nat)}
    (g : GStep w h W H b wr) (hw : ∀ x ∈ wr, ∀ c off, x.1 = .ref (.heap c) off → h.nextBlk ≤ c) :
    GStep w h W H b [] := by
  obtain ⟨⟨⟨f1, f2⟩, c, gz⟩, o, t⟩ := g
  refine ⟨⟨⟨?_, f2⟩, c, gz⟩, o, t⟩
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f1
  refine ⟨s1, g1, i1, fun c' hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩
  obtain ⟨d2, f2, s2, q2⟩ := b1 c' hc hn data hd
  exact ⟨d2, f2, s2, fun j hj _ => q2 j hj fun x hx off he => absurd (hw x hx c' off he) (by omega)⟩

theorem gz_free_ne {W : World} {H : Heap} {b c : Nat} (hbc : b ≠ c) :
    W.gz { H with bytes := upd H.bytes c none } b = W.gz H b := by
  unfold World.gz; simp [upd_ne _ _ _ _ hbc]

theorem owned_free_ne {W : World} {H : Heap} {b c : Nat} (hbc : b ≠ c) :
    GzOwned W { H with bytes := upd H.bytes c none } (some b) = GzOwned W H (some b) := by
  simp only [GzOwned, gz_free_ne hbc]

/-- Freeing a block from `h.nextBlk` on keeps a step of a call. -/
theorem GStep.free_new {w W : World} {h H : Heap} {b c : Nat} {wr : List (BPtr × Nat)}
    (g : GStep w h W H b wr) (hc : h.nextBlk ≤ c) (hbn : b < h.nextBlk) :
    GStep w h W { H with bytes := upd H.bytes c none } b wr := by
  have hbc : b ≠ c := by omega
  obtain ⟨⟨⟨⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩, f2⟩, cc, gz⟩, o, t⟩ := g
  refine ⟨⟨⟨⟨s1, g1, i1, fun c' hc' hn data hd => ?_, fun c' hc' hn hd => ?_, c1, r1, x1, a1, k1⟩, f2⟩, cc, gz⟩,
    fun c' hc' hlt => o c' (by rw [owned_free_ne hbc] at hc'; exact hc') hlt, fun s s' e1 e2 => t s s' e1 (by rw [gz_free_ne hbc] at e2; exact e2)⟩
  · have hne : c' ≠ c := by omega
    obtain ⟨d2, f2', s2, q2⟩ := b1 c' hc' hn data hd
    exact ⟨d2, by simp only [upd_ne _ _ _ _ hne]; exact f2', s2, q2⟩
  · have hne : c' ≠ c := by omega
    simp only [upd_ne _ _ _ _ hne]; exact n1 c' hc' hn hd

/-- Freeing a block that is not the file's keeps a read handle. -/
theorem invR_free {W : World} {H : Heap} {b c : Nat} (hv : GzInvR W H (some b)) (hc : c ∉ GzOwned W H (some b)) :
    GzInvR W { H with bytes := upd H.bytes c none } (some b) := by
  obtain ⟨⟨b0, s, e0, hs, sh, hn⟩, hm, hw⟩ := hv
  cases e0
  have hL : ∀ c' ∈ ownL H b s, c' ≠ c := fun c' h1 e => hc (e ▸ ownL_owned hs c' h1)
  have hbc : b ≠ c := hL b (by simp [ownL])
  have hk : HK H { H with bytes := upd H.bytes c none } s (ownL H b s) :=
    ⟨rfl, fun c' h1 => by simp [upd_ne _ _ _ _ (hL c' h1)], fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, Nat.le_refl _, fun _ c' _ e _ => by
        by_cases e' : c' = c
        · subst e'; simp
        · simp [upd_ne _ _ _ _ e']; exact e, fun _ _ => rfl⟩
  obtain ⟨sh', eo⟩ := shape_keep sh hk
  have hl : HLess H { H with bytes := upd H.bytes c none } := by
    refine ⟨fun c' d e => ?_, fun _ z e => ⟨z, e⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
    by_cases e' : c' = c
    · subst e'; simp at e
    · simpa [upd_ne _ _ _ _ e'] using e
  have := (keeps_store hs hl (fun d e => by simp [upd_ne _ _ _ _ hbc]; exact e) sh' (by rw [eo]; exact hn) rfl rfl).1
    ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩
  rwa [DeflateReset.upd_self W.gzs b s (gzs_of hs)] at this

/-- `LookIdle` after a store of a state with the same `how`, `direct` and stream. -/
theorem idle_upd {w : World} {h : Heap} {b : Nat} {s : GzState} (hi : LookIdle w h (some b))
    (hs : w.gz h b = some s) (s' : GzState) (e1 : s'.how = s.how) (e2 : s'.direct = s.direct)
    (e3 : s'.strm = s.strm) : LookIdle { w with gzs := upd w.gzs b (some s') } h (some b) :=
  idle_same hi hs (gz_upd_same hs s') e1 e2 e3 rfl

/-- `LookIdle` after freeing a block other than the state's. -/
theorem idle_free {W : World} {H : Heap} {b c : Nat} (hi : LookIdle W H (some b)) (hbc : b ≠ c) :
    LookIdle W { H with bytes := upd H.bytes c none } (some b) := by
  intro b' s z e hs hz
  cases e
  rw [gz_free_ne hbc] at hs
  exact hi b s z rfl hs hz

/-! ## `gzgetc` -/

/-- **`gzgetc`** on a read handle with `LookIdle`: a read handle with `LookIdle` again, and a step of the call that
writes no caller memory. -/
theorem gzgetc_read (RS : GzReadSpec) (RI : GzReadIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) :
    GSat w h (gzgetc (some b))
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b []) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  have P := sh.pos
  have hmx := gzmax
  obtain ⟨db, hdb⟩ := gz_live hs
  have done : GSat w h (pure (-1 : Int32))
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b []) :=
    GSat.pure ⟨hv, hi, GStep.refl w h b []⟩
  unfold gzgetc
  apply GSat.ite
  · intro _; exact done
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact done
  intro _
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hh0
    have hh : s.«have» ≠ 0 := by simpa using hh0
    have hsz : s.size ≠ 0 := fun e => hh (R.nobuf e)
    obtain ⟨c, base, z, hb, -, -, hhv, -, -⟩ := R.bufs hsz
    obtain ⟨p, hp, k, hpk, hlo, hhi⟩ := hhv.resolve_left hh
    obtain ⟨d, hd, hds⟩ := hb.fits
    have h1 : 1 ≤ s.«have».toNat := by
      have : s.«have».toNat ≠ 0 := fun e => hh (UInt32.toNat_inj.mp (by simpa using e))
      omega
    have hhm : (s.«have» - 1).toNat = s.«have».toNat - 1 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using h1)]; simp
    have hph := R.pos_have
    have hb1 : -(2 ^ 63 : Int) ≤ s.pos.toInt + 1 ∧ s.pos.toInt + 1 < 2 ^ 63 := by
      have := P.3; constructor <;> omega
    let s1 : GzState := { s with «have» := s.«have» - 1 }
    refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
    refine GSat.bind (GSat.of_eq (rdG_upd hdb w s1 _) ?_)
    refine GSat.bind (GSat.lm ⟨_, h, chkI64_ok hb1.1 hb1.2 h, ?_⟩)
    refine GSat.bind (GSat.of_eq (wrG_upd hdb w s1 _) ?_)
    refine GSat.bind (GSat.of_eq (ldGz_upd hdb w _) ?_)
    refine GSat.bind (GSat.lm ⟨p, h, by show Ival.get s.next h = _; rw [hp]; rfl, ?_⟩)
    rw [hpk]
    have hlt : base + k < d.size := by omega
    refine GSat.bind (GSat.lm ⟨_, h, addH hd (off := base + k) 1 (by omega), ?_⟩)
    refine GSat.bind (GSat.of_eq (wrG_upd hdb w _ _) ?_)
    obtain ⟨v, ev⟩ := load8_heap hd hlt
    refine GSat.bind (GSat.lm ⟨v, h, ev, ?_⟩)
    refine GSat.pure ?_
    simp only [InflateInv.upd_upd]
    have e2 := toInt_ofInt' hb1.1 hb1.2
    refine and_left_comm.mp ⟨idle_upd hi hs _ rfl rfl rfl, ?_⟩
    refine invR_hp hv hs rfl (by rw [e2]; have := P.3; omega) ?_ ?_ ?_ ?_ ?_
    · show (Int64.ofInt (s.pos.toInt + 1)).toInt + s.skip.toInt ≤ GZ_OFF_MAX.toInt
      rw [e2]
      by_cases hk : s.skip = 0
      · rw [hk]; simp; omega
      · have := R.skip_have hk; omega
    · refine Or.inr ⟨hsz, fun c' base' hb' => ?_⟩
      have e1 := hb'.buffers; rw [hb.buffers] at e1; cases e1
      refine ⟨_, rfl, k + 1, by show Ptr.ref (BRef.heap c) (base + k + 1) = _; rw [Nat.add_assoc], by omega, ?_⟩
      show k + 1 + (s.«have» - 1).toNat ≤ _; rw [hhm]; omega
    · intro hk
      show (Int64.ofInt (s.pos.toInt + 1)).toInt + s.skip.toInt + ((s.«have» - 1).toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [e2, hhm]; have := R.skip_have hk; omega
    · show (Int64.ofInt (s.pos.toInt + 1)).toInt + ((s.«have» - 1).toNat : Int) ≤ GZ_OFF_MAX.toInt
      rw [e2, hhm]; omega
    · intro hL hD
      show (Int64.ofInt (s.pos.toInt + 1)).toInt + ((s.«have» - 1).toNat : Int) ≤ 0
      rw [e2, hhm]; have := R.look_pos hL hD; omega
  · intro _
    have hext := HExt.localB h 1
    obtain ⟨hs1, hv1, g1⟩ := ext_step hv hs rfl rfl hext (LitOk.ext hv.2.2.lit rfl fun _ _ e => e)
    have ho : GzOwned w (localH h 1) (some b) = GzOwned w h (some b) := by simp only [GzOwned, hs1, hs]; rfl
    have hnb : h.nextBlk ∉ GzOwned w h (some b) := fun m => by have := owned_lt hv _ m; omega
    have hbn : b < h.nextBlk := owned_lt hv b (by simp [GzOwned, hs])
    refine GSat.bind (GSat.lm ⟨_, localH h 1, localBlock_app h 1, ?_⟩)
    have hout : GzOut w (localH h 1) (some b) (.ref (.heap h.nextBlk) 0) (1 : UInt64).toNat := by
      refine Or.inr ⟨⟨h.nextBlk, 0, localArr h 1, rfl, by simp [localH], by simp [localArr]⟩, fun c hc off e => ?_⟩
      cases e
      rw [ho] at hc
      exact hnb hc
    have hi1 : LookIdle w (localH h 1) (some b) := idle_same hi hs hs1 rfl rfl rfl rfl
    refine GSat.bind (GSat.mono (GSat.withRun (RS w (localH h 1) b _ 1 hv1 hout)) fun r W H q => ?_)
    obtain ⟨⟨-, hvW, gW, -⟩, run⟩ := q
    have hiW := RI w (localH h 1) b _ 1 r W H hv1 hi1 hout run
    have hl : h.nextBlk < (localH h 1).nextBlk := by simp [localH]
    have hno : h.nextBlk ∉ GzOwned w (localH h 1) (some b) := by rw [ho]; exact hnb
    obtain ⟨a, ha, hasz⟩ := frame_live gW.frame.1.1 hl hno (d := localArr h 1) (by simp [localH])
    have ha' : H.bytes h.nextBlk = some a := ha
    have hasz' : 0 < a.size := by rw [hasz]; simp [localArr]
    have hnW : h.nextBlk ∉ GzOwned W H (some b) := fun m => hno (gW.own _ m hl)
    have g2 : GStep w h W H b [] := by
      refine ((GzDecomp.GStep.widen g1 _).trans gW ⟨s, hs⟩ ⟨s, hs1⟩).fresh_writes ?_
      intro x hx c off e
      simp at hx; subst hx; cases e; exact Nat.le_refl _
    have T : ∀ r' : Int32, GSat W H (do lm (dropLocal (Ptr.ref (BRef.heap h.nextBlk) 0)); pure r')
        (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b []) := by
      intro r'
      refine GSat.bind (GSat.lm ⟨(), { H with bytes := upd H.bytes h.nextBlk none }, by simp [dropLocal, ha'], ?_⟩)
      exact GSat.pure ⟨invR_free hvW hnW, idle_free hiW (by omega), g2.free_new (Nat.le_refl _) hbn⟩
    dsimp only
    apply GSat.ite
    · intro _; exact GSat.bind (GSat.pure (T (-1)))
    · intro _
      refine GSat.bind (GSat.lm ⟨_, H, index8_heap 0 ha' (by simpa using hasz'), ?_⟩)
      exact GSat.bind (GSat.pure (T _))

/-- `gzgetc_` is `gzgetc`. -/
theorem gzgetc__read (RS : GzReadSpec) (RI : GzReadIdle) {w : World} {h : Heap} {b : Nat}
    (hv : GzInvR w h (some b)) (hi : LookIdle w h (some b)) :
    GSat w h (gzgetc_ (some b))
      (fun _ W H => GzInvR W H (some b) ∧ LookIdle W H (some b) ∧ GStep w h W H b []) :=
  gzgetc_read RS RI hv hi

theorem getc_keepsRI (RS : GzReadSpec) (RI : GzReadIdle) : KeepsRI SGetc := by
  intro w h w' h' f hv hi ⟨r, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzgetc_read RS RI hv hi).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

theorem getc__keepsRI (RS : GzReadSpec) (RI : GzReadIdle) : KeepsRI SGetc_ := by
  intro w h w' h' f hv hi ⟨r, e⟩
  obtain ⟨b, s, rfl, -, -, -⟩ := hv.1
  obtain ⟨r2, W, H, e2, q⟩ := (gzgetc__read RS RI hv hi).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact ⟨q.1, q.2.1⟩

end ZlibNgF.Proof.GzMode
