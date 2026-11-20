import ZlibNgF.Proof.«gzwrite.c.calls»
import ZlibNgF.Proof.«gzread.c.getc»

/-!
# `gzputc` (`ZlibNgF`)

`gzputc_spec`: on a write handle, `gzputc` keeps the invariant `GzInvWS` and is a step of the file, given
`GzCompSpec` and `DeflateGz`. With buffers, room in the first `size` bytes of `in` and `x.pos != GZ_OFF_MAX` (patch
0014), the byte goes into `in` (`putc_fast`); otherwise it goes into a local one-byte array and through `gz_write`
(`putc_local`), and the array is dropped again.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- Every block of a write handle is below `h.nextBlk`. -/
theorem owned_ltW {w : World} {h : Heap} {b : Nat} (hv : GzInvWS w h (some b)) :
    ∀ c ∈ GzOwned w h (some b), c < h.nextBlk := by
  obtain ⟨⟨b0, s, e0, hs, sh, hn⟩, hm, hw⟩ := hv
  cases e0
  have hr := modeOf hs hm
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hL : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_liveW sh hr ⟨db, hdb⟩ c hc)
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

/-- Freeing a block that is not the file's keeps a write handle. -/
theorem invWS_free {W : World} {H : Heap} {b c : Nat} (hv : GzInvWS W H (some b)) (hc : c ∉ GzOwned W H (some b)) :
    GzInvWS W { H with bytes := upd H.bytes c none } (some b) := by
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
  have := (keeps_store hs hl (fun d e => by simp [upd_ne _ _ _ _ hbc]; exact e) sh' (by rw [eo]; exact hn) rfl rfl).2
    ⟨⟨b, s, rfl, hs, sh, hn⟩, hm, hw⟩
  rwa [DeflateReset.upd_self W.gzs b s (gzs_of hs)] at this

/-- A heap with one more block, of any bytes. -/
theorem HExt.newB (h : Heap) (a : Array UInt8) :
    HExt h { h with bytes := upd h.bytes h.nextBlk (some a), nextBlk := h.nextBlk + 1 } := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
  · have hne : c ≠ h.nextBlk := by omega
    simp [upd_ne _ _ _ _ hne]
  · have hne : c ≠ h.nextBlk := by simp at hc; omega
    simp [upd_ne _ _ _ _ hne]

/-! ## The local array -/

/-- The tail of `gzputc` through a local array (copied from the translation). -/
def putcLocal (state : GzPtr) (c : Int32) : G Int32 := do
  let buf ← lm (localBlock 1)
  lm (store8 (← lm (buf.add 0)) c.toUInt32.toUInt8)
  let r ← if (← gz_write state buf 1) != 1 then pure (-1) else pure (c &&& 0xff)
  lm (dropLocal buf)
  return r

theorem putc_local (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (hs0 : ∃ s0, w.gz h b = some s0)
    (c : Int32) : GSat W H (putcLocal (some b) c) (CallPost w h b) := by
  unfold putcLocal
  have hbn : b < H.nextBlk := owned_ltW hv b (by simp [GzOwned, hs])
  have hnb : H.nextBlk ∉ GzOwned W H (some b) := fun m => by have := owned_ltW hv _ m; omega
  refine GSat.bind (GSat.lm ⟨_, localH H 1, localBlock_app H 1, ?_⟩)
  have hla : (localH H 1).bytes H.nextBlk = some (localArr H 1) := by simp [localH]
  have hsz1 : (localArr H 1).size = 1 := by simp [localArr]
  refine GSat.bind (GSat.lm ⟨_, localH H 1, padd_ok (r := BRef.heap H.nextBlk) (off := 0)
    (hla : Space.get (localH H 1) (BRef.heap H.nextBlk) = some (localArr H 1)) 0 (by omega), ?_⟩)
  have hst := store8_heap hla (off := 0 + 0) (by omega) c.toUInt32.toUInt8
  generalize ha2 : (localArr H 1).set! 0 c.toUInt32.toUInt8 = a2
  have hH2 : ({ localH H 1 with
        bytes := (localH H 1).bytes.modify H.nextBlk (Option.map (fun a' => a'.set! (0 + 0) c.toUInt32.toUInt8)) } :
        Heap) = { H with bytes := upd H.bytes H.nextBlk (some a2), nextBlk := H.nextBlk + 1 } := by
    rw [Tbl.modify_opt _ _ _ _ hla, ← ha2]
    simp [localH, InflateInv.upd_upd]
  rw [hH2] at hst
  refine GSat.bind (GSat.lm ⟨(), _, hst, ?_⟩)
  have hsz2 : a2.size = 1 := by rw [← ha2]; simp [hsz1]
  obtain ⟨hv2, hs2, g2⟩ := invWS_ext hv hs (HExt.newB H a2) rfl (LitOk.ext hv.2.2.lit rfl fun _ _ e => e)
  have ho2 : GzOwned W { H with bytes := upd H.bytes H.nextBlk (some a2), nextBlk := H.nextBlk + 1 } (some b) =
      GzOwned W H (some b) := by simp only [GzOwned, hs2, hs]
  have hin : GzIn W { H with bytes := upd H.bytes H.nextBlk (some a2), nextBlk := H.nextBlk + 1 } (some b)
      (.ref (.heap H.nextBlk) 0) (1 : UInt64).toNat := by
    refine Or.inr ⟨⟨.heap H.nextBlk, 0, a2, rfl, by show (upd H.bytes H.nextBlk (some a2)) H.nextBlk = _; simp,
      by simp [hsz2]⟩, fun c' hc off e => ?_⟩
    cases e
    rw [ho2] at hc
    exact hnb hc
  refine GSat.bind (GSat.mono (gz_write_spec C G hv2 hs2 _ 1 hin) fun r W3 H3 q => ?_)
  obtain ⟨s3, -, hv3, g3, -⟩ := q
  have hl : H.nextBlk < ({ H with bytes := upd H.bytes H.nextBlk (some a2), nextBlk := H.nextBlk + 1 } : Heap).nextBlk := by
    simp
  have hno : H.nextBlk ∉ GzOwned W { H with bytes := upd H.bytes H.nextBlk (some a2), nextBlk := H.nextBlk + 1 }
      (some b) := by rw [ho2]; exact hnb
  obtain ⟨a3, ha3, -⟩ := GzDecomp.frame_live g3.frame.1.1 hl hno (d := a2) (by simp)
  have hnW : H.nextBlk ∉ GzOwned W3 H3 (some b) := fun m => hno (g3.own _ m hl)
  have g23 : GStep W H W3 H3 b [] := g2.trans g3 ⟨s1, hs⟩ ⟨s1, hs2⟩
  have T : ∀ r' : Int32, GSat W3 H3 (do lm (dropLocal (Ptr.ref (BRef.heap H.nextBlk) 0)); pure r') (CallPost w h b) := by
    intro r'
    refine GSat.bind (GSat.lm ⟨(), { H3 with bytes := upd H3.bytes H.nextBlk none }, by simp [dropLocal, ha3], ?_⟩)
    exact GSat.pure ⟨invWS_free hv3 hnW, g.trans (g23.free_new (Nat.le_refl _) hbn) hs0 ⟨s1, hs⟩⟩
  exact GSat.ite (fun _ => GSat.bind (GSat.pure (T _))) (fun _ => GSat.bind (GSat.pure (T _)))

/-! ## The byte into `in` -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gzputc` with buffers, after `next_in` is set (copied from the translation). -/
def putcFast (state : GzPtr) (strm : StreamPtr) (c : Int32) : G Int32 := do
  let e ← lm ((← lm (rdZ strm (·.next_in))).add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
  let d ← lm (Ptr.diff e (← (← ldGz state).«in».get))
  let hv : UInt32 := d.toUInt64.toUInt32
  if hv < (← rdG state (·.size)) && (← rdG state (·.pos)) != GZ_OFF_MAX then
    lm (store8 (← lm ((← (← ldGz state).«in».get).add (Int.ofNat hv.toNat))) c.toUInt32.toUInt8)
    lm (wrZ strm fun z => { z with avail_in := z.avail_in + 1 })
    let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + 1))
    wrG state fun st => { st with pos := np }
    return c &&& 0xff
  putcLocal state c

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gzputc` after the pending seek (copied from the translation). -/
def putcRest (state : GzPtr) (strm : StreamPtr) (c : Int32) : G Int32 := do
  if (← rdG state (·.size)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) == 0 then
      let i ← (← ldGz state).«in».get
      lm (wrZ strm fun z => { z with next_in := i })
    putcFast state strm c
  else
    putcLocal state c

theorem gzputc_eq (b : Nat) (c : Int32) : gzputc (some b) c = (do
    let strm ← strmOf (some b)
    if (← rdG (some b) (·.mode)) != GZ_WRITE || (← rdG (some b) (·.err)) != ZlibNg.Inflate.Z_OK then
      return -1
    if (← rdG (some b) (·.skip)) != 0 then
      if (← gz_zero (some b)) == -1 then
        return -1
    putcRest (some b) strm c) := rfl

theorem putc_fast (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    {z : ZStream} {c0 base k : Nat} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b [])
    (hs0 : ∃ s0, w.gz h b = some s0) (zf : ZFix s s1) (hsk : s1.skip = 0) (hsz : s1.size ≠ 0)
    (hB : GzBufs H s1 c0 base) (hz : H.streams s.strm = some z) (hk : z.next_in = .ref (.heap c0) (base + k))
    (hka : k + z.avail_in.toNat ≤ s1.size.toNat) (c : Int32) :
    GSat W H (putcFast (some b) (some s.strm) c) (CallPost w h b) := by
  have hstrm : s1.strm = s.strm := zf.strm
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hP := sh.pos
  have hpw := hP.write_pos hwm
  have hps := hP.pos_skip
  have hsk0 : s1.skip.toInt = 0 := by rw [hsk]; rfl
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hw30 := sh.want_hi
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  have hg : Space.get H (BRef.heap c0) = some d := hd
  unfold putcFast
  refine GSat.bind (GSat.of_eq (a := z.next_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  rw [hk]
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c0) (base + k + z.avail_in.toNat)) (w' := W) (h' := H)
    (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (((base + k + z.avail_in.toNat : Nat) : Int) - base)) (w' := W)
    (h' := H) (by rw [lm_app, pdiff_ok hd (by omega) (by omega) (by omega)]) ?_)
  have ehv : (Int64.ofInt (((base + k + z.avail_in.toNat : Nat) : Int) - base)).toUInt64.toUInt32.toNat =
      k + z.avail_in.toNat := by
    have : (((base + k + z.avail_in.toNat : Nat) : Int) - base) = ((k + z.avail_in.toNat : Nat) : Int) := by omega
    rw [this]; exact diff_u32 _ (by omega)
  generalize (Int64.ofInt (((base + k + z.avail_in.toNat : Nat) : Int) - base)).toUInt64.toUInt32 = hvv at ehv
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hc => ?_) (fun _ => putc_local C G hv hs g hs0 c)
  have hc' : hvv < s1.size ∧ s1.pos ≠ GZ_OFF_MAX := by simpa using hc
  have hlt : k + z.avail_in.toNat < s1.size.toNat := by rw [← ehv]; exact UInt32.lt_iff_toNat_lt.mp hc'.1
  have hpne : s1.pos.toInt ≠ GZ_OFF_MAX.toInt := fun e => hc'.2 (Int64.toInt_inj.mp e)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  rw [ehv]
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c0) (base + (k + z.avail_in.toNat))) (w' := W) (h' := H)
    (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
  have hst := store8_heap hd (off := base + (k + z.avail_in.toNat)) (by omega) c.toUInt32.toUInt8
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (by rw [lm_app, hst]) ?_)
  have x2 := HBuf.store8 hd (lo := base + (k + z.avail_in.toNat)) (hi := base + (k + z.avail_in.toNat) + 1)
    (Nat.le_refl _) (by omega) c.toUInt32.toUInt8
  obtain ⟨hcb, hpth, hstb, hown⟩ := bufBlk hs hn hsz hB
  obtain ⟨hv2, hs2, g2⟩ := invWS_hbuf hv hs x2 hcb hpth hstb hown
  generalize ({ H with bytes := H.bytes.modify c0 (Option.map fun a' => a'.set! (base + (k + z.avail_in.toNat))
    c.toUInt32.toUInt8) } : Heap) = H2 at hv2 hs2 g2 x2 ⊢
  have hz2 : H2.streams s1.strm = some z := by obtain ⟨t, e, -⟩ := x2; rw [e, hstrm]; exact hz
  have hai : (z.avail_in + 1).toNat = z.avail_in.toNat + 1 := by
    rw [UInt32.toNat_add]; simp; omega
  obtain ⟨hv3, hs3, g3⟩ := invWS_setIn hv2 hs2 hsz hz2 z.next_in (z.avail_in + 1) (fun c' base' hb' => by
    have e := hb'.buffers; rw [hB.buffers] at e; cases e
    exact Or.inl ⟨k, hk, Nat.zero_le _, by rw [hai]; omega⟩)
  rw [hstrm] at hv3 hs3 g3 hz2
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
    (h' := setZ H2 s.strm { z with next_in := z.next_in, avail_in := z.avail_in + 1 })
    (by simp [lm_app, wrZ_run hz2]) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.pos.toInt + 1))
    (by simp only [lm_app, chkI64_ok (v := s1.pos.toInt + 1) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app hs3 _) ?_)
  have hp1 : (Int64.ofInt (s1.pos.toInt + 1)).toInt = s1.pos.toInt + 1 :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  obtain ⟨sh3, hn3⟩ := inv_of hs3 hv3.1
  have sh4 := shape_posW sh3 hwm (Int64.ofInt (s1.pos.toInt + 1)) s1.skip
    ⟨by dsimp only; omega, by dsimp only; rw [hp1]; omega, by dsimp only; rw [hp1]; omega,
      fun _ => by dsimp only; rw [hp1]; omega⟩
  obtain ⟨hv4, hs4, g4⟩ := invWS_store hv3 hs3 sh4 hn3 hwm rfl (fun c' hc _ => by
    simp only [GzOwned, gz_upd_same hs3, hs3] at hc ⊢; exact hc)
  exact GSat.pure ⟨hv4, ((g.trans g2 hs0 ⟨s1, hs⟩).trans g3 hs0 ⟨s1, hs2⟩).trans g4 hs0 ⟨s1, hs3⟩⟩

theorem putc_rest (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (hs0 : ∃ s0, w.gz h b = some s0)
    (zf : ZFix s s1) (hsk : s1.skip = 0) (c : Int32) :
    GSat W H (putcRest (some b) (some s.strm) c) (CallPost w h b) := by
  have hstrm : s1.strm = s.strm := zf.strm
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  unfold putcRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hsz0 => ?_) (fun _ => putc_local C G hv hs g hs0 c)
  have hsz : s1.size ≠ 0 := by simpa using hsz0
  obtain ⟨c0, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  rw [hstrm] at hz
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.ite (fun hai => ?_) (fun hai => ?_)
  · have hai0 : z.avail_in = 0 := by simpa using hai
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    rw [hB.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    obtain ⟨hv1, hs1, g1⟩ := invWS_setIn hv hs hsz (by rw [hstrm]; exact hz) (.ref (.heap c0) base) z.avail_in
      (fun c' base' hb => by
        have e := hb.buffers; rw [hB.buffers] at e; cases e
        exact Or.inl ⟨0, by simp, Nat.le_refl _, by rw [hai0]; simp⟩)
    rw [hstrm] at hv1 hs1 g1
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
      (h' := setZ H s.strm { z with next_in := .ref (.heap c0) base, avail_in := z.avail_in })
      (by simp [lm_app, wrZ_run hz]) ?_)
    have hB1 : GzBufs (setZ H s.strm { z with next_in := .ref (.heap c0) base, avail_in := z.avail_in }) s1 c0 base :=
      ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩
    exact putc_fast C G hv1 hs1 (g.trans g1 hs0 ⟨s1, hs⟩) hs0 zf hsk hsz hB1 (setZ_streams_same _ _ _) (k := 0)
      (by simp) (by rw [hai0]; simp) c
  · have hai0 : z.avail_in ≠ 0 := by simpa using hai
    rcases WB.inp with ⟨k, ek, -, hk⟩ | ⟨e1, -⟩
    · exact putc_fast C G hv hs g hs0 zf hsk hsz hB hz ek hk c
    · exact absurd e1 hai0

/-- **`gzputc`** on a write handle. -/
theorem gzputc_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (c : Int32) :
    GSat w h (gzputc (some b) c) (CallPost w h b) := by
  rw [gzputc_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hk => ?_)
    (fun hk => putc_rest C G hv hs (GStep.refl w h b []) ⟨s, hs⟩ (ZFix.refl s) (by simpa using hk) c)
  refine GSat.bind (GSat.mono (gz_zero_spec C G hv hs (by simpa using hk)) fun rz W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2, zf2, hrz, hok⟩ := q
  refine GSat.ite (fun _ => GSat.pure ⟨hv2, g2⟩) (fun hne => ?_)
  have hr0 : rz = 0 := by rcases hrz with e | e; exact e; simp [e] at hne
  exact putc_rest C G hv2 hs2 g2 ⟨s, hs⟩ zf2 (hok hr0).1 c

end ZlibNgF.Proof.GzWrite
