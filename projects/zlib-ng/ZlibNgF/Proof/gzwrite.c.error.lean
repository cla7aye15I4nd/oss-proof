import ZlibNgF.Proof.«gzlib.c.error»

/-!
# `gz_error` on a write handle (`ZlibNgF`)

`gz_error_invW`: as `gz_error_inv` for read handles. The blocks of a write handle are live (`ownL_liveW`): its
state, `path`, `msg`, and with buffers the buffer block and, when not direct, the block of the deflate state (a
direct file has no deflate state, `GzWBuf.nostate`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat

theorem wfw_ext {w W : World} {h h' : Heap} {b : Nat} {s : GzState} (hw : GzWFw w h) (hs : w.gz h b = some s)
    (hg : ∀ c, c ≠ b → W.gzs c = w.gzs c) (hgb : ∀ s', W.gzs b = some s' → s'.strm = s.strm)
    (x : HExt h h') (hL : LitOk W h') : GzWFw W h' := by
  obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hst, -⟩ := hw
  obtain ⟨d0, hd0⟩ := gz_live hs
  refine ⟨⟨by rw [x.crc]; exact hc.1, by rw [x.x2n]; exact hc.2⟩, ⟨x.fresh hfr, fun c e => ?_⟩, fun c e => ?_,
    fun c s2 e => ?_, hL⟩
  · rw [x.dstates, x.dallocs]; exact hdf c (Nat.le_trans x.next e)
  · have hbn : b < h.nextBlk := by
      refine Nat.lt_of_not_le fun e => ?_
      rw [(hfr b e).2.2] at hd0; cases hd0
    rw [hg c (by have := x.next; omega)]; exact hgz c (Nat.le_trans x.next e)
  · unfold World.gz at e
    split at e
    · next d hd =>
      by_cases hcb : c = b
      · subst hcb; rw [hgb s2 e, x.streams]; exact hst c s hs
      · rw [hg c hcb] at e
        by_cases hlt : c < h.nextBlk
        · rw [(x.old c hlt).1] at hd
          obtain ⟨z, hz⟩ := hst c s2 (by unfold World.gz; rw [hd]; exact e)
          exact ⟨z, by rw [x.streams]; exact hz⟩
        · rw [hgz c (by omega)] at e; cases e
    · cases e

/-- The blocks of a write handle are live. -/
theorem ownL_liveW {h : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hw : s.mode = GZ_WRITE)
    (hb : ∃ d, h.bytes b = some d) : ∀ c ∈ ownL h b s, ∃ d, h.bytes c = some d := by
  intro c hc
  unfold ownL at hc
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with ((rfl | hc) | hc) | hc
  · exact hb
  · obtain ⟨c', n, e, r, off, d, e1, e2, -⟩ := sh.path
    rw [e] at hc; simp [blkOf] at hc; subst hc; cases e1; exact ⟨d, e2⟩
  · rcases sh.msg.msg with e | ⟨c', d, e, hd⟩
    · rw [e] at hc; simp [blkOf] at hc
    · rw [e] at hc; simp [blkOf] at hc; subst hc; exact ⟨d, hd⟩
  · split at hc
    · simp at hc
    · next hsz =>
      obtain ⟨c0, base, z, hbf, hz, W⟩ := (sh.write hw).bufs hsz
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · rw [hbf.buffers] at hc; simp [blkOf] at hc; subst hc
        obtain ⟨d, hd, -⟩ := hbf.fits; exact ⟨d, hd⟩
      · by_cases hdir : s.direct = 0
        · obtain ⟨i, z0, sb, st, al, e, hz0, hsb, hst, -, -⟩ := (W.deflate hdir).1
          cases e; rw [hz] at hz0; cases hz0
          simp [stBlk, hz, hsb] at hc; subst hc
          unfold Heap.dstate at hst; split at hst
          · next d hd => exact ⟨d, hd⟩
          · cases hst
        · simp [stBlk, hz, W.nostate hdir] at hc

/-- **`gz_error` on a write handle** (as `gz_error_inv`). -/
theorem gz_error_invW {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ W H => ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧
      GzInvWS W H (some b) ∧ W.fs = w.fs ∧ GStep w h W H b []) := by
  have hlit : LitOk w h := hv.2.2.lit
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hwm := modeOf hs hm
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hn hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, hn1⟩ := err0_keep sh hn e
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, mv, ev, hgz, hsW, hfs, x, hlW, hMN⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  rw [freeMsg_next] at hMN
  have hw1 : (errSt s e).mode = GZ_WRITE := hwm
  have hlt : ∀ c ∈ ownL (freeMsg h s) b (errSt s e), c < h.nextBlk := fun c hc => by
    rw [← freeMsg_next h s]; exact live_lt fr1 (ownL_liveW sh1 hw1 ⟨db, hdb1⟩ c hc)
  have hk := HK_ext x (errSt s e) _ (by rw [freeMsg_next]; exact hlt)
  obtain ⟨shH, eH⟩ := shape_keep sh1 hk
  have hnH : (ownL H b (errSt s e)).Nodup := by rw [eH]; exact hn1
  let s' : GzState := { errSt s e with msg := mv, err := ev }
  have hmsgH : GzMsg H s' := by
    refine ⟨?_, hMN.1⟩
    rcases hMN.2.2 with e' | ⟨c, e', -, d, hd⟩
    · exact Or.inl e'
    · exact Or.inr ⟨c, d, e', hd⟩
  have shS : GzShape H s' := shape_congr shH ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hmsgH
  have hnS : (ownL H b s').Nodup := by
    rcases hMN.2.2 with e' | ⟨c, e', hc, -⟩
    · have : ownL H b s' = ownL H b (errSt s e) := by simp [ownL, s', e', errSt, stBlk]
      rw [this]; exact hnH
    · have : ownL H b s' = ownL H b { errSt s e with msg := .val (.ref (.heap c) 0) } := by simp [ownL, s', e', stBlk]
      rw [this]
      refine ownL_msg hnH rfl c fun m => ?_
      rw [eH] at m
      have := hlt c m; omega
  have hgb : ∀ s2, W.gzs b = some s2 → s2.strm = (errSt s e).strm := by
    intro s2 e2; rw [gzs_of hsW] at e2; cases e2; rfl
  have wf1 : GzWFw { w with gzs := upd w.gzs b (some (errSt s e)) } (freeMsg h s) :=
    wfw_step hw hs (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp at e2; rw [← e2]; rfl)
      (HLess.free h s) (LitOk.ext hlit rfl (HLess.free h s).consts)
  have wfW : GzWFw W H := wfw_ext wf1 hs1 hgz hgb x hlW
  have hstH : H.streams = h.streams := x.streams.trans (freeMsg_streams h s)
  refine ⟨r, W, H, by rw [gz_error_run hs sh.msg (msg_ne_b hn) e msg]; exact eq, s', hsW, ⟨rfl, hMN.2.1⟩,
    ⟨⟨b, s', rfl, hsW, shS, hnS⟩, ⟨b, s', rfl, hsW, hwm⟩, wfW⟩, hfs, ?_⟩
  refine gstep_mk hs hsW rfl (fun c hc _ => by rw [hgz c hc]; simp [upd_ne _ _ _ _ hc])
    (fun i _ => by rw [hstH]) (x.hdr.trans (HLess.free h s).hdr) (fun c hc hno => ?_)
    (fun k a e' => x.consts k a (by rw [freeMsg_consts]; exact e')) (x.crc.trans (HLess.free h s).crc)
    (x.x2n.trans (HLess.free h s).x2n) (x.base.trans (HLess.free h s).base)
    (by have := x.next; rw [freeMsg_next] at this; exact this) (fun c hc hlt' => ?_)
  · have hc' : c < (freeMsg h s).nextBlk := by rw [freeMsg_next]; exact hc
    refine ⟨by rw [(x.old c hc').1]; exact freeMsg_bytes h s c fun hm' => hno (ownL_owned hs c (by unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm'))), ?_, ?_, ?_, ?_⟩
    · rw [x.istates, (HLess.free h s).istates]
    · rw [x.iallocs, (HLess.free h s).iallocs]
    · rw [x.dstates, (HLess.free h s).dstates]
    · rw [x.dallocs, (HLess.free h s).dallocs]
  · simp only [GzOwned, hsW, hs, List.mem_append, hstH] at hc ⊢
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exfalso
      rcases hMN.2.2 with e' | ⟨c', e', hc', -⟩
      · simp [s', e'] at h3
      · simp [s', e'] at h3; omega
    · exact Or.inl (Or.inr h4)
    · exact Or.inr h5

end ZlibNgF.Proof.GzMode
