import ZlibNgF.Proof.«gzwrite.c.flat»

/-!
# `gz_error` on a write handle in the state `GzWX` (`ZlibNgF`)

`gz_error` does not touch the streams: run on the actual heap, the invariant of the flat heap carries over
(`gz_error_invX`, as `gz_error_invW`), and so do `gz_error(state, Z_ERRNO, strerror(errno))` (`gz_error_strX`) and
`gz_error` with a literal (`gz_error_litX`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

theorem freeMsg_setZ (h : Heap) (s : GzState) (i : Nat) (z : ZStream) :
    freeMsg (setZ h i z) s = setZ (freeMsg h s) i z := by
  unfold freeMsg; split <;> (try split) <;> rfl

theorem hext_setZ {h H : Heap} (x : HExt h H) (i : Nat) (z : ZStream) : HExt (setZ h i z) (setZ H i z) :=
  ⟨x.old, x.beyond, x.next, by simp only [setZ, x.streams], x.istates, x.iallocs, x.dstates, x.dallocs, x.crc, x.x2n,
    x.base, x.hdr, x.consts⟩

theorem ownL_setZ (h : Heap) (b : Nat) {s : GzState} {z z' : ZStream} (hz : h.streams s.strm = some z)
    (hst : z'.state = z.state) : ownL (setZ h s.strm z') b s = ownL h b s := by
  simp [ownL, stBlk, hz, hst]

/-- **`gz_error` on a write handle in the state `GzWX`**, run on the actual heap: the invariant of the flat heap. -/
theorem gz_error_invX {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ W H => ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧
      GzInvWS W (setZ H s.strm (flatZ za)) (some b) ∧ W.fs = w.fs ∧ H.streams = h.streams ∧
      GStep w (setZ h s.strm (flatZ za)) W (setZ H s.strm (flatZ za)) b []) := by
  have hlit : LitOk w h := hv.2.2.lit
  have hsF : w.gz (setZ h s.strm (flatZ za)) b = some s := hs
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hsF] at hs0; cases hs0
  have hwm := modeOf hsF hm
  have hoF : ownL (setZ h s.strm (flatZ za)) b s = ownL h b s := ownL_setZ h b hz rfl
  have hnA : (ownL h b s).Nodup := hoF ▸ hn
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hnA hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, hn1⟩ := err0_keep sh hn e
  rw [freeMsg_setZ] at sh1 hn1
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, mv, ev, hgz, hsW, hfs, x, hlW, hMN⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  rw [freeMsg_next] at hMN
  have hstH : H.streams = h.streams := x.streams.trans (freeMsg_streams h s)
  -- the flat heaps
  have x' := hext_setZ x s.strm (flatZ za)
  have hsWF : W.gz (setZ H s.strm (flatZ za)) b = some { errSt s e with msg := mv, err := ev } := hsW
  have hzH : H.streams s.strm = some za := by rw [hstH]; exact hz
  have hw1 : (errSt s e).mode = GZ_WRITE := hwm
  have hdbF : (setZ (freeMsg h s) s.strm (flatZ za)).bytes b = some db := hdb1
  have hlt : ∀ c ∈ ownL (setZ (freeMsg h s) s.strm (flatZ za)) b (errSt s e), c < h.nextBlk := fun c hc => by
    rw [← freeMsg_next h s]; exact live_lt fr1 (ownL_liveW sh1 hw1 ⟨db, hdbF⟩ c hc)
  have hk := HK_ext x' (errSt s e) (ownL (setZ (freeMsg h s) s.strm (flatZ za)) b (errSt s e))
    (fun c hc => by have := hlt c hc; rw [← freeMsg_next h s] at this; exact this)
  obtain ⟨shH, eH⟩ := shape_keep sh1 hk
  have hnH : (ownL (setZ H s.strm (flatZ za)) b (errSt s e)).Nodup := by rw [eH]; exact hn1
  let s' : GzState := { errSt s e with msg := mv, err := ev }
  have hmsgH : GzMsg (setZ H s.strm (flatZ za)) s' := by
    refine ⟨?_, hMN.1⟩
    rcases hMN.2.2 with e' | ⟨c, e', -, d, hd⟩
    · exact Or.inl e'
    · exact Or.inr ⟨c, d, e', hd⟩
  have shS : GzShape (setZ H s.strm (flatZ za)) s' :=
    shape_congr shH ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hmsgH
  have hnS : (ownL (setZ H s.strm (flatZ za)) b s').Nodup := by
    rcases hMN.2.2 with e' | ⟨c, e', hc, -⟩
    · have : ownL (setZ H s.strm (flatZ za)) b s' = ownL (setZ H s.strm (flatZ za)) b (errSt s e) := by
        simp [ownL, s', e', errSt, stBlk]
      rw [this]; exact hnH
    · have : ownL (setZ H s.strm (flatZ za)) b s' =
          ownL (setZ H s.strm (flatZ za)) b { errSt s e with msg := .val (.ref (.heap c) 0) } := by
        simp [ownL, s', e', stBlk]
      rw [this]
      refine ownL_msg hnH rfl c fun m => ?_
      rw [eH] at m
      have := hlt c m; omega
  have hgb : ∀ s2, W.gzs b = some s2 → s2.strm = (errSt s e).strm := by
    intro s2 e2; rw [gzs_of hsW] at e2; cases e2; rfl
  have wf1 : GzWFw { w with gzs := upd w.gzs b (some (errSt s e)) } (setZ (freeMsg h s) s.strm (flatZ za)) := by
    rw [← freeMsg_setZ]
    exact wfw_step hw hsF (fun c hc => by simp [upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp at e2; rw [← e2]; rfl)
      (HLess.free _ s) (LitOk.ext hw.lit rfl (HLess.free _ s).consts)
  have wfW : GzWFw W (setZ H s.strm (flatZ za)) := wfw_ext wf1 hs1 hgz hgb x' hlW
  refine ⟨r, W, H, by rw [gz_error_run hs (by obtain ⟨⟩ := sh.msg; constructor <;> assumption) (msg_ne_b hnA) e msg]; exact eq, s', hsW, ⟨rfl, hMN.2.1⟩,
    ⟨⟨b, s', rfl, hsWF, shS, hnS⟩, ⟨b, s', rfl, hsWF, hwm⟩, wfW⟩, hfs, hstH, ?_⟩
  have hxH : (setZ H s.strm (flatZ za)).streams = (setZ h s.strm (flatZ za)).streams := by
    show upd H.streams _ _ = upd h.streams _ _; rw [hstH]
  have hsMF : HLess (setZ h s.strm (flatZ za)) (freeMsg (setZ h s.strm (flatZ za)) s) := HLess.free _ s
  rw [freeMsg_setZ] at hsMF
  have hcF : (setZ (freeMsg h s) s.strm (flatZ za)).consts = h.consts := freeMsg_consts h s
  have hnF : (setZ (freeMsg h s) s.strm (flatZ za)).nextBlk = h.nextBlk := freeMsg_next h s
  refine gstep_mk hsF hsWF rfl (fun c hc _ => by rw [hgz c hc]; simp [upd_ne _ _ _ _ hc])
    (fun i _ => by rw [hxH]) (x'.hdr.trans hsMF.hdr) (fun c hc hno => ?_)
    (fun k a e' => x'.consts k a (by rw [hcF]; exact e')) (x'.crc.trans hsMF.crc)
    (x'.x2n.trans hsMF.x2n) (x'.base.trans hsMF.base)
    (by have := x'.next; rw [hnF] at this; exact this) (fun c hc hlt' => ?_)
  · have hc' : c < (setZ (freeMsg h s) s.strm (flatZ za)).nextBlk := by
      show c < (freeMsg h s).nextBlk; rw [freeMsg_next]; exact hc
    refine ⟨by rw [(x'.old c hc').1]; exact freeMsg_bytes h s c fun hm' => hno (ownL_owned hsF c (by
      rw [hoF]; unfold ownL; simp only [List.mem_append]; exact Or.inl (Or.inr hm'))), ?_, ?_, ?_, ?_⟩
    · rw [x'.istates, hsMF.istates]
    · rw [x'.iallocs, hsMF.iallocs]
    · rw [x'.dstates, hsMF.dstates]
    · rw [x'.dallocs, hsMF.dallocs]
  · simp only [GzOwned, hsWF, hsF, List.mem_append, hxH] at hc ⊢
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exfalso
      rcases hMN.2.2 with e' | ⟨c', e', hc', -⟩
      · simp [s', e'] at h3
      · simp [s', e'] at h3
        have : (setZ h s.strm (flatZ za)).nextBlk = h.nextBlk := rfl
        omega
    · exact Or.inl (Or.inr h4)
    · exact Or.inr (by simpa [errSt, hstH] using h5)

/-- What `gz_error` leaves on a write handle in the state `GzWX` (flat heaps). -/
def ErrPostX (w : World) (h : Heap) (b : Nat) (s : GzState) (za : ZStream) (e : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧ GzInvWS W (setZ H s.strm (flatZ za)) (some b) ∧ W.fs = w.fs ∧
    H.streams = h.streams ∧ GStep w (setZ h s.strm (flatZ za)) W (setZ H s.strm (flatZ za)) b []

/-- A heap that grows by static strings keeps the flat invariant. -/
theorem invX_ext {w : World} {h H : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b)) (hs : w.gz h b = some s) (x : HExt h H)
    (hL : LitOk w H) :
    GzInvWS w (setZ H s.strm (flatZ za)) (some b) ∧ w.gz H b = some s ∧
      GStep w (setZ h s.strm (flatZ za)) w (setZ H s.strm (flatZ za)) b [] := by
  obtain ⟨v, e, g⟩ := invWS_ext hv (show w.gz (setZ h s.strm (flatZ za)) b = some s from hs) (hext_setZ x s.strm (flatZ za)) rfl hL
  exact ⟨v, e, g⟩

/-- `gz_error(state, Z_ERRNO, zstrerror())` on a write handle in the state `GzWX`. -/
theorem gz_error_strX {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) Z_ERRNO (← zstrerror); pure r)
      (fun r' W H => r' = r ∧ ErrPostX w h b s za Z_ERRNO W H) := by
  obtain ⟨p, a, e, hc, hk⟩ := zstrerror_spec w h
  refine GSat.bind ⟨p, w, _, e, ?_⟩
  have x := HExt.lit h a
  obtain ⟨hv1, hs1, st1⟩ := invX_ext hv hs x (LitOk.ext hv.2.2.lit rfl x.consts)
  refine GSat.bind (GSat.mono (gz_error_invX (by rw [x.streams]; exact hz) hv1 hs1 _ p (Or.inr hc) hk)
    fun _ W H q => ?_)
  obtain ⟨s', hs', he, hv', hf', hst', st2⟩ := q
  exact GSat.pure ⟨rfl, s', hs', he, hv', hf', hst'.trans x.streams, st1.trans st2 ⟨s, hs⟩ ⟨s, hs1⟩⟩

/-- `gz_error(state, e, lit)` with a literal of the table on a write handle in the state `GzWX`. -/
theorem gz_error_litX (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hl : gzLits[i]? = some lit) (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState} {za : ZStream}
    (hz : h.streams s.strm = some za) (hv : GzInvWS w (setZ h s.strm (flatZ za)) (some b))
    (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r) (fun r' W H => r' = r ∧ ErrPostX w h b s za e W H) := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, hf, x, hL, hc, hk⟩ := q
  obtain ⟨v1, e1, g1⟩ := invWS_ext hv (show w.gz (setZ h s.strm (flatZ za)) b = some s from hs) (hext_setZ x s.strm (flatZ za)) hg (by exact hL)
  have hs1 : W1.gz H1 b = some s := e1
  refine GSat.bind (GSat.mono (gz_error_invX (by rw [x.streams]; exact hz) v1 hs1 e p (Or.inr ⟨_, hc⟩) hk)
    fun _ W H q => ?_)
  obtain ⟨s', hs', he, hv', hf', hst', st2⟩ := q
  exact GSat.pure ⟨rfl, s', hs', he, hv', by rw [hf', hf], hst'.trans x.streams,
    g1.trans st2 ⟨s, hs⟩ ⟨s, hs1⟩⟩

end ZlibNgF.Proof.GzWrite
