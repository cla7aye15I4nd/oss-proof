import ZlibNgF.Proof.«gzwrite.c.error»
import ZlibNgF.Proof.«gzwrite.c.needs»

/-!
# `gz_write_init` (`ZlibNgF`)

`gz_write_init_spec`: on a write handle without buffers, `gz_write_init` returns, keeps the invariant `GzInvWS`, is a
step of the file (`GStep`), leaves the file system and the fields of `WFix` alone, and returns `0` with the buffers
made or `-1`. Its paths: `gz_buffer_alloc` fails (`gz_error` twice); direct mode (no deflate state); `deflateInit2_`
fails (`gz_buffer_free`, `gz_error`); `deflateInit2_` succeeds (the deflate invariant, `DSide` and the buffer
pointers of `GzWBuf`). The deflate facts beyond `deflateInit2_`'s own proofs come from `DeflateGz`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode

/-- `gz_buffer_alloc` on a write handle when the allocation fails: the buffers stay absent and `gz_error` reports
`Z_MEM_ERROR`. -/
theorem gz_buffer_alloc_failW {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (hwm : s.mode = GZ_WRITE) (hok : h.allocOk h.nalloc = false) :
    gz_buffer_alloc (some b) w h =
      (do gz_error (some b) ZlibNg.Inflate.Z_MEM_ERROR (← gzLit "out of memory"); pure (-1 : Int32))
        { w with gzs := upd w.gzs b (some (bfSt s)) } { h with nalloc := h.nalloc + 1 } := by
  obtain ⟨d, hd⟩ := gz_live hs
  have hdA : ({ h with nalloc := h.nalloc + 1 } : Heap).bytes b = some d := hd
  have hsA : w.gz { h with nalloc := h.nalloc + 1 } b = some s := by
    unfold World.gz at hs ⊢; rw [hdA]; rw [hd] at hs; exact hs
  have hal : ∀ n : UInt32, ZlibNg.Zutil.zng_alloc_aligned n 64 h = .ok (.null, { h with nalloc := h.nalloc + 1 }) := by
    intro n; simp [ZlibNg.Zutil.zng_alloc_aligned, allocB, hok]
  by_cases hdir : s.direct = 0 <;>
  simp [gz_buffer_alloc, rdG_app' hs, hdir, lm_app, hwm, GZ_READ, GZ_WRITE, hal, wrG_app hsA, ldGz_upd hdA, wrG_upd hdA,
    rdG_upd hdA, Ival.get, liftM, monadLift, MonadLift.monadLift, gz_buffer_free, ZlibNg.Zutil.zng_free_aligned,
    InflateInv.upd_upd, bfSt]

/-- A write handle stays one, with the same state, across a heap that grows by fresh blocks and static strings and a
world with the same `gz_state` objects. -/
theorem invWS_ext {w W : World} {h H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (x : HExt h H) (hg : W.gzs = w.gzs) (hL : LitOk W H) :
    GzInvWS W H (some b) ∧ W.gz H b = some s ∧ GStep w h W H b [] := by
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, hm, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have hwm := modeOf hs hm
  obtain ⟨d, hd⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hbn : b < h.nextBlk := live_lt fr ⟨d, hd⟩
  have hsW : W.gz H b = some s := by
    unfold World.gz at hs ⊢; rw [(x.old b hbn).1, hd, hg]; rw [hd] at hs; exact hs
  have hlt : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_liveW sh hwm ⟨d, hd⟩ c hc)
  obtain ⟨shH, eH⟩ := shape_keep sh (HK_ext x s _ hlt)
  have wf : GzWFw W H := wfw_ext hw hs (fun c _ => by rw [hg])
    (fun s' e => by rw [hg, gzs_of hs] at e; cases e; rfl) x hL
  refine ⟨⟨⟨b, s, rfl, hsW, shH, by rw [eH]; exact hn⟩, ⟨b, s, rfl, hsW, hwm⟩, wf⟩, hsW, ?_⟩
  refine gstep_mk hs hsW rfl (fun c _ _ => by rw [hg]) (fun i _ => by rw [x.streams]) x.hdr
    (fun c hc _ => ⟨(x.old c hc).1, by rw [x.istates], by rw [x.iallocs], by rw [x.dstates], by rw [x.dallocs]⟩)
    x.consts x.crc x.x2n x.base x.next (fun c hc _ => ?_)
  simp only [GzOwned, hsW, hs, x.streams] at hc ⊢; exact hc

/-- What `gz_error(state, e, lit)` with a literal of the table does on a write handle. -/
def ErrPost (w : World) (h : Heap) (b : Nat) (s : GzState) (e : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧ GzInvWS W H (some b) ∧ W.fs = w.fs ∧ GStep w h W H b []

theorem gz_error_litW (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hl : gzLits[i]? = some lit) (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r) (fun r' W H => r' = r ∧ ErrPost w h b s e W H) := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, hf, x, hL, hc, hk⟩ := q
  obtain ⟨hv1, hs1, st1⟩ := invWS_ext hv hs x hg hL
  refine GSat.bind (GSat.mono (gz_error_invW hv1 hs1 e p (Or.inr ⟨_, hc⟩) hk) fun _ W H q => ?_)
  obtain ⟨s', hs', he, hv', hf', st2⟩ := q
  exact GSat.pure ⟨rfl, s', hs', he, hv', by rw [hf', hf], st1.trans st2 ⟨s, hs⟩ ⟨s, hs1⟩⟩

/-- A store of a state `s'` with the invariant into a write handle. -/
theorem invWS_store {w : World} {h : Heap} {b : Nat} {s s' : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (sh' : GzShape h s') (hn' : (ownL h b s').Nodup) (hm : s'.mode = GZ_WRITE)
    (hstrm : s'.strm = s.strm)
    (hown : ∀ c ∈ GzOwned { w with gzs := upd w.gzs b (some s') } h (some b), c < h.nextBlk →
      c ∈ GzOwned w h (some b)) :
    GzInvWS { w with gzs := upd w.gzs b (some s') } h (some b) ∧
      ({ w with gzs := upd w.gzs b (some s') } : World).gz h b = some s' ∧
      GStep w h { w with gzs := upd w.gzs b (some s') } h b [] := by
  have hsW := gz_upd_same hs s'
  refine ⟨⟨⟨b, s', rfl, hsW, sh', hn'⟩, ⟨b, s', rfl, hsW, hm⟩, wfw_store hv.2.2 hs s' hstrm⟩, hsW, ?_⟩
  exact gstep_mk hs hsW hstrm (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) (fun _ _ => rfl) rfl
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _) hown

/-- The fields of a write handle without buffers after `gz_buffer_free`. -/
theorem shape_bfW {h : Heap} {b : Nat} {s : GzState} (sh : GzShape h s) (hwm : s.mode = GZ_WRITE)
    (hz : s.size = 0) : GzShape h (bfSt s) ∧ ownL h b (bfSt s) = ownL h b s := by
  have Wr := sh.write hwm
  refine ⟨⟨sh.mode, sh.path, sh.strm, sh.want_lo, sh.want_hi, Or.inl rfl, ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩, ⟨sh.msg.1, sh.msg.2⟩,
    fun hr => absurd (hwm.symm.trans hr) write_ne_read, fun _ => ⟨fun e => absurd rfl e, fun _ => Wr.nobuf hz,
    Wr.have0⟩, fun _ c hc => ?_⟩, by simp [ownL, bfSt, hz, stBlk]⟩
  simp only [bfSt, blkOf, List.nil_append] at hc
  exact sh.dead hz c (List.mem_append_right _ (by simpa [stBlk] using hc))

/-- After a failed allocation in `gz_buffer_alloc`, before its `gz_error`. -/
theorem invWS_bf {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) :
    GzInvWS { w with gzs := upd w.gzs b (some (bfSt s)) } { h with nalloc := h.nalloc + 1 } (some b) ∧
      ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz { h with nalloc := h.nalloc + 1 } b = some (bfSt s) ∧
      GStep w h { w with gzs := upd w.gzs b (some (bfSt s)) } { h with nalloc := h.nalloc + 1 } b [] := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh1, e1⟩ := shape_bfW (b := b) sh hwm hz
  obtain ⟨v1, s1, g1⟩ := invWS_store hv hs sh1 (by rw [e1]; exact hn) hwm rfl (fun c hc _ => by
    simp only [GzOwned, gz_upd_same hs, hs] at hc ⊢
    simp [bfSt] at hc ⊢
    rcases hc with h1 | h1 | h1 | h1 <;> simp [h1])
  have x : HExt h { h with nalloc := h.nalloc + 1 } :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ e => e⟩
  obtain ⟨v2, s2, g2⟩ := invWS_ext v1 s1 x rfl (LitOk.ext v1.2.2.lit rfl fun _ _ e => e)
  exact ⟨v2, s2, g1.trans g2 ⟨s, hs⟩ ⟨_, s1⟩⟩

theorem lit_oom_get : gzLits[0]? = some "out of memory" := by decide
theorem nonul_oom : NoNul "out of memory" := by decide

/-- `gz_buffer_alloc` on a write handle without buffers: it fails with `gz_error`, or allocates the block. -/
theorem gz_buffer_alloc_specW {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) :
    GSat w h (gz_buffer_alloc (some b)) (fun r W H =>
      (r = -1 ∧ ErrPost w h b (bfSt s) ZlibNg.Inflate.Z_MEM_ERROR W H) ∨
      (r = 0 ∧ h.allocOk h.nalloc = true ∧
        W = { w with gzs := upd w.gzs b (some (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk))))) } ∧
        H = alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk))))) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  cases hok : h.allocOk h.nalloc with
  | true =>
    have hfr : h.bytes h.nextBlk = none := (hv.2.2.2.1.1 h.nextBlk (Nat.le_refl _)).2.2
    exact ⟨_, _, _, gz_buffer_alloc_okW hs hwm sh.want_lo sh.want_hi hfr hok, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
  | false =>
    obtain ⟨v1, s1, g1⟩ := invWS_bf hv hs hz
    obtain ⟨r, W, H, e, rfl, s', h1, h2, h3, h4, g2⟩ :=
      gz_error_litW "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom v1 s1 ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)
    refine ⟨-1, W, H, by rw [gz_buffer_alloc_failW hs hwm hok]; exact e, Or.inl ⟨rfl, s', h1, h2, h3, h4, ?_⟩⟩
    exact g1.trans g2 ⟨s, hs⟩ ⟨_, s1⟩

theorem HExt.alloc_aligned (h : Heap) (n o : Nat) : HExt h (alH h n o) := by
  unfold alH
  refine ⟨fun c hc => ?_, fun c hc => ?_, Nat.le_succ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ _ e => e⟩
  · have hne : c ≠ h.nextBlk := by omega
    simp [upd_ne _ _ _ _ hne]
  · have hne : c ≠ h.nextBlk := by simp at hc; omega
    simp [upd_ne _ _ _ _ hne]

theorem baStW_size {s : GzState} (hlo : 8 ≤ s.want.toNat) (c o : Nat) : (baStW s c o).size ≠ 0 := by
  intro e; simp [baStW] at e; have := congrArg UInt32.toNat e; simp at this; omega

/-- After a successful `gz_buffer_alloc` on a direct write handle, the handle has its invariant. -/
theorem invWS_allocDirect {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) (hd : s.direct ≠ 0) :
    let o := alOff (h.baseAddr (.heap h.nextBlk))
    let W1 : World := { w with gzs := upd w.gzs b (some (baStW s h.nextBlk o)) }
    let H1 := alH h (8 + wBytes s + 64) o
    GzInvWS W1 H1 (some b) ∧ W1.gz H1 b = some (baStW s h.nextBlk o) ∧ GStep w h W1 H1 b [] := by
  intro o W1 H1
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have x : HExt h H1 := HExt.alloc_aligned h _ _
  obtain ⟨v0, hs0, -⟩ := invWS_ext hv hs x rfl (LitOk.ext hv.2.2.lit rfl x.consts)
  obtain ⟨shH, -⟩ := inv_of hs0 v0.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hv.2.2.2.1.1
  have hbn : b < h.nextBlk := live_lt fr ⟨db, hdb⟩
  have hdbH : H1.bytes b = some db := by rw [(x.old b hbn).1]; exact hdb
  have hsW : W1.gz H1 b = some (baStW s h.nextBlk o) := by
    unfold World.gz; rw [hdbH]; simp [W1]
  have Wr := shH.write hwm
  obtain ⟨z, hz0, hai, -, -, hns⟩ := Wr.nobuf hz
  have hst : z.state = none := hns hd
  have ho := alOff_bounds (h.baseAddr (.heap h.nextBlk))
  have hcH : H1.bytes h.nextBlk = some (Array.ofFn (n := 8 + wBytes s + 64)
      fun i => Junk.of (h.garbage h.nalloc i.val)) := by simp [H1, alH]
  have hsize := baStW_size sh.want_lo h.nextBlk o
  have hlt : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_liveW sh hwm ⟨db, hdb⟩ c hc)
  have hB : GzBufs H1 (baStW s h.nextBlk o) h.nextBlk o := by
    refine ⟨rfl, rfl, rfl, fun e => ?_, ⟨_, hcH, ?_⟩, ho.1, by simp [H1, alH]⟩
    · exfalso; apply e; simp [outSize, baStW, hwm, hd]
    · simp [inSize, outSize, baStW, hwm, hd, wBytes]; omega
  have hWB : GzWBuf H1 (baStW s h.nextBlk o) h.nextBlk o z := by
    refine ⟨fun e => absurd e hd, fun sb _ _ e _ => ?_, Or.inr ⟨hai, Or.inl hd⟩, fun _ => hst, fun e => absurd e hd⟩
    rw [hst] at e; cases e
  have shape : GzShape H1 (baStW s h.nextBlk o) := by
    refine ⟨shH.mode, shH.path, shH.strm, shH.want_lo, shH.want_hi, Or.inr rfl,
      ⟨shH.pos.1, shH.pos.2, shH.pos.3, shH.pos.4⟩, ⟨shH.msg.1, shH.msg.2⟩,
      fun hr => absurd (hwm.symm.trans hr) write_ne_read, fun _ => ⟨fun _ => ⟨h.nextBlk, o, z, hB, hz0, hWB⟩,
      fun e => absurd e hsize, Wr.have0⟩, fun e => absurd e hsize⟩
  have hnew : ownL H1 b (baStW s h.nextBlk o) = ownL h b s ++ [h.nextBlk] := by
    have hzh : h.streams s.strm = some z := by rw [← x.streams]; exact hz0
    have hw0 : ¬ s.want = 0 := fun e => hsize (by simp [baStW, e])
    simp [ownL, baStW, hz, hw0, stBlk, hz0, hzh, hst, blkOf]
  have hnd : (ownL H1 b (baStW s h.nextBlk o)).Nodup := by
    rw [hnew, List.nodup_append]
    exact ⟨hn, by simp, fun a ha c hc => by simp at hc; subst hc; have := hlt a ha; omega⟩
  refine ⟨⟨⟨b, _, rfl, hsW, shape, hnd⟩, ⟨b, _, rfl, hsW, hwm⟩, wfw_ext hv.2.2 hs
    (fun c hc => by simp [W1, upd_ne _ _ _ _ hc]) (fun s2 e2 => by simp [W1] at e2; rw [← e2]; rfl) x
    (LitOk.ext hv.2.2.lit rfl x.consts)⟩, hsW, ?_⟩
  refine gstep_mk hs hsW rfl (fun c hc _ => by simp [W1, upd_ne _ _ _ _ hc]) (fun i _ => by rw [x.streams]) x.hdr
    (fun c hc _ => ⟨(x.old c hc).1, by rw [x.istates], by rw [x.iallocs], by rw [x.dstates], by rw [x.dallocs]⟩)
    x.consts x.crc x.x2n x.base x.next (fun c hc hlt' => ?_)
  have hzh : h.streams s.strm = some z := by rw [← x.streams]; exact hz0
  simp only [GzOwned, hsW, hs, x.streams, hzh, hst] at hc ⊢
  simp [baStW] at hc ⊢
  rcases hc with h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · omega
  · simp [hzh, hst] at h1

/-- A block older than `h` that is not a library block and is not written keeps its bytes. -/
theorem frame_bytes_eq {h h' : Heap} {S L G : List Nat} (f : Frame h h' S L G []) {c : Nat} (hc : c < h.nextBlk)
    (hL : c ∉ L) : h'.bytes c = h.bytes c := by
  obtain ⟨-, -, -, hb, hn, -⟩ := f
  cases e : h.bytes c with
  | none => exact hn c hc hL e
  | some d =>
    obtain ⟨d', e', hsz, hq⟩ := hb c hc hL d e
    rw [e']; congr 1
    apply Array.ext hsz
    intro j h1 h2
    have := hq j h2 (fun w hw => by simp at hw)
    rwa [getElem!_pos d' j h1, getElem!_pos d j h2] at this

theorem strLit_version (h : Heap) : strLitRef "1.3.2.zlib-ng" h = .ok (.ref (.str 0) 0, h) := by
  have hf : strTable.findIdx? (· == "1.3.2.zlib-ng") = some 0 :=
    Array.findIdx?_eq_some_iff_getElem.mpr ⟨by decide, by decide, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  simp only [strLitRef, hf]

theorem version_ok (h : Heap) : VersionOk h (.ref (.str 0) 0) := by
  refine Or.inr ⟨.str 0, 0, _, rfl, rfl, ?_⟩
  simp [Heap.litBytes]

/-- `deflateInit2_` with the library's version string on a stream ready for it: no fault, the frame. -/
theorem init2__run (h : Heap) (s : StreamPtr) (level method wb ml strat size : Int32) (hfr : DFreshBlocks h)
    (hi : DInitReady h s) :
    ∃ r h', ZlibNg.Deflate.deflateInit2_ s level method wb ml strat (.ref (.str 0) 0) size h = .ok (r, h') ∧
      DFrame h h' (streamIds s) [] [] [] := by
  obtain ⟨c, hc⟩ := InflateInit.checkVer_ok h _ size (version_ok h)
  cases c
  · obtain ⟨r, h', e, f⟩ := DeflateInitPublic.init2_safe h s level method wb ml strat hfr hi
    exact ⟨r, h', by simp [ZlibNg.Deflate.deflateInit2_, bind_app, hc, e], f⟩
  · exact ⟨_, h, by simp [ZlibNg.Deflate.deflateInit2_, bind_app, hc]; rfl, DeflateInitPublic.dframe_refl h _ _ _ _⟩

/-- `gstep_mk` with the header table kept pointwise. -/
theorem gstep_mk' {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hstrm : s'.strm = s.strm)
    (hg : ∀ c, c ≠ b → c < h.nextBlk → W.gzs c = w.gzs c)
    (hstreams : ∀ i, i ≠ s.strm → H.streams i = h.streams i) (hhdr : ∀ k, H.gzheaders k = h.gzheaders k)
    (hobj : ∀ c, c < h.nextBlk → c ∉ GzOwned w h (some b) → H.bytes c = h.bytes c ∧ H.istates c = h.istates c ∧
      H.iallocs c = h.iallocs c ∧ H.dstates c = h.dstates c ∧ H.dallocs c = h.dallocs c)
    (hc : ∀ k a, h.consts k = some a → H.consts k = some a) (hcrc : H.crcTable = h.crcTable)
    (hx2n : H.x2nTable = h.x2nTable) (hbase : H.baseAddr = h.baseAddr) (hnext : h.nextBlk ≤ H.nextBlk)
    (hown : ∀ c ∈ GzOwned W H (some b), c < h.nextBlk → c ∈ GzOwned w h (some b)) : GStep w h W H b [] := by
  refine ⟨⟨⟨⟨fun i hi => ?_, fun k _ => by simp [hhdr], fun c hc' hn => ⟨(hobj c hc' hn).2.1, (hobj c hc' hn).2.2.1⟩,
    fun c hc' hn d hd => ⟨d, by simp only; rw [(hobj c hc' hn).1]; exact hd, rfl, fun _ _ _ => rfl⟩,
    fun c hc' hn hd => by simp only; rw [(hobj c hc' hn).1]; exact hd, rfl, hcrc, hx2n, hbase, hnext⟩,
    fun c hc' hn => ⟨(hobj c hc' hn).2.2.2.1, (hobj c hc' hn).2.2.2.2⟩⟩, hc, fun c hcb hlt => hg c
      (fun e => hcb (by rw [e])) hlt⟩, hown, fun s0 s2 e0 e2 => ?_⟩
  · simp only [hs, List.mem_singleton] at hi
    exact hstreams i hi
  · rw [hs] at e0; rw [hs'] at e2; cases e0; cases e2; exact hstrm

open ZlibNgF.Proof.GzWriteNeeds in
/-- After a successful `deflateInit2_` in `gz_write_init` and the stores that follow it, the write handle has its
invariant. `H2` is the heap after `deflateInit2_`, `z'` the stream there. -/
theorem invWS_initOk (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) (hd : s.direct = 0) {lv m wb ml st sz : Int32} {H2 : Heap}
    (e : ZlibNg.Deflate.deflateInit2_ (some s.strm) lv m wb ml st (.ref (.str 0) 0) sz
      (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) = .ok (ZlibNg.Inflate.Z_OK, H2)) :
    ∃ z', H2.streams s.strm = some z' ∧
      let o := alOff (h.baseAddr (.heap h.nextBlk))
      let p : BPtr := .ref (.heap h.nextBlk) (o + 2 * s.want.toNat)
      let s3 : GzState := { baStW s h.nextBlk o with next := .val p }
      let W3 : World := { w with gzs := upd w.gzs b (some s3) }
      let H3 : Heap := { H2 with streams := (upd H2.streams s.strm
        (some { z' with next_in := .null, avail_out := s.want, next_out := p })) }
      GzInvWS W3 H3 (some b) ∧ W3.gz H3 b = some s3 ∧ GStep w h W3 H3 b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  generalize ho : alOff (h.baseAddr (.heap h.nextBlk)) = o at e
  generalize hH1 : alH h (8 + wBytes s + 64) o = H1 at e
  have x : HExt h H1 := hH1 ▸ HExt.alloc_aligned h _ _
  have hn1 : H1.nextBlk = h.nextBlk + 1 := by rw [← hH1]; rfl
  have hfr0 := hv.2.2.2.1
  have fr : FreshBlocks h := hfr0.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbn : b < h.nextBlk := live_lt fr ⟨db, hdb⟩
  have hlt : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_liveW sh hwm ⟨db, hdb⟩ c hc)
  obtain ⟨z, hz0, hai, hza, hzf, -⟩ := (sh.write hwm).nobuf hz
  have hz1 : H1.streams s.strm = some z := by rw [x.streams]; exact hz0
  have hfr1 : DFreshBlocks H1 :=
    ⟨x.fresh fr, fun c e' => by rw [x.dstates, x.dallocs]; exact hfr0.2 c (by omega)⟩
  have hi1 : DInitReady H1 (some s.strm) := Or.inr ⟨z, ⟨s.strm, rfl, hz1⟩, hza, hzf⟩
  obtain ⟨r', H2', e', f⟩ := init2__run H1 (some s.strm) lv m wb ml st sz hfr1 hi1
  rw [e] at e'; cases e'
  have GI := G.1 H1 H2 (some s.strm) lv m wb ml st _ sz _ z ⟨s.strm, rfl, hz1⟩ hi1 hfr1 (by simpa [C.run] using e)
  obtain ⟨z', hst2, GI⟩ := GI
  obtain ⟨i', ei, hz2⟩ := hst2
  cases ei
  obtain ⟨ni, GI⟩ := GI
  obtain ⟨ai, GI⟩ := GI
  obtain ⟨_no, GI⟩ := GI
  obtain ⟨_ao, GI⟩ := GI
  obtain ⟨_fl, GI⟩ := GI
  obtain ⟨hk, hsb⟩ := GI
  obtain ⟨sb, hsb, hsbn⟩ := hsb rfl
  obtain ⟨hinv, hfo⟩ := DeflateInitPublic.init2__inv H1 H2 (some s.strm) lv m wb ml st _ sz hi1 (version_ok H1)
    (by simpa [C.run] using e)
  have hside := DeflateSide.side_fresh hinv hfo
  refine ⟨z', hz2, ?_⟩
  intro o' p s3 W3 H3
  have ho' : o' = o := by simp only [o']
  -- the heap after the stores
  have hold : ∀ c, c < h.nextBlk → H3.bytes c = h.bytes c := fun c hc => by
    show H2.bytes c = _
    rw [frame_bytes_eq f.1 (by omega) (List.not_mem_nil), (x.old c hc).1]
  have hcN : h.nextBlk < H1.nextBlk := by omega
  have hc3 : H3.bytes h.nextBlk = H1.bytes h.nextBlk := frame_bytes_eq f.1 hcN (List.not_mem_nil)
  have hcH1 : H1.bytes h.nextBlk = some (Array.ofFn (n := 8 + wBytes s + 64)
      fun i => Junk.of (h.garbage h.nalloc i.val)) := by rw [← hH1]; simp [alH]
  have hzst : ∀ c, z.state = some c → c < h.nextBlk ∧ h.bytes c = none := by
    intro c hc
    have := sh.dead hz c (List.mem_append_right _ (by simp [stBlk, hz0, hc]))
    exact ⟨this.2, this.1⟩
  have hsv : H3.savedPtrs h.nextBlk = some (o - 8, .ref (.heap h.nextBlk) 0) := by
    show H2.savedPtrs h.nextBlk = _
    rw [hk.1 h.nextBlk hcN (fun z0 ⟨i0, e0, hz0'⟩ e2 => by
      cases e0; rw [hz1] at hz0'; cases hz0'
      have := (hzst _ e2).1; omega)]
    rw [← hH1]; simp [alH]
  have hz3 : H3.streams s.strm = some { z' with next_in := .null, avail_out := s.want, next_out := p } := by
    simp [H3]
  have ho72 := alOff_bounds (h.baseAddr (.heap h.nextBlk))
  rw [ho] at ho72
  -- the deflate stream after the stores
  obtain ⟨i0, z0, sb0, st0, al0, e0, hz0', hsb0, hst0, hal0, core0⟩ := hinv
  cases e0; rw [hz2] at hz0'; cases hz0'; rw [hsb] at hsb0; cases hsb0
  have hcs : DCallerStep H2 H3 (some s.strm) :=
    ⟨s.strm, z', _, sb, st0, rfl, hz2, hz3, hsb, hst0, rfl, rfl, rfl, rfl,
      fun k g _ hg => ⟨g, hg, fun _ => ⟨rfl, rfl, rfl, rfl, fun _ hc => hc, fun _ hc => hc⟩⟩, rfl, Nat.le_refl _⟩
  have hinv3 := DeflateReach.caller_inv ⟨s.strm, z', sb, st0, al0, rfl, hz2, hsb, hst0, hal0, core0⟩ hcs
  have hside3 := DeflateSide.caller_side hside hcs
  have hnohdr : ∀ k, st0.gzhead ≠ .val (some k) := by
    intro k hk'
    rcases hk.2.2 (some k) ⟨sb, st0, ⟨⟨z', ⟨s.strm, rfl, hz2⟩, hsb⟩, hst0⟩, hk'⟩ with e1 | ⟨sb1, st1, ⟨⟨z1, ⟨i1, e1, hz1'⟩, hsb1⟩, hst1⟩, -⟩
    · cases e1
    · cases e1; rw [hz1] at hz1'; cases hz1'
      obtain ⟨hlt1, hnone⟩ := hzst sb1 hsb1
      have : H1.bytes sb1 = none := by rw [(x.old sb1 hlt1).1]; exact hnone
      simp [Heap.dstate, this] at hst1
  -- the fields
  have hw0 : ¬ s.want = 0 := fun e => by have := congrArg UInt32.toNat e; simp at this; have := sh.want_lo; omega
  have hsize : s3.size ≠ 0 := by simp [s3, baStW]; exact hw0
  have hin : inSize s3 = 2 * s.want.toNat := by simp [inSize, s3, baStW, hwm]
  have hout : outSize s3 = s.want.toNat := by simp [outSize, s3, baStW, hwm, hd]
  have hwb : wBytes s = 3 * s.want.toNat := by simp [wBytes, hd]; omega
  have hB : GzBufs H3 s3 h.nextBlk o := by
    refine ⟨rfl, by simp [s3, baStW, ho'], by simp [s3, baStW, ho'], fun _ => ?_, ⟨_, by rw [hc3]; exact hcH1, ?_⟩,
      ho72.1, hsv⟩
    · rw [hin]; simp [s3, baStW, hd, ho']
    · rw [hin, hout, Array.size_ofFn, hwb]; omega
  have hWB : GzWBuf H3 s3 h.nextBlk o { z' with next_in := .null, avail_out := s.want, next_out := p } := by
    refine ⟨fun _ => ⟨hinv3, hside3⟩, fun sb' st' k e1 e2 => ?_, Or.inr ⟨by simp; rw [ai]; exact hai, Or.inr rfl⟩,
      fun e1 => absurd hd e1, fun _ => ⟨0, 0, ?_, ?_, Nat.le_refl _, ?_⟩⟩
    · simp at e1; rw [hsb] at e1; cases e1
      have : H3.dstate sb = H2.dstate sb := rfl
      rw [this, hst0] at e2; cases e2; exact hnohdr k
    · rw [hin]; simp [p, ho']
    · rw [hin]; simp [s3, p, ho']
    · simp [s3, baStW]
  have hpath : ∀ c ∈ blkOf s.path, H3.bytes c = h.bytes c := fun c hc =>
    hold c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc))))
  have hmsgb : ∀ c ∈ blkOf s.msg, H3.bytes c = h.bytes c := fun c hc =>
    hold c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr hc)))
  have shape : GzShape H3 s3 := by
    refine ⟨sh.mode, ownStr_keep sh.path hpath, ⟨_, hz3⟩, sh.want_lo, sh.want_hi, Or.inr rfl,
      ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩, ⟨?_, sh.msg.2⟩,
      fun hr => absurd (hwm.symm.trans hr) write_ne_read, fun _ => ⟨fun _ => ⟨h.nextBlk, o, _, hB, hz3, hWB⟩,
      fun e => absurd e hsize, (sh.write hwm).have0⟩, fun e => absurd e hsize⟩
    rcases sh.msg.1 with e1 | e1
    · exact Or.inl e1
    · exact Or.inr (ownBlk_keep e1 hmsgb)
  have hown3 : ownL H3 b s3 = ownL h b s ++ [h.nextBlk, sb] := by
    simp [ownL, s3, baStW, hz, hw0, stBlk, hz3, hsb, blkOf]
  have hnd : (ownL H3 b s3).Nodup := by
    rw [hown3, List.nodup_append]
    refine ⟨hn, by simp; omega, fun a ha c hc => ?_⟩
    have := hlt a ha
    simp at hc; rcases hc with rfl | rfl <;> omega
  obtain ⟨⟨fS, fG, fI, -, -, fC, fcrc, fx2n, fbase, fnext⟩, fD⟩ := f
  have hsW : W3.gz H3 b = some s3 := by
    unfold World.gz; rw [hold b hbn, hdb]; simp [W3]
  have hstr : ∀ i, i ≠ s.strm → H3.streams i = h.streams i := fun i hi => by
    show (upd H2.streams s.strm _) i = _
    rw [upd_ne _ _ _ _ hi, fS i (by simp [streamIds]; exact hi), x.streams]
  have hwf := hv.2.2
  have wf : GzWFw W3 H3 := by
    refine ⟨⟨by rw [show H3.crcTable = h.crcTable from fcrc.trans x.crc]; exact hwf.1.1,
      by rw [show H3.x2nTable = h.x2nTable from fx2n.trans x.x2n]; exact hwf.1.2⟩, hk.2.1 hfr1, fun c hc => ?_,
      fun c s' hc => ?_, LitOk.ext hwf.lit rfl fun k a e => by show H2.consts k = _; rw [fC, ← x.consts k a e]⟩
    · have hcb : c ≠ b := by have : h.nextBlk ≤ H3.nextBlk := Nat.le_trans x.next fnext; omega
      simp only [W3, upd_ne _ _ _ _ hcb]
      exact hwf.2.2.1 c (by have : h.nextBlk ≤ H3.nextBlk := Nat.le_trans x.next fnext; omega)
    · by_cases hcb : c = b
      · subst hcb; rw [hsW] at hc; cases hc; exact ⟨_, hz3⟩
      · unfold World.gz at hc
        split at hc
        · next d hd =>
          simp only [W3, upd_ne _ _ _ _ hcb] at hc
          by_cases hcl : c < h.nextBlk
          · rw [hold c hcl] at hd
            obtain ⟨z5, hz5⟩ := hwf.2.2.2.1 c s' (by unfold World.gz; rw [hd]; exact hc)
            by_cases hst5 : s'.strm = s.strm
            · rw [hst5]; exact ⟨_, hz3⟩
            · exact ⟨z5, by rw [hstr _ hst5]; exact hz5⟩
          · rw [hwf.2.2.1 c (by omega)] at hc; cases hc
        · cases hc
  refine ⟨⟨⟨b, s3, rfl, hsW, shape, hnd⟩, ⟨b, s3, rfl, hsW, hwm⟩, wf⟩, hsW, ?_⟩
  refine gstep_mk' hs hsW rfl (fun c hc _ => by simp [W3, upd_ne _ _ _ _ hc]) hstr
    (fun k => by show H2.gzheaders k = _; rw [fG k (List.not_mem_nil), x.hdr]) (fun c hc _ => ?_)
    (fun k a e => by show H2.consts k = _; rw [fC, ← x.consts k a e]) (fcrc.trans x.crc) (fx2n.trans x.x2n)
    (fbase.trans x.base) (Nat.le_trans x.next fnext) (fun c hc hlt' => ?_)
  · have hc1 : c < H1.nextBlk := by omega
    obtain ⟨i1, i2⟩ := fI c hc1 (List.not_mem_nil)
    obtain ⟨d1, d2⟩ := fD c hc1 (List.not_mem_nil)
    exact ⟨hold c hc, by show H2.istates c = _; rw [i1, x.istates], by show H2.iallocs c = _; rw [i2, x.iallocs],
      by show H2.dstates c = _; rw [d1, x.dstates], by show H2.dallocs c = _; rw [d2, x.dallocs]⟩
  · simp only [GzOwned, hsW, hs, hz3, hz0] at hc ⊢
    simp [s3, baStW, hsb, hzst] at hc ⊢
    rcases hc with h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · omega
    · rw [hz3] at h1; simp [hsb] at h1; omega

theorem bfSt_baStW (s : GzState) (c o : Nat) : bfSt (baStW s c o) = bfSt s := by simp [bfSt, baStW]

open ZlibNgF.Proof.GzWriteNeeds in
/-- After a failed `deflateInit2_` in `gz_write_init` and `gz_buffer_free`, before its `gz_error`: the buffers are
freed, the write handle has its invariant without buffers. -/
theorem invWS_initFail (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) {lv m wb ml st sz r : Int32} {H2 : Heap}
    (e : ZlibNg.Deflate.deflateInit2_ (some s.strm) lv m wb ml st (.ref (.str 0) 0) sz
      (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) = .ok (r, H2))
    (hr : r ≠ ZlibNg.Inflate.Z_OK) :
    ∃ d, H2.bytes h.nextBlk = some d ∧ alOff (h.baseAddr (.heap h.nextBlk)) ≤ d.size ∧
      H2.savedPtrs h.nextBlk = some (alOff (h.baseAddr (.heap h.nextBlk)) - 8, .ref (.heap h.nextBlk) 0) ∧
      H2.bytes b = h.bytes b ∧
      GzInvWS { w with gzs := upd w.gzs b (some (bfSt s)) } (freeH H2 h.nextBlk) (some b) ∧
      ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz (freeH H2 h.nextBlk) b = some (bfSt s) ∧
      GStep w h { w with gzs := upd w.gzs b (some (bfSt s)) } (freeH H2 h.nextBlk) b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  generalize ho : alOff (h.baseAddr (.heap h.nextBlk)) = o at e ⊢
  generalize hH1 : alH h (8 + wBytes s + 64) o = H1 at e
  have x : HExt h H1 := hH1 ▸ HExt.alloc_aligned h _ _
  have hn1 : H1.nextBlk = h.nextBlk + 1 := by rw [← hH1]; rfl
  have hfr0 := hv.2.2.2.1
  have fr : FreshBlocks h := hfr0.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbn : b < h.nextBlk := live_lt fr ⟨db, hdb⟩
  have hlt : ∀ c ∈ ownL h b s, c < h.nextBlk := fun c hc => live_lt fr (ownL_liveW sh hwm ⟨db, hdb⟩ c hc)
  obtain ⟨z, hz0, hai, hza, hzf, hns⟩ := (sh.write hwm).nobuf hz
  have hz1 : H1.streams s.strm = some z := by rw [x.streams]; exact hz0
  have hfr1 : DFreshBlocks H1 :=
    ⟨x.fresh fr, fun c e' => by rw [x.dstates, x.dallocs]; exact hfr0.2 c (by omega)⟩
  have hi1 : DInitReady H1 (some s.strm) := Or.inr ⟨z, ⟨s.strm, rfl, hz1⟩, hza, hzf⟩
  obtain ⟨r', H2', e', f⟩ := init2__run H1 (some s.strm) lv m wb ml st sz hfr1 hi1
  rw [e] at e'; cases e'
  have GI := G.1 H1 H2 (some s.strm) lv m wb ml st _ sz _ z ⟨s.strm, rfl, hz1⟩ hi1 hfr1 (by simpa [C.run] using e)
  obtain ⟨z', ⟨i', ei, hz2⟩, ni, ai, _no, _ao, hfl, hk, -⟩ := GI
  cases ei
  obtain ⟨hzst', hza', hzf'⟩ := hfl hr
  have hcN : h.nextBlk < H1.nextBlk := by omega
  have hold : ∀ c, c < h.nextBlk → H2.bytes c = h.bytes c := fun c hc => by
    rw [frame_bytes_eq f.1 (by omega) (List.not_mem_nil), (x.old c hc).1]
  have hzst : ∀ c, z.state = some c → c < h.nextBlk ∧ h.bytes c = none := by
    intro c hc
    have := sh.dead hz c (List.mem_append_right _ (by simp [stBlk, hz0, hc]))
    exact ⟨this.2, this.1⟩
  have hcH1 : H1.bytes h.nextBlk = some (Array.ofFn (n := 8 + wBytes s + 64)
      fun i => Junk.of (h.garbage h.nalloc i.val)) := by rw [← hH1]; simp [alH]
  have ho72 := alOff_bounds (h.baseAddr (.heap h.nextBlk))
  rw [ho] at ho72
  refine ⟨_, by rw [frame_bytes_eq f.1 hcN (List.not_mem_nil)]; exact hcH1, by simp; omega, ?_, hold b hbn, ?_⟩
  · rw [hk.1 h.nextBlk hcN (fun z0 ⟨i0, e0, hz0'⟩ e2 => by
      cases e0; rw [hz1] at hz0'; cases hz0'
      have := (hzst _ e2).1; omega)]
    rw [← hH1]; simp [alH]
  -- the heap after the free
  generalize hH3 : freeH H2 h.nextBlk = H3
  have hold3 : ∀ c, c < h.nextBlk → H3.bytes c = h.bytes c := fun c hc => by
    rw [← hH3, freeH_bytes_ne (by omega)]; exact hold c hc
  have hz3 : H3.streams s.strm = some z' := by rw [← hH3]; exact hz2
  obtain ⟨⟨fS, fG, fI, -, fN, fC, fcrc, fx2n, fbase, fnext⟩, fD⟩ := f
  have hstr : ∀ i, i ≠ s.strm → H3.streams i = h.streams i := fun i hi => by
    rw [← hH3]; show H2.streams i = _; rw [fS i (by simp [streamIds]; exact hi), x.streams]
  have hsW : ({ w with gzs := upd w.gzs b (some (bfSt s)) } : World).gz H3 b = some (bfSt s) := by
    unfold World.gz; rw [hold3 b hbn, hdb]; simp
  have hpath : ∀ c ∈ blkOf s.path, H3.bytes c = h.bytes c := fun c hc =>
    hold3 c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inl (Or.inr hc))))
  have hmsgb : ∀ c ∈ blkOf s.msg, H3.bytes c = h.bytes c := fun c hc =>
    hold3 c (hlt c (by simp only [ownL, List.mem_append]; exact Or.inl (Or.inr hc)))
  have hstB : stBlk H3 (bfSt s) = stBlk h s := by simp [stBlk, bfSt, hz3, hz0, hzst']
  have shape : GzShape H3 (bfSt s) := by
    refine ⟨sh.mode, ownStr_keep sh.path hpath, ⟨_, hz3⟩, sh.want_lo, sh.want_hi, Or.inl rfl,
      ⟨sh.pos.1, sh.pos.2, sh.pos.3, sh.pos.4⟩, ⟨?_, sh.msg.2⟩,
      fun hr' => absurd (hwm.symm.trans hr') write_ne_read, fun _ => ⟨fun e => absurd rfl e,
      fun _ => ⟨z', hz3, by rw [ai]; exact hai, hza', hzf', fun e => by rw [hzst']; exact hns e⟩,
      (sh.write hwm).have0⟩, fun _ c hc => ?_⟩
    · rcases sh.msg.1 with e1 | e1
      · exact Or.inl e1
      · exact Or.inr (ownBlk_keep e1 hmsgb)
    · simp only [bfSt, blkOf, List.nil_append] at hc
      rw [show stBlk H3 { s with buffers := .val .null, out := .val .null, «in» := .val .null, size := 0 } =
        stBlk h s from hstB] at hc
      obtain ⟨h1, h2⟩ := sh.dead hz c (List.mem_append_right _ hc)
      have hle : h.nextBlk ≤ H3.nextBlk := by rw [← hH3]; exact Nat.le_trans x.next fnext
      exact ⟨by rw [hold3 c h2]; exact h1, by omega⟩
  have hown3 : ownL H3 b (bfSt s) = ownL h b s := by simp [ownL, bfSt, hz]
  have hwf := hv.2.2
  have wf : GzWFw { w with gzs := upd w.gzs b (some (bfSt s)) } H3 := by
    refine ⟨⟨by rw [show H3.crcTable = h.crcTable by rw [← hH3]; exact fcrc.trans x.crc]; exact hwf.1.1,
      by rw [show H3.x2nTable = h.x2nTable by rw [← hH3]; exact fx2n.trans x.x2n]; exact hwf.1.2⟩, ?_, fun c hc => ?_,
      fun c s' hc => ?_, LitOk.ext hwf.lit rfl fun k a e => by rw [← hH3]; show H2.consts k = _; rw [fC, ← x.consts k a e]⟩
    · obtain ⟨f1, f3⟩ := hk.2.1 hfr1
      refine ⟨fun c hc => ?_, by rw [← hH3]; exact f3⟩
      have hcc : c ≠ h.nextBlk := by rw [← hH3] at hc; simp [freeH] at hc; omega
      rw [← hH3] at hc ⊢; exact ⟨(f1 c hc).1, (f1 c hc).2.1, by rw [freeH_bytes_ne hcc]; exact (f1 c hc).2.2⟩
    · have hle : h.nextBlk ≤ H3.nextBlk := by rw [← hH3]; exact Nat.le_trans x.next fnext
      have hcb : c ≠ b := by omega
      simp only [upd_ne _ _ _ _ hcb]
      exact hwf.2.2.1 c (by omega)
    · by_cases hcb : c = b
      · subst hcb; rw [hsW] at hc; cases hc; exact ⟨_, hz3⟩
      · unfold World.gz at hc
        split at hc
        · next d hd =>
          simp only [upd_ne _ _ _ _ hcb] at hc
          by_cases hcl : c < h.nextBlk
          · rw [hold3 c hcl] at hd
            obtain ⟨z5, hz5⟩ := hwf.2.2.2.1 c s' (by unfold World.gz; rw [hd]; exact hc)
            by_cases hst5 : s'.strm = s.strm
            · rw [hst5]; exact ⟨_, hz3⟩
            · exact ⟨z5, by rw [hstr _ hst5]; exact hz5⟩
          · rw [hwf.2.2.1 c (by omega)] at hc; cases hc
        · cases hc
  refine ⟨⟨⟨b, _, rfl, hsW, shape, by rw [hown3]; exact hn⟩, ⟨b, _, rfl, hsW, hwm⟩, wf⟩, hsW, ?_⟩
  refine gstep_mk' hs hsW rfl (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) hstr
    (fun k => by rw [← hH3]; show H2.gzheaders k = _; rw [fG k (List.not_mem_nil), x.hdr]) (fun c hc _ => ?_)
    (fun k a e => by rw [← hH3]; show H2.consts k = _; rw [fC, ← x.consts k a e])
    (by rw [← hH3]; exact fcrc.trans x.crc) (by rw [← hH3]; exact fx2n.trans x.x2n)
    (by rw [← hH3]; exact fbase.trans x.base) (by rw [← hH3]; exact Nat.le_trans x.next fnext) (fun c hc hlt' => ?_)
  · have hc1 : c < H1.nextBlk := by omega
    obtain ⟨i1, i2⟩ := fI c hc1 (List.not_mem_nil)
    obtain ⟨d1, d2⟩ := fD c hc1 (List.not_mem_nil)
    rw [← hH3]
    exact ⟨by rw [hH3]; exact hold3 c hc, by show H2.istates c = _; rw [i1, x.istates],
      by show H2.iallocs c = _; rw [i2, x.iallocs], by show H2.dstates c = _; rw [d1, x.dstates],
      by show H2.dallocs c = _; rw [d2, x.dallocs]⟩
  · simp only [GzOwned, hsW, hs, hz3, hz0, hzst'] at hc ⊢
    simp [bfSt] at hc ⊢
    rcases hc with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · simp only [hz3, hzst'] at h1; exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

/-! ## Reads and stores of the state on a heap whose stream table changed -/

theorem ldGz_updS {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (T : Tbl (Option ZStream))
    (w : World) (s : GzState) :
    ldGz (some b) { w with gzs := upd w.gzs b (some s) } { h with streams := T } =
      .ok ((s, { w with gzs := upd w.gzs b (some s) }), { h with streams := T }) :=
  ldGz_upd (h := { h with streams := T }) hb w s

theorem rdG_updS {α : Type} {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d)
    (T : Tbl (Option ZStream)) (w : World) (s : GzState) (g : GzState → α) :
    rdG (some b) g { w with gzs := upd w.gzs b (some s) } { h with streams := T } =
      .ok ((g s, { w with gzs := upd w.gzs b (some s) }), { h with streams := T }) :=
  rdG_upd (h := { h with streams := T }) hb w s g

theorem wrG_updS {h : Heap} {b : Nat} {d : Array UInt8} (hb : h.bytes b = some d) (T : Tbl (Option ZStream))
    (w : World) (s : GzState) (f : GzState → GzState) :
    wrG (some b) f { w with gzs := upd w.gzs b (some s) } { h with streams := T } =
      .ok (((), { w with gzs := upd w.gzs b (some (f s)) }), { h with streams := T }) :=
  wrG_upd (h := { h with streams := T }) hb w s f

/-- The fields of a write handle that `gz_write_init` and `gz_comp` keep. -/
structure WFix (s s' : GzState) : Prop where
  pos : s'.pos = s.pos
  skip : s'.skip = s.skip
  want : s'.want = s.want
  direct : s'.direct = s.direct
  mode : s'.mode = s.mode
  level : s'.level = s.level
  strategy : s'.strategy = s.strategy
  fd : s'.fd = s.fd
  strm : s'.strm = s.strm

theorem WFix.refl (s : GzState) : WFix s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem WFix.trans {s1 s2 s3 : GzState} (a : WFix s1 s2) (b : WFix s2 s3) : WFix s1 s3 :=
  ⟨b.1.trans a.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6, b.7.trans a.7,
    b.8.trans a.8, b.9.trans a.9⟩

theorem WFix.of_err {s s' : GzState} {e : Int32} (h : ErrOf s e s') : WFix s s' := by
  obtain ⟨h1, -⟩ := h
  rw [h1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What `gz_write_init` leaves: the invariant, a step of the file, the same file system and fixed fields, and on
success the buffers. -/
def InitPost (w : World) (h : Heap) (b : Nat) (s : GzState) (r : Int32) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ GzInvWS W H (some b) ∧ GStep w h W H b [] ∧ W.fs = w.fs ∧ WFix s s' ∧
    ((r = 0 ∧ s'.size ≠ 0) ∨ r = -1)

open ZlibNgF.Proof.GzWriteNeeds in
/-- **`gz_write_init`** on a write handle without buffers. -/
theorem gz_write_init_spec (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (hz : s.size = 0) :
    GSat w h (gz_write_init (some b)) (InitPost w h b s) := by
  unfold gz_write_init
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.mono (gz_buffer_alloc_specW hv hs hz) fun r W1 H1 q => ?_)
  rcases q with ⟨rfl, s1, hs1, he1, hv1, hf1, g1⟩ | ⟨rfl, hok, rfl, rfl⟩
  · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by decide) hc)
    refine GSat.mono (gz_error_litW "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom hv1 hs1
      ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)) fun r' W H q => ?_
    obtain ⟨rfl, s2, hs2, he2, hv2, hf2, g2⟩ := q
    exact ⟨s2, hs2, hv2, g1.trans g2 ⟨s, hs⟩ ⟨s1, hs1⟩, hf2.trans hf1,
      (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : WFix s (bfSt s)).trans
        ((WFix.of_err he1).trans (WFix.of_err he2)), Or.inr rfl⟩
  · refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
    have hwm := modeOf hs hv.2.1
    obtain ⟨sh, -⟩ := inv_of hs hv.1
    obtain ⟨db, hdb⟩ := gz_live hs
    have fr : FreshBlocks h := hv.2.2.2.1.1
    have hbn : b < h.nextBlk := live_lt fr ⟨db, hdb⟩
    have x : HExt h (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) := HExt.alloc_aligned h _ _
    have hs1 : ({ w with gzs := upd w.gzs b (some (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk))))) } :
        World).gz (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) b =
        some (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))) := by
      unfold World.gz; rw [(x.old b hbn).1, hdb]; simp
    refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
    by_cases hd : s.direct = 0
    · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simp [baStW, hd]) hc)
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      refine GSat.bind (GSat.lm ⟨_, _, strLit_version _, ?_⟩)
      obtain ⟨z, hz0, hai, hza, hzf, -⟩ := (sh.write hwm).nobuf hz
      have hz1 : (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))).streams s.strm = some z := by
        rw [x.streams]; exact hz0
      have hfr1 : DFreshBlocks (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) :=
        ⟨x.fresh fr, fun c e' => by rw [x.dstates, x.dallocs]; exact hv.2.2.2.1.2 c (by simp [alH] at e'; omega)⟩
      have hi1 : DInitReady (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) (some s.strm) :=
        Or.inr ⟨z, ⟨s.strm, rfl, hz1⟩, hza, hzf⟩
      obtain ⟨r, H2, e, f⟩ := init2__run _ (some s.strm) (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).level
        ZlibNg.Inflate.Z_DEFLATED.toUInt32.toInt32 (ZlibNg.Inflate.MAX_WBITS + 16) ZlibNg.Deflate.DEF_MEM_LEVEL
        (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).strategy SIZEOF_Z_STREAM.toInt32 hfr1 hi1
      refine GSat.bind (GSat.lm ⟨r, H2, e, ?_⟩)
      have hb2 : H2.bytes b = h.bytes b := by
        rw [frame_bytes_eq f.1 (by simp [alH]; omega) (List.not_mem_nil), (x.old b hbn).1]
      have hs2 : ({ w with gzs := upd w.gzs b (some (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk))))) } :
          World).gz H2 b = some (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))) := by
        unfold World.gz; rw [hb2, hdb]; simp
      by_cases hr : r = ZlibNg.Inflate.Z_OK
      · subst hr
        refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
        obtain ⟨z', hz2, hv3, hs3, g3⟩ := invWS_initOk G hv hs hz hd e
        refine ⟨0, _, _, ?_, _, hs3, hv3, g3, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
          Or.inl ⟨rfl, baStW_size sh.want_lo h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))⟩⟩
        have hd2 : H2.bytes b = some db := by rw [hb2, hdb]
        simp [ZlibNg.Inflate.wrZ, ZlibNg.Inflate.rdZ, ldStream, stStream, hz2, rdG_updS hd2, ldGz_updS hd2,
          wrG_updS hd2, Ival.get, liftM, monadLift, MonadLift.monadLift,
          InflateInv.upd_upd, baStW, hd]
      · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simpa using hr) hc)
        obtain ⟨d, hdc, hod, hsv, -, hv3, hs3, g3⟩ := invWS_initFail G hv hs hz e hr
        have hd2 : H2.bytes b = some db := by rw [hb2, hdb]
        have hcb : h.nextBlk ≠ b := by omega
        have hdF : (freeH H2 h.nextBlk).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hd2
        have ho8 := (alOff_bounds (h.baseAddr (.heap h.nextBlk))).1
        refine GSat.bind (GSat.of_eq (a := ()) (w' := { w with gzs := upd w.gzs b (some (bfSt s)) })
          (h' := freeH H2 h.nextBlk) ?_ ?_)
        · simp [gz_buffer_free, ldGz_upd hd2, Ival.get, liftM, monadLift, MonadLift.monadLift, baStW,
            free_aligned_app hdc hod ho8 hsv, wrG_upd hdF, InflateInv.upd_upd, bfSt]
        · have hfin : ∀ (lit : String) (i : Nat) (e : Int32), gzLits.findIdx? (· == lit) = some i →
              gzLits[i]? = some lit → NoNul lit →
              GSat { w with gzs := upd w.gzs b (some (bfSt s)) } (freeH H2 h.nextBlk)
                (do gz_error (some b) e (← gzLit lit); pure (-1 : Int32)) (InitPost w h b s) := by
            intro lit i e hi hl hn
            refine GSat.mono (gz_error_litW lit i hi hl hn hv3 hs3 e (-1 : Int32)) fun r' W H q => ?_
            obtain ⟨rfl, s4, hs4, he4, hv4, hf4, g4⟩ := q
            exact ⟨s4, hs4, hv4, g3.trans g4 ⟨s, hs⟩ ⟨_, hs3⟩, hf4,
              (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : WFix s (bfSt s)).trans (WFix.of_err he4), Or.inr rfl⟩
          refine GSat.ite (fun _ => hfin _ 0 _ GzReach.lit_oom lit_oom_get nonul_oom) (fun _ => ?_)
          exact hfin "invalid compression parameters" 1 _ (by simp [gzLits, List.findIdx?_cons]) (by decide) (by decide)
    · refine GSat.ite (fun hc => absurd (by simpa [baStW] using hc) hd) (fun _ => ?_)
      obtain ⟨v2, s2, g2⟩ := invWS_allocDirect hv hs hz hd
      exact GSat.pure ⟨_, s2, v2, g2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        Or.inl ⟨rfl, baStW_size sh.want_lo _ _⟩⟩

end ZlibNgF.Proof.GzWrite
