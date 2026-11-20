import ZlibNgF.Proof.«gzwrite.c.keeps»
import ZlibNgF.Proof.«gzread.c.close»

/-!
# `gzclose_w` releases a write handle (`ZlibNgF`)

`gzclose_w` of a write handle runs the pending seek (`gz_zero`) and `gz_comp(state, Z_FINISH)`, then ends the deflate
stream (when not direct) and frees the buffers (when they exist), frees the message, the path and the state, ends the
embedded stream and closes the descriptor. Every block the file owned at entry is freed at the end (`GzReleased`),
whatever `gz_zero`, `gz_comp` and `close` return.

The calls before the close keep each block the file owned at entry: it is still a block of the file or it is freed
(`Ret`). `gz_write_init` keeps `path`, frees the old message or keeps it, and keeps dead blocks dead (the stale buffer
and stream-state blocks of a file without buffers); once the buffers exist, `gz_comp` keeps `path`, the buffers and the
stream's `state` field and frees the old message or keeps it (`Trk`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-! ## Keeping the blocks of the entry -/

/-- Every block that the file `b` owns in `w`, `h` is still one of its blocks in `W`, `H`, or is freed. -/
def Ret (w : World) (h : Heap) (W : World) (H : Heap) (b : Nat) : Prop :=
  ∀ c ∈ GzOwned w h (some b), c ∈ GzOwned W H (some b) ∨ H.bytes c = none

theorem Ret.refl (w : World) (h : Heap) (b : Nat) : Ret w h w h b := fun _ m => Or.inl m

/-- The heap does not shrink and dead blocks stay dead. -/
def DeadK (h H : Heap) : Prop := h.nextBlk ≤ H.nextBlk ∧ ∀ c, c < h.nextBlk → h.bytes c = none → H.bytes c = none

theorem DeadK.refl (h : Heap) : DeadK h h := ⟨Nat.le_refl _, fun _ _ e => e⟩

theorem DeadK.trans {h1 h2 h3 : Heap} (a : DeadK h1 h2) (b : DeadK h2 h3) : DeadK h1 h3 :=
  ⟨Nat.le_trans a.1 b.1, fun c hc hd => b.2 c (Nat.lt_of_lt_of_le hc a.1) (a.2 c hc hd)⟩

theorem DeadK.of_hext {h H : Heap} (x : HExt h H) : DeadK h H :=
  ⟨x.next, fun c hc hd => by rw [(x.old c hc).1]; exact hd⟩

/-- The blocks of a write handle with the invariant are older than the heap. -/
theorem own_lt {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) :
    ∀ c ∈ GzOwned w h (some b), c < h.nextBlk := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have fr : FreshBlocks h := hv.2.2.2.1.1
  intro c hc
  by_cases hsz : s.size = 0
  · rw [gzOwned_eq hs] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with (((h1 | h2) | h3) | h4) | h5
    · exact live_lt fr (ownL_liveW sh hwm (gz_live hs) c (by simp [ownL, h1]))
    · exact live_lt fr (ownL_liveW sh hwm (gz_live hs) c (by simp [ownL, h2]))
    · exact live_lt fr (ownL_liveW sh hwm (gz_live hs) c (by simp [ownL, h3]))
    · exact (sh.dead hsz c (List.mem_append_left _ h4)).2
    · exact (sh.dead hsz c (List.mem_append_right _ h5)).2
  · exact live_lt fr (ownL_liveW sh hwm (gz_live hs) c (owned_ownL hs hsz hc))

/-- The heap of a step is not smaller. -/
theorem GStep.next {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) : h.nextBlk ≤ H.nextBlk := by
  obtain ⟨⟨⟨fr, -⟩, -, -⟩, -, -⟩ := g
  exact fr.2.2.2.2.2.2.2.2.2

/-- A dead block that is not one of the file's stays dead across a step. -/
theorem GStep.dead {w W : World} {h H : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s)
    (g : GStep w h W H b []) {c : Nat} (hc : c < h.nextBlk) (hno : c ∉ GzOwned w h (some b))
    (hd : h.bytes c = none) : H.bytes c = none := by
  obtain ⟨⟨⟨fr, -⟩, -, -⟩, -, -⟩ := g
  simp only [hs] at fr
  exact fr.2.2.2.2.1 c hc hno hd

theorem Ret.trans {w W1 W2 : World} {h H1 H2 : Heap} {b : Nat} {s1 : GzState} (r1 : Ret w h W1 H1 b)
    (r2 : Ret W1 H1 W2 H2 b) (hs1 : W1.gz H1 b = some s1) (g : GStep W1 H1 W2 H2 b [])
    (hlt : ∀ c ∈ GzOwned w h (some b), c < H1.nextBlk) : Ret w h W2 H2 b := by
  intro c hc
  rcases r1 c hc with m | d
  · exact r2 c m
  · by_cases m : c ∈ GzOwned W1 H1 (some b)
    · exact r2 c m
    · exact Or.inr (GStep.dead hs1 g (hlt c hc) m d)

/-- `Ret` from the fields: `path` kept, the message kept or freed, and the buffer and stream-state blocks kept or
freed. -/
theorem ret_mk {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hp : s'.path = s.path) (hm : MKeep s s' H)
    (hr : ∀ c ∈ blkOf s.buffers ++ stBlk h s, c ∈ GzOwned W H (some b) ∨ H.bytes c = none) : Ret w h W H b := by
  intro c hc
  rw [gzOwned_eq hs] at hc
  have e' := gzOwned_eq hs'
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with (((h1 | h2) | h3) | h4) | h5
  · exact Or.inl (by rw [e', h1]; simp)
  · exact Or.inl (by rw [e', hp]; simp [h2])
  · rcases hm with em | dm
    · exact Or.inl (by rw [e', em]; simp [h3])
    · exact Or.inr (dm c h3).1
  · exact hr c (List.mem_append_left _ h4)
  · exact hr c (List.mem_append_right _ h5)

/-! ## `gz_error` on a write handle frees the old message -/

/-- `gz_error` on a write handle frees the old message and keeps dead blocks dead. -/
theorem gz_error_freesW {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ _ H => (∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) ∧
      DeadK h H) := by
  have hlit : LitOk w h := hv.2.2.lit
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, -, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  have fr : FreshBlocks h := hw.2.1.1
  obtain ⟨db, hdb⟩ := gz_live hs
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hn hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, -⟩ := err0_keep sh hn e
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, -, -, -, -, -, x, -, -⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  refine ⟨r, W, H, by rw [gz_error_run hs sh.msg (msg_ne_b hn) e msg]; exact eq, ?_, ?_⟩
  · intro c hc
    rcases sh.msg.msg with e1 | ⟨c', d, e1, hd⟩
    · rw [e1] at hc; simp [blkOf] at hc
    · rw [e1] at hc; simp [blkOf] at hc; subst hc
      have hne : s.err ≠ ZlibNg.Inflate.Z_MEM_ERROR := fun e' => by
        have := sh.msg.mem e'; rw [e1] at this; cases this
      have hlt : c < h.nextBlk := live_lt fr ⟨d, hd⟩
      have hf : (freeMsg h s).bytes c = none := by unfold freeMsg; rw [e1]; simp [hne]
      have hc' : c < (freeMsg h s).nextBlk := by rw [freeMsg_next]; exact hlt
      exact ⟨by rw [(x.old c hc').1]; exact hf, Nat.lt_of_lt_of_le hc' x.next⟩
  · refine ⟨by have := x.next; rw [freeMsg_next] at this; exact this, fun c hc hd => ?_⟩
    have hc' : c < (freeMsg h s).nextBlk := by rw [freeMsg_next]; exact hc
    rw [(x.old c hc').1]; exact freeMsg_none h s c hd

/-- `gz_error(state, e, lit)` on a write handle frees the old message and keeps dead blocks dead. -/
theorem gz_error_litW_frees (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hl : gzLits[i]? = some lit) (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r)
      (fun _ _ H => (∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) ∧ DeadK h H) := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, -, x, hL, hc, hk⟩ := q
  obtain ⟨hv1, hs1, -⟩ := invWS_ext hv hs x hg hL
  refine GSat.bind (GSat.mono (gz_error_freesW hv1 hs1 e p (Or.inr ⟨_, hc⟩) hk) fun _ W H q => ?_)
  exact GSat.pure ⟨q.1, (DeadK.of_hext x).trans q.2⟩

/-! ## `gz_write_init` -/

/-- `gz_buffer_alloc` on a write handle without buffers: when it fails, its `gz_error` freed the old message and
dead blocks stay dead. -/
theorem alloc_frees {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) :
    GSat w h (gz_buffer_alloc (some b)) (fun r _ H => r = -1 →
      (∀ c ∈ blkOf s.msg, H.bytes c = none ∧ c < H.nextBlk) ∧ DeadK h H) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  cases hok : h.allocOk h.nalloc with
  | true =>
    have hfr : h.bytes h.nextBlk = none := (hv.2.2.2.1.1 h.nextBlk (Nat.le_refl _)).2.2
    exact ⟨_, _, _, gz_buffer_alloc_okW hs hwm sh.want_lo sh.want_hi hfr hok, fun e => by cases e⟩
  | false =>
    obtain ⟨v1, s1, -⟩ := invWS_bf hv hs hz
    obtain ⟨r, W, H, e, q⟩ := gz_error_litW_frees "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom v1 s1
      ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)
    exact ⟨r, W, H, by rw [gz_buffer_alloc_failW hs hwm hok]; exact e, fun _ => ⟨q.1, ⟨q.2.1, fun c hc hd => q.2.2 c hc hd⟩⟩⟩

/-- What `gz_write_init` keeps of the entry state `s`, heap `h`: the `path`, the message or its freeing, and dead
blocks. -/
def InitK (h : Heap) (b : Nat) (s : GzState) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ s'.path = s.path ∧ MKeep s s' H ∧ DeadK h H

theorem initK_err {h H1 H : Heap} {b : Nat} {s s1 s2 : GzState} {W : World} {e : Int32}
    (hm1 : ∀ c ∈ blkOf s.msg, H1.bytes c = none ∧ c < H1.nextBlk) (d1 : DeadK h H1) (hp1 : s1.path = s.path)
    (hs2 : W.gz H b = some s2) (he : ErrOf s1 e s2) (d2 : DeadK H1 H) : InitK h b s W H :=
  ⟨s2, hs2, (errOf_path he).trans hp1, Or.inr fun c hc => ⟨d2.2 c (hm1 c hc).2 (hm1 c hc).1,
    Nat.lt_of_lt_of_le (hm1 c hc).2 d2.1⟩, d1.trans d2⟩

theorem DeadK.of_frame {h H : Heap} {S G : List Nat} {wr : List (BPtr × Nat)} (f : Frame h H S [] G wr) :
    DeadK h H :=
  ⟨f.2.2.2.2.2.2.2.2.2, fun c hc hd => f.2.2.2.2.1 c hc List.not_mem_nil hd⟩

theorem DeadK.freeH (h : Heap) (c : Nat) : DeadK h (freeH h c) :=
  ⟨Nat.le_refl _, fun _ _ hd => freeH_none hd⟩

open ZlibNgF.Proof.GzWriteNeeds in
/-- **`gz_write_init`** keeps the `path`, frees or keeps the message, and keeps dead blocks dead. -/
theorem init_keep (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (hz : s.size = 0) :
    GSat w h (gz_write_init (some b)) (fun _ W H => InitK h b s W H) := by
  unfold gz_write_init
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.mono (gsat_and (gz_buffer_alloc_specW hv hs hz) (alloc_frees hv hs hz))
    fun r W1 H1 q => ?_)
  obtain ⟨q, hf1⟩ := q
  rcases q with ⟨rfl, s1, hs1, he1, hv1, -, -⟩ | ⟨rfl, hok, rfl, rfl⟩
  · obtain ⟨hm1, d1⟩ := hf1 rfl
    refine GSat.ite (fun _ => ?_) (fun hc => absurd (by decide) hc)
    refine GSat.mono (gsat_and (gz_error_litW "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom hv1 hs1
      ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)) (gz_error_litW_frees "out of memory" 0 GzReach.lit_oom lit_oom_get
      nonul_oom hv1 hs1 ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32))) fun r' W H q => ?_
    obtain ⟨⟨-, s2, hs2, he2, -⟩, -, d2⟩ := q
    exact initK_err hm1 d1 ((errOf_path he1).trans rfl) hs2 he2 d2
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
      obtain ⟨z0, hz0, -, hza, hzf, -⟩ := (sh.write hwm).nobuf hz
      have hz1 : (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))).streams s.strm = some z0 := by
        rw [x.streams]; exact hz0
      have hfr1 : DFreshBlocks (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) :=
        ⟨x.fresh fr, fun c e' => by rw [x.dstates, x.dallocs]; exact hv.2.2.2.1.2 c (by simp [alH] at e'; omega)⟩
      have hi1 : DInitReady (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) (some s.strm) :=
        Or.inr ⟨z0, ⟨s.strm, rfl, hz1⟩, hza, hzf⟩
      obtain ⟨r, H2, e, f⟩ := init2__run _ (some s.strm) (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).level
        ZlibNg.Inflate.Z_DEFLATED.toUInt32.toInt32 (ZlibNg.Inflate.MAX_WBITS + 16) ZlibNg.Deflate.DEF_MEM_LEVEL
        (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).strategy SIZEOF_Z_STREAM.toInt32 hfr1 hi1
      have dk2 : DeadK h H2 := (DeadK.of_hext x).trans (DeadK.of_frame f.1)
      refine GSat.bind (GSat.lm ⟨r, H2, e, ?_⟩)
      have hb2 : H2.bytes b = h.bytes b := by
        rw [frame_bytes_eq f.1 (by simp [alH]; omega) (List.not_mem_nil), (x.old b hbn).1]
      by_cases hr : r = ZlibNg.Inflate.Z_OK
      · subst hr
        refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
        obtain ⟨z', hz2', -, hs3, -⟩ := invWS_initOk G hv hs hz hd e
        refine ⟨0, _, _, ?_, _, hs3, rfl, Or.inl rfl, dk2.trans ⟨Nat.le_refl _, fun _ _ hd => hd⟩⟩
        have hd2 : H2.bytes b = some db := by rw [hb2, hdb]
        simp [ZlibNg.Inflate.wrZ, ZlibNg.Inflate.rdZ, ldStream, stStream, hz2', rdG_updS hd2, ldGz_updS hd2,
          wrG_updS hd2, Ival.get, liftM, monadLift, MonadLift.monadLift,
          InflateInv.upd_upd, baStW, hd]
      · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simpa using hr) hc)
        obtain ⟨d, hdc, hod, hsv, -, hv3, hs3, -⟩ := invWS_initFail G hv hs hz e hr
        have hd2 : H2.bytes b = some db := by rw [hb2, hdb]
        have hcb : h.nextBlk ≠ b := by omega
        have hdF : (freeH H2 h.nextBlk).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hd2
        have ho8 := (alOff_bounds (h.baseAddr (.heap h.nextBlk))).1
        have dk3 : DeadK h (freeH H2 h.nextBlk) := dk2.trans (DeadK.freeH _ _)
        refine GSat.bind (GSat.of_eq (a := ()) (w' := { w with gzs := upd w.gzs b (some (bfSt s)) })
          (h' := freeH H2 h.nextBlk) ?_ ?_)
        · simp [gz_buffer_free, ldGz_upd hd2, Ival.get, liftM, monadLift, MonadLift.monadLift, baStW,
            free_aligned_app hdc hod ho8 hsv, wrG_upd hdF, InflateInv.upd_upd, bfSt]
        · have hfin : ∀ (lit : String) (i : Nat) (e : Int32), gzLits.findIdx? (· == lit) = some i →
              gzLits[i]? = some lit → NoNul lit →
              GSat { w with gzs := upd w.gzs b (some (bfSt s)) } (freeH H2 h.nextBlk)
                (do gz_error (some b) e (← gzLit lit); pure (-1 : Int32)) (fun _ W H => InitK h b s W H) := by
            intro lit i e hi hl hn
            refine GSat.mono (gsat_and (gz_error_litW lit i hi hl hn hv3 hs3 e (-1 : Int32))
              (gz_error_litW_frees lit i hi hl hn hv3 hs3 e (-1 : Int32))) fun r' W H q => ?_
            obtain ⟨⟨-, s4, hs4, he4, -⟩, hm4, d4⟩ := q
            exact ⟨s4, hs4, (errOf_path he4).trans rfl, Or.inr hm4, dk3.trans d4⟩
          refine GSat.ite (fun _ => hfin _ 0 _ GzReach.lit_oom lit_oom_get nonul_oom) (fun _ => ?_)
          exact hfin "invalid compression parameters" 1 _ (by simp [gzLits, List.findIdx?_cons]) (by decide) (by decide)
    · refine GSat.ite (fun hc => absurd (by simpa [baStW] using hc) hd) (fun _ => ?_)
      exact GSat.pure ⟨_, hs1, rfl, Or.inl rfl, DeadK.of_hext x⟩

/-! ## `gz_comp` -/

/-- `Ret` from what `gz_comp` keeps once the buffers exist (`Trk`). -/
theorem ret_of_trk {W1 W : World} {H1 H : Heap} {b : Nat} {s1 s' : GzState} {z1 z' : ZStream}
    (hs1 : W1.gz H1 b = some s1) (hz1 : H1.streams s1.strm = some z1) (T : Trk W1 H1 b s1 z1 W H s' z') :
    Ret W1 H1 W H b := by
  obtain ⟨hx', fx, -, -, -, -, -, -, mk, hst⟩ := T
  have hs' := hx'.1
  have hz' : H.streams s1.strm = some z' := by rw [← fx.fix.strm]; exact hx'.2.1
  refine ret_mk hs1 hs' fx.path mk fun c hc => Or.inl ?_
  rw [gzOwned_eq hs']
  have e : stBlk H s' = stBlk H1 s1 := by simp [stBlk, fx.fix.strm, hz', hz1, hst]
  simp only [List.mem_append] at hc ⊢
  rcases hc with h1 | h1
  · exact Or.inl (Or.inr (by rw [fx.buffers]; exact h1))
  · exact Or.inr (by rw [e]; exact h1)

/-- The step between the actual heaps of a `Trk`. -/
theorem gstep_of_trk {W1 W : World} {H1 H : Heap} {b : Nat} {s1 s' : GzState} {z1 z' : ZStream}
    (hx1 : GzWX W1 H1 b s1 z1) (T : Trk W1 H1 b s1 z1 W H s' z') : GStep W1 H1 W H b [] := by
  have hz' : H.streams s1.strm = some z' := by rw [← T.2.1.fix.strm]; exact T.1.2.1
  exact gstep_unflat (a := flatZ z1) (a' := flatZ z') hx1.1 T.1.1 hx1.2.1 hz' rfl rfl T.2.1.fix.strm T.2.2.2.1

/-- **`gz_comp`** on a write handle with the invariant keeps every block of the entry or frees it. -/
theorem comp_keep (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (flush : Int32) :
    GSat w h (gz_comp (some b) flush) (fun _ W H => Ret w h W H b) := by
  obtain ⟨ψ, Gr, hP⟩ := psi_of G
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  have P := DeflatePublic.dpending
  rw [gz_comp_eq, compAll_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hsz : s.size = 0
  · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simp [hsz]) hc)
    refine GSat.bind (GSat.mono (gsat_and (gz_write_init_spec G hv hs hsz) (init_keep G hv hs hsz))
      fun r W1 H1 q => ?_)
    obtain ⟨⟨s1, hs1, hv1, g1, -, fx1, hr⟩, s1', hs1', hp1, hm1, dk1⟩ := q
    rw [hs1] at hs1'; cases hs1'
    have R1 : Ret w h W1 H1 b := ret_mk hs hs1 hp1 hm1 fun c hc =>
      Or.inr (dk1.2 c (sh.dead hsz c hc).2 (sh.dead hsz c hc).1)
    apply GSat.ite
    · intro _; exact GSat.pure R1
    · intro hc
      have hsz1 : s1.size ≠ 0 := by
        rcases hr with ⟨-, h1⟩ | rfl
        · exact h1
        · simp at hc
      obtain ⟨z1, hx1, -⟩ := wx_of_inv hv1 hs1 hsz1
      have e1 : s1.strm = s.strm := fx1.strm
      rw [← e1]
      refine GSat.mono (rest_spec P hP G hx1 flush) fun r W H q => ?_
      obtain ⟨s', z', T, -⟩ := q
      exact Ret.trans R1 (ret_of_trk hs1 hx1.2.1 T) hs1 (gstep_of_trk hx1 T)
        (fun c hc => Nat.lt_of_lt_of_le (own_lt hv hs c hc) (GStep.next g1))
  · refine GSat.ite (fun hc => absurd (by simpa using hc) hsz) (fun _ => ?_)
    obtain ⟨z1, hx, -⟩ := wx_of_inv hv hs hsz
    exact GSat.mono (rest_spec P hP G hx flush) fun r W H q => by
      obtain ⟨s', z', T, -⟩ := q
      exact ret_of_trk hs hx.2.1 T

/-! ## `gz_zero` -/

/-- `Ret` across a change that keeps `path`, the message, the buffers and the stream's state block. -/
theorem ret_same {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hp : s'.path = s.path) (hm : s'.msg = s.msg) (hb : s'.buffers = s.buffers)
    (hst : stBlk H s' = stBlk h s) : Ret w h W H b :=
  ret_mk hs hs' hp (Or.inl hm) fun c hc => Or.inl (by
    rw [gzOwned_eq hs']
    simp only [List.mem_append] at hc ⊢
    rcases hc with h1 | h1
    · exact Or.inl (Or.inr (by rw [hb]; exact h1))
    · exact Or.inr (by rw [hst]; exact h1))

theorem zero_tail_preK (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0) (n : UInt32)
    (hn1 : n.toNat ≤ s1.size.toNat) (hn2 : (n.toNat : Int) ≤ s1.skip.toInt) (first : Int32) :
    GSat W H (zeroTail (some b) (some s1.strm) n first) (fun r W' H' => (∃ s2, W'.gz H' b = some s2 ∧
      GzInvWS W' H' (some b) ∧ GStep W H W' H' b [] ∧ ZFix s1 s2 ∧ s2.size ≠ 0 ∧
      s2.pos.toInt + s2.skip.toInt = s1.pos.toInt + s1.skip.toInt ∧ s2.skip.toInt = s1.skip.toInt - n.toNat ∧
      r.1 = first ∧ (r.2 = .go ∨ r.2 = .ret)) ∧ Ret W H W' H' b) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  have hP := sh.pos
  unfold zeroTail
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s1.strm { z with avail_in := n })
    (by simp [lm_app, wrZ_app hz]) ?_)
  have hs1 : W.gz (setZ H s1.strm { z with avail_in := n }) b = some s1 := hs
  refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
    (h' := setZ H s1.strm { z with next_in := .ref (.heap c) base, avail_in := n })
    (by simp [lm_app, wrZ_app (setZ_streams_same H s1.strm _), InflateInv.upd_upd]) ?_)
  obtain ⟨hv2, hs2, g2⟩ := invWS_setIn hv hs hsz hz (.ref (.heap c) base) n (fun c' base' hb => by
    have e := hb.buffers; rw [hB.buffers] at e; cases e
    exact Or.inl ⟨0, by simp, Nat.le_refl _, by omega⟩)
  have hsk0 := hP.skip_nonneg
  have hps := hP.pos_skip
  have hpl := hP.pos_lower
  have hpw := hP.write_pos hwm
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.pos.toInt + n.toNat))
    (by simp only [lm_app, chkI64_ok (v := s1.pos.toInt + n.toNat) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app hs2 _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' (gz_upd_same hs2 _) _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.skip.toInt - n.toNat))
    (by simp only [lm_app, chkI64_ok (v := s1.skip.toInt - n.toNat) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app (gz_upd_same hs2 _) _) ?_)
  simp only [InflateInv.upd_upd]
  have hp1 : (Int64.ofInt (s1.pos.toInt + n.toNat)).toInt = s1.pos.toInt + n.toNat :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hk1 : (Int64.ofInt (s1.skip.toInt - n.toNat)).toInt = s1.skip.toInt - n.toNat :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  obtain ⟨sh2, hn2'⟩ := inv_of hs2 hv2.1
  have sh3 := shape_posW sh2 hwm (Int64.ofInt (s1.pos.toInt + n.toNat)) (Int64.ofInt (s1.skip.toInt - n.toNat))
    ⟨by dsimp only; rw [hk1]; omega, by dsimp only; rw [hp1, hk1]; omega, by dsimp only; rw [hp1]; omega,
      fun _ => by dsimp only; rw [hp1]; omega⟩
  obtain ⟨hv3, hs3, g3⟩ := invWS_store hv2 hs2 sh3 hn2' hwm rfl (fun c' hc _ => by
    simp only [GzOwned, gz_upd_same hs2, hs2] at hc ⊢; exact hc)
  have R3 := ret_same hs hs3 rfl rfl rfl (by simp [stBlk, setZ, hz])
  have g23 := g2.trans g3 ⟨s1, hs⟩ ⟨s1, hs2⟩
  refine GSat.bind (GSat.mono (gsat_and (comp_inv C G hv3 hs3 _) (comp_keep G hv3 hs3 _)) fun r W4 H4 q => ?_)
  obtain ⟨⟨s4, z4, hs4, hz4, hv4, g4, fx, hsz4, -, -⟩, R4⟩ := q
  have R := Ret.trans R3 R4 hs3 g4 (fun c hc => Nat.lt_of_lt_of_le (own_lt hv hs c hc) (GStep.next g23))
  have g := g23.trans g4 ⟨s1, hs⟩ ⟨_, hs3⟩
  have hsz' : s4.size ≠ 0 := by rw [hsz4 hsz]; exact hsz
  have z34 := ZFix.of_w fx
  have zf : ZFix s1 s4 := ⟨z34.want, z34.direct, z34.mode, z34.level, z34.strategy, z34.fd, z34.strm⟩
  have e1 : s4.pos.toInt = s1.pos.toInt + n.toNat := by rw [fx.pos]; exact hp1
  have e2 : s4.skip.toInt = s1.skip.toInt - n.toNat := by rw [fx.skip]; exact hk1
  refine GSat.ite (fun _ => GSat.pure ⟨⟨s4, hs4, hv4, g, zf, hsz', by omega, e2, rfl, Or.inr rfl⟩, R⟩)
    (fun _ => GSat.pure ⟨⟨s4, hs4, hv4, g, zf, hsz', by omega, e2, rfl, Or.inl rfl⟩, R⟩)

theorem zero_bodyK (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0) (hsk : 0 < s1.skip.toInt)
    (st : Int32 × Ctl) :
    GSat W H (zeroBody (some b) (some s1.strm) st) (fun r W' H' => (ZRound W H b s1 W' H' ∧
      (r.2 = .go ∨ r.2 = .ret)) ∧ Ret W H W' H' b) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  obtain ⟨hn1, hn2, hn3⟩ := zero_n s1.size s1.skip (by rw [hsw]; exact sh.want_lo) (by rw [hsw]; exact sh.want_hi) hsk
  have tail : ∀ (H' : Heap) (first : Int32), GzInvWS W H' (some b) → W.gz H' b = some s1 → GStep W H W H' b [] →
      Ret W H W H' b →
      GSat W H' (zeroTail (some b) (some s1.strm)
        (if GT_OFF s1.size || Int64.ofNat s1.size.toNat > s1.skip then s1.skip.toUInt64.toUInt32 else s1.size) first)
        (fun r W' H'' => (ZRound W H b s1 W' H'' ∧ (r.2 = .go ∨ r.2 = .ret)) ∧ Ret W H W' H'' b) := by
    intro H' first hv' hs' g' R'
    refine GSat.mono (zero_tail_preK C G hv' hs' hsz _ hn2 hn3 first) fun r W2 H2 q => ?_
    obtain ⟨⟨s2, hs2, hv2, g2, zf, hsz2, hps, hk, -, hr⟩, R2⟩ := q
    exact ⟨⟨⟨s2, hs2, hv2, g'.trans g2 ⟨s1, hs⟩ ⟨s1, hs'⟩, zf, hsz2, hps, by omega⟩, hr⟩,
      Ret.trans R' R2 hs' g2 (fun c hc => Nat.lt_of_lt_of_le (own_lt hv hs c hc) (GStep.next g'))⟩
  unfold zeroBody
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => ?_) (fun _ => tail H _ hv hs (GStep.refl W H b []) (Ret.refl W H b))
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  obtain ⟨H1, e1, x1⟩ := memset_hbuf (off := base) hd 0 (if GT_OFF s1.size || Int64.ofNat s1.size.toNat > s1.skip
    then s1.skip.toUInt64.toUInt32 else s1.size).toNat (by have := sh.want_hi; simp only [outSize, hwm] at hds; omega)
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := H1) (by rw [lm_app, e1]) ?_)
  obtain ⟨hcb, hp, hst, hown⟩ := bufBlk hs hn hsz hB
  obtain ⟨hv1, hs1, g1⟩ := invWS_hbuf hv hs x1 hcb hp hst hown
  have R1 : Ret W H W H1 b := by
    obtain ⟨tt, rfl, -⟩ := x1
    exact ret_same hs hs1 rfl rfl rfl (by simp [stBlk])
  exact tail H1 _ hv1 hs1 g1 R1

theorem zero_loopK (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip ≠ 0) (hs0 : ∃ s0, w.gz h b = some s0) (first : Int32)
    (R : Ret w h W H b) (hlt : ∀ c ∈ GzOwned w h (some b), c < h.nextBlk) :
    GSat W H (gdoWhile (zeroBody (some b) (some s.strm)) (zeroCond (some b)) (first, Ctl.go))
      (fun lp W' H' => ∃ s2, W'.gz H' b = some s2 ∧ GzInvWS W' H' (some b) ∧ GStep w h W' H' b [] ∧ ZFix s s2 ∧
        s2.size ≠ 0 ∧ (lp.2 = .go → s2.skip = 0) ∧ (lp.2 = .go ∨ lp.2 = .ret) ∧ Ret w h W' H' b) := by
  have pos0 : ∀ {W : World} {H : Heap} {s2 : GzState}, GzInvWS W H (some b) → W.gz H b = some s2 →
      0 ≤ s2.skip.toInt := fun hv hs => (GzInv.pos hs hv.1).skip_nonneg
  refine gsat_gdoWhile (fun st W H => st.2 = .go ∧ ∃ s1, W.gz H b = some s1 ∧ GzInvWS W H (some b) ∧
      GStep w h W H b [] ∧ ZFix s s1 ∧ s1.size ≠ 0 ∧ s1.skip ≠ 0 ∧ Ret w h W H b)
    (fun _ W H => match W.gz H b with | some s1 => s1.skip.toInt.toNat | none => 0) _ ?_
    ⟨rfl, s1, hs, hv, g, zf, hsz, hsk, R⟩ ?_
  · rintro st W1 H1 ⟨-, s2, hs2, hv2, g2, zf2, hsz2, hsk2, R2⟩
    have hk : 0 < s2.skip.toInt := by
      have := pos0 hv2 hs2
      rcases Int.lt_or_eq_of_le this with h' | h'
      · exact h'
      · exact absurd (Int64.toInt_inj.mp (by rw [← h']; rfl)) hsk2
    rw [← zf2.strm]
    refine GSat.mono (zero_bodyK C G hv2 hs2 hsz2 hk st) fun r W3 H3 q => ?_
    obtain ⟨⟨⟨s3, hs3, hv3, g3, zf3, hsz3, hps3, hlt3⟩, hr⟩, R3⟩ := q
    have g' := g2.trans g3 hs0 ⟨s2, hs2⟩
    have R' := Ret.trans R2 R3 hs2 g3 (fun c hc => Nat.lt_of_lt_of_le (hlt c hc) (GStep.next g2))
    unfold zeroCond
    have h0 := pos0 hv3 hs3
    rcases hr with hr | hr
    · refine GSat.ite (fun hc => by simp [hr] at hc) (fun _ => ?_)
      refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
      refine GSat.pure ⟨fun e => ⟨⟨hr, s3, hs3, hv3, g', zf2.trans zf3, hsz3, by simpa using e, R'⟩, ?_⟩,
        fun e => ⟨s3, hs3, hv3, g', zf2.trans zf3, hsz3, fun _ => by simpa using e, Or.inl hr, R'⟩⟩
      simp only [hs3, hs2]
      omega
    · refine GSat.ite (fun _ => GSat.pure ⟨fun e => by simp at e, fun _ => ⟨s3, hs3, hv3, g', zf2.trans zf3, hsz3,
        fun e => by simp [hr] at e, Or.inr hr, R'⟩⟩) (fun hc => by simp [hr] at hc)
  · simp only [hs]
    have : s1.skip.toInt < 2 ^ 63 := s1.skip.toInt_lt
    unfold fuel; omega

theorem zero_restK (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip ≠ 0) (hs0 : ∃ s0, w.gz h b = some s0) (R : Ret w h W H b)
    (hlt : ∀ c ∈ GzOwned w h (some b), c < h.nextBlk) :
    GSat W H (zeroRest (some b) (some s.strm)) (fun r W' H' => ZeroPost w h b s r W' H' ∧ Ret w h W' H' b) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  have loop : ∀ {W2 : World} {H2 : Heap} {s2 : GzState}, GzInvWS W2 H2 (some b) → W2.gz H2 b = some s2 →
      GStep w h W2 H2 b [] → ZFix s s2 → s2.size ≠ 0 → s2.skip ≠ 0 → Ret w h W2 H2 b →
      GSat W2 H2 (do
        let lp ← gdoWhile (zeroBody (some b) (some s.strm)) (zeroCond (some b)) ((1 : Int32), Ctl.go)
        if lp.2 == .ret then
          return -1
        return 0) (fun r W' H' => ZeroPost w h b s r W' H' ∧ Ret w h W' H' b) := by
    intro W2 H2 s2 hv2 hs2 g2 zf2 hsz2 hsk2 R2
    refine GSat.bind (GSat.mono (zero_loopK C G hv2 hs2 g2 zf2 hsz2 hsk2 hs0 1 R2 hlt) fun lp W3 H3 q => ?_)
    obtain ⟨s3, hs3, hv3, g3, zf3, hsz3, hgo, hr, R3⟩ := q
    refine GSat.ite (fun _ => GSat.pure ⟨⟨s3, hs3, hv3, g3, zf3, Or.inr rfl, fun e => by simp at e⟩, R3⟩)
      (fun hc => GSat.pure ⟨⟨s3, hs3, hv3, g3, zf3, Or.inl rfl, fun _ => ⟨hgo ?_, hsz3⟩⟩, R3⟩)
    rcases hr with hr | hr
    · exact hr
    · simp [hr] at hc
  unfold zeroRest
  rw [← zf.strm]
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.ite (fun _ => ?_) (fun _ => by rw [zf.strm]; exact loop hv hs g zf hsz hsk R)
  refine GSat.bind (GSat.mono (gsat_and (comp_inv C G hv hs _) (comp_keep G hv hs _)) fun r W2 H2 q => ?_)
  obtain ⟨⟨s2, z2, hs2, hz2, hv2, g2, fx, hsz2, hr, -⟩, R2⟩ := q
  have g' := g.trans g2 hs0 ⟨s1, hs⟩
  have R' := Ret.trans R R2 hs g2 (fun c hc => Nat.lt_of_lt_of_le (hlt c hc) (GStep.next g))
  have zf2 : ZFix s s2 := zf.trans (ZFix.of_w fx)
  refine GSat.ite (fun _ => GSat.pure ⟨⟨s2, hs2, hv2, g', zf2, Or.inr rfl, fun e => by simp at e⟩, R'⟩) (fun _ => ?_)
  rw [zf.strm]
  exact loop hv2 hs2 g' zf2 (by rw [hsz2 hsz]; exact hsz) (by rw [fx.skip]; exact hsk) R'

/-- **`gz_zero`** on a write handle with a pending skip: `ZeroPost`, and every block of the entry is kept or freed. -/
theorem gz_zero_keep (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (hsk : s.skip ≠ 0) :
    GSat w h (gz_zero (some b)) (fun r W H => ZeroPost w h b s r W H ∧ Ret w h W H b) := by
  have C := gz_comp_spec
  have hlt := own_lt hv hs
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  rw [gz_zero_eq']
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hz : s.size = 0
  · refine GSat.ite (fun _ => ?_) (fun hc => by simp [hz] at hc)
    refine GSat.bind (GSat.mono (gsat_and (gz_write_init_spec G hv hs hz) (init_keep G hv hs hz)) fun r W H q => ?_)
    obtain ⟨⟨s', hs', hv', g, -, fx, hr⟩, s'', hs'', hp1, hm1, dk1⟩ := q
    rw [hs'] at hs''; cases hs''
    have R1 : Ret w h W H b := ret_mk hs hs' hp1 hm1 fun c hc =>
      Or.inr (dk1.2 c (sh.dead hz c hc).2 (sh.dead hz c hc).1)
    refine GSat.ite (fun _ => GSat.pure ⟨⟨s', hs', hv', g, ZFix.of_w fx, Or.inr rfl, fun e => by simp at e⟩, R1⟩)
      (fun hc => ?_)
    rcases hr with ⟨rfl, hsz⟩ | rfl
    · exact zero_restK C G hv' hs' g (ZFix.of_w fx) hsz (by rw [fx.skip]; exact hsk) ⟨s, hs⟩ R1 hlt
    · simp at hc
  · refine GSat.ite (fun hc => by simp at hc; exact absurd hc hz) (fun _ => ?_)
    exact zero_restK C G hv hs (GStep.refl w h b []) (ZFix.refl s) hz hsk ⟨s, hs⟩ (Ret.refl w h b) hlt

/-! ## The close -/

/-- The end of `gzclose_w` from `gz_error(state, Z_OK, NULL)` on (`gzwrite.c:509-514`), with the result so far
`ret0`. -/
def closeEndW (b : Nat) (ret0 : Int32) : G Int32 := do
  let mut ret := ret0
  gz_error (some b) ZlibNg.Inflate.Z_OK .null
  lm (freeB (← (← ldGz (some b)).path.get))
  if (← closeG (← rdG (some b) (·.fd))) == -1 then
    ret := Z_ERRNO
  gz_state_free (some b)
  return ret

/-- The end of `gzclose_w` from `if (state->size)` on (`gzwrite.c:503-514`). -/
def closeTailW (b : Nat) (ret0 : Int32) : G Int32 := do
  if (← rdG (some b) (·.size)) != 0 then
    if (← rdG (some b) (·.direct)) == 0 then
      let _ ← lm (ZlibNg.Deflate.deflateEnd (← strmOf (some b)))
    gz_buffer_free (some b)
  closeEndW b ret0

/-- `gzclose_w` from `gz_comp(state, Z_FINISH)` on (`gzwrite.c:499-514`). -/
def compPartW (b : Nat) (ret0 : Int32) : G Int32 := do
  let mut ret := ret0
  if (← gz_comp (some b) ZlibNg.Inflate.Z_FINISH) == -1 then
    ret := (← rdG (some b) (·.err))
  closeTailW b ret

theorem gzclose_w_eq (b : Nat) : gzclose_w (some b) = (do
    if (← rdG (some b) (·.mode)) != GZ_WRITE then return ZlibNg.Inflate.Z_STREAM_ERROR
    let mut ret : Int32 := ZlibNg.Inflate.Z_OK
    if (← rdG (some b) (·.skip)) != 0 then
      if (← gz_zero (some b)) == -1 then
        ret := (← rdG (some b) (·.err))
    compPartW b ret) := rfl

theorem closeEndW_ok {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} {cp : Nat} {dp : Array UInt8}
    (hs : W.gz H b = some s) (hm : GzMsg H s) (hmb : ∀ c o, s.msg = .val (.ref (.heap c) o) → c ≠ b)
    (hp : s.path = .val (.ref (.heap cp) 0)) (hdp : H.bytes cp = some dp) (hcpb : cp ≠ b) (hcpm : cp ∉ blkOf s.msg)
    (hz : H.streams s.strm = some z) (r0 : Int32) :
    ∃ r, GzRun (closeEndW b r0) W H r
      { W with fs := (W.fs.closeCall s.fd).2, gzs := upd W.gzs b none } (closeH H s cp b s.strm) := by
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbm : b ∉ blkOf s.msg := by
    intro hb
    unfold blkOf at hb; split at hb
    · next c o e => simp at hb; exact hmb c o e hb.symm
    · simp at hb
  have hdbM : (freeMsg H s).bytes b = some db := by rw [freeMsg_bytes H s b hbm]; exact hdb
  have hdpM : (freeMsg H s).bytes cp = some dp := by rw [freeMsg_bytes H s cp hcpm]; exact hdp
  have hdbP : (freeH (freeMsg H s) cp).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcpb)]; exact hdbM
  have hzB : (freeH (freeH (freeMsg H s) cp) b).streams s.strm = some z := by
    simp only [freeH]; rw [freeMsg_streams]; exact hz
  have e := gz_error_null_app hs hm hmb ZlibNg.Inflate.Z_OK
  have hl4 := ldGz_live hdbP { W with fs := (W.fs.closeCall s.fd).2, gzs := upd W.gzs b (some (errSt s ZlibNg.Inflate.Z_OK)) }
    (errSt s ZlibNg.Inflate.Z_OK) (by simp)
  simp [errSt, hp] at hl4
  refine ⟨if (W.fs.closeCall s.fd).1 = -1 then Z_ERRNO else r0, ?_⟩
  simp only [GzRun, C.run, StateT.run]
  by_cases hc : (W.fs.closeCall s.fd).1 = -1 <;>
  simp [hc, closeEndW, e, ldGz_upd hdbM, errSt, hp, Ival.get, liftM, monadLift, MonadLift.monadLift,
    freeB_app hdpM, rdG_upd hdbP, closeG, modifyFs, gz_state_free, gzStateFree, hl4, freeB_app hdbP,
    InflateInv.upd_upd, dropStream, hzB, closeH] <;>
  simp [freeH, freeMsg_streams]

/-- What the end of `gzclose_w` leaves, from `W`, `H` and the state `s` there. -/
def TailOK (W : World) (H : Heap) (b : Nat) (s : GzState) (W' : World) (H' : Heap) : Prop :=
  GzFrame W H W' H' (some b) [] ∧ (∀ c ∈ GzOwned W H (some b), H'.bytes c = none) ∧
    (∀ c, H.bytes c = none → H'.bytes c = none) ∧ W'.gzs b = none ∧ H'.streams s.strm = none ∧
    W'.fs.ofile? s.fd = none

theorem tail_fin {W W' : World} {H H2 : Heap} {b cp : Nat} {s s' : GzState}
    (hs : W.gz H b = some s)
    (hown : ∀ x, x ∈ GzOwned W H (some b) ↔ x = b ∨ x = cp ∨ x ∈ blkOf s.msg ∨ x ∈ blkOf s.buffers ++ stBlk H s)
    (h2b : ∀ x, x ∉ blkOf s.buffers ++ stBlk H s → H2.bytes x = H.bytes x)
    (h2n : ∀ x, H.bytes x = none → H2.bytes x = none)
    (h2o : ∀ x ∈ blkOf s.buffers ++ stBlk H s, H2.bytes x = none)
    (o1 : H2.consts = H.consts) (o2 : H2.istates = H.istates) (o3 : H2.iallocs = H.iallocs)
    (o4 : H2.dstates = H.dstates) (o5 : H2.dallocs = H.dallocs) (o6 : H2.crcTable = H.crcTable)
    (o7 : H2.x2nTable = H.x2nTable) (o8 : H2.baseAddr = H.baseAddr) (o9 : H2.nextBlk = H.nextBlk)
    (o10 : H2.gzheaders = H.gzheaders) (h2st : ∀ i, i ≠ s.strm → H2.streams i = H.streams i)
    (hm2 : GzMsg H2 s') (em : s'.msg = s.msg) (est : s'.strm = s.strm) (efd : s'.fd = s.fd)
    (hW2 : ∀ c, c ≠ b → W'.gzs c = W.gzs c) :
    TailOK W H b s { W' with fs := (W'.fs.closeCall s'.fd).2, gzs := upd W'.gzs b none } (closeH H2 s' cp b s'.strm) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := closeH_other H2 s' cp b s'.strm
  have hmsg : ∀ x, x ∉ blkOf s'.msg ↔ x ∉ blkOf s.msg := fun x => by rw [em]
  refine ⟨gzframe_gen (fun x hx => ?_) (fun i hi => ?_) (p1.trans o1) (p2.trans o2) (p3.trans o3) (p4.trans o4)
    (p5.trans o5) (p6.trans o6) (p7.trans o7) (p8.trans o8) (p9.trans o9) (p10.trans o10) (fun c hc _ => ?_),
    fun x hx => ?_, fun x hx => ?_, by simp, ?_, ?_⟩
  · have hx' := fun h' => hx ((hown x).mpr h')
    rw [(closeH_bytes H2 s' cp b s'.strm x).1 ⟨fun e => hx' (Or.inr (Or.inl e)), fun e => hx' (Or.inl e),
      (hmsg x).mpr fun e => hx' (Or.inr (Or.inr (Or.inl e)))⟩]
    exact h2b x fun e => hx' (Or.inr (Or.inr (Or.inr e)))
  · have hi' := hi b s rfl hs
    rw [p11, est, upd_ne _ _ _ _ hi']; exact h2st i hi'
  · have hcb : c ≠ b := fun e => hc (by rw [e])
    simp [upd_ne _ _ _ _ hcb, hW2 c hcb]
  · rcases (hown x).mp hx with h1 | h1 | h1 | h1
    · exact (closeH_bytes H2 s' cp b s'.strm x).2.1 (Or.inr h1)
    · exact (closeH_bytes H2 s' cp b s'.strm x).2.1 (Or.inl h1)
    · exact (closeH_bytes H2 s' cp b s'.strm x).2.2.2 hm2 (by rw [em]; exact h1)
    · exact (closeH_bytes H2 s' cp b s'.strm x).2.2.1 (h2o x h1)
  · exact (closeH_bytes H2 s' cp b s'.strm x).2.2.1 (h2n x hx)
  · rw [p11, est]; simp
  · show (W'.fs.closeCall s'.fd).2.ofile? s.fd = none
    rw [efd]; exact closeCall_ofile _ _

/-- **The end of `gzclose_w`** on a write handle with the invariant: it releases every block of the file. -/
theorem closeTailW_ok {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b))
    (hs : W.gz H b = some s) (r0 : Int32) :
    GSat W H (closeTailW b r0) (fun _ W' H' => TailOK W H b s W' H') := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨cp, np, hcp, r1, off0, dp, e0, hdp, -⟩ := sh.path
  cases e0
  have hdp' : H.bytes cp = some dp := hdp
  obtain ⟨hcpb, hcpm, hbm, hrest, hnd2⟩ := nodup_parts hcp hn
  have hmb := msg_ne_b hn
  obtain ⟨z, hz⟩ := sh.strm
  obtain ⟨db, hdb⟩ := gz_live hs
  have hown : ∀ x, x ∈ GzOwned W H (some b) ↔
      x = b ∨ x = cp ∨ x ∈ blkOf s.msg ∨ x ∈ blkOf s.buffers ++ stBlk H s := by
    intro x
    have e : GzOwned W H (some b) = [b] ++ [cp] ++ blkOf s.msg ++ blkOf s.buffers ++ stBlk H s := by
      simp only [GzOwned, hs, hcp]; rfl
    rw [e]; simp only [List.mem_append, List.mem_singleton, or_assoc]
  unfold closeTailW
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  dsimp only
  by_cases hsz : s.size = 0
  · refine GSat.ite (fun hc => absurd (by simpa using hc) (by simp [hsz])) (fun _ => ?_)
    obtain ⟨r, e⟩ := closeEndW_ok hs sh.msg hmb hcp hdp' hcpb hcpm hz r0
    refine ⟨r, _, _, e, tail_fin hs hown (fun _ _ => rfl) (fun _ e => e) (fun x hx => (sh.dead hsz x hx).1)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl) sh.msg rfl rfl rfl (fun _ _ => rfl)⟩
  · obtain ⟨c, base, z0, hB, hz0, WB⟩ := (sh.write hwm).bufs hsz
    rw [hz] at hz0; cases hz0
    obtain ⟨d, hd, hds⟩ := hB.fits
    have hcL : c ∈ blkOf s.buffers ++ stBlk H s := by simp [hB.buffers, blkOf]
    obtain ⟨hcb, hccp, hcm⟩ := hrest hsz c hcL
    refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simpa using hsz) hc)
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    -- the common part after the stream: `gz_buffer_free` and the end
    have fin : ∀ (H1 : Heap), H1.bytes c = some d → H1.savedPtrs c = some (base - 8, .ref (.heap c) 0) →
        H1.bytes b = some db → (∀ x, x ∉ blkOf s.buffers ++ stBlk H s → H1.bytes x = H.bytes x) →
        (∀ x, H.bytes x = none → H1.bytes x = none) → (∀ x ∈ stBlk H s, H1.bytes x = none) →
        H1.consts = H.consts → H1.istates = H.istates → H1.iallocs = H.iallocs → H1.dstates = H.dstates →
        H1.dallocs = H.dallocs → H1.crcTable = H.crcTable → H1.x2nTable = H.x2nTable →
        H1.baseAddr = H.baseAddr → H1.nextBlk = H.nextBlk → H1.gzheaders = H.gzheaders →
        (∀ i, i ≠ s.strm → H1.streams i = H.streams i) → (∃ z1, H1.streams s.strm = some z1) →
        GSat W H1 (do gz_buffer_free (some b); closeEndW b r0) (fun _ W' H' => TailOK W H b s W' H') := by
      intro H1 hd1 hsv1 hdb1 h1b h1n h1st o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 h1s ⟨z1, hz1⟩
      have hs1 : W.gz H1 b = some s := by unfold World.gz at hs ⊢; rw [hdb1]; rw [hdb] at hs; exact hs
      have hdbF : (freeH H1 c).bytes b = some db := by rw [freeH_bytes_ne (Ne.symm hcb)]; exact hdb1
      have hs2 : ({ W with gzs := upd W.gzs b (some (bfSt s)) } : World).gz (freeH H1 c) b = some (bfSt s) := by
        unfold World.gz; rw [hdbF]; simp
      have hsF : W.gz (freeH H1 c) b = some s := by unfold World.gz at hs ⊢; rw [hdbF]; rw [hdb] at hs; exact hs
      have hcm' : ∀ x ∈ blkOf s.msg, x ∉ blkOf s.buffers ++ stBlk H s := fun x hx hx' =>
        (hrest hsz x hx').2.2 hx
      have hm2 : GzMsg (freeH H1 c) (bfSt s) := by
        refine ⟨?_, sh.msg.mem⟩
        rcases sh.msg.msg with e | hm
        · exact Or.inl e
        · refine Or.inr (ownBlk_keep hm fun x hx => ?_)
          rw [freeH_bytes_ne (fun e => hcm (by rw [← e]; exact hx))]; exact h1b x (hcm' x hx)
      have hdp2 : (freeH H1 c).bytes cp = some dp := by
        rw [freeH_bytes_ne (Ne.symm hccp), h1b cp fun hx => (hrest hsz cp hx).2.1 rfl]; exact hdp'
      have hz2 : (freeH H1 c).streams (bfSt s).strm = some z1 := hz1
      obtain ⟨r, e⟩ := closeEndW_ok hs2 hm2 hmb hcp hdp2 hcpb hcpm hz2 r0
      have ho8 := hB.hdr.1
      refine GSat.bind (GSat.of_eq (a := ()) (w' := { W with gzs := upd W.gzs b (some (bfSt s)) })
        (h' := freeH H1 c) ?_ ⟨r, _, _, e, ?_⟩)
      · simp [gz_buffer_free, ldGz_app hs1, hB.buffers, Ival.get, liftM, monadLift, MonadLift.monadLift,
          free_aligned_app hd1 (by omega) ho8 hsv1, wrG_upd hdbF, wrG_app hsF, InflateInv.upd_upd, bfSt]
      · refine tail_fin hs hown (fun x hx => ?_) (fun x hx => freeH_none (h1n x hx)) (fun x hx => ?_)
          (by simp [freeH, o1]) (by simp [freeH, o2]) (by simp [freeH, o3]) (by simp [freeH, o4])
          (by simp [freeH, o5]) (by simp [freeH, o6]) (by simp [freeH, o7]) (by simp [freeH, o8])
          (by simp [freeH, o9]) (by simp [freeH, o10]) (fun i hi => by simp [freeH, h1s i hi]) hm2 rfl rfl rfl
          (fun c' hc' => by simp [upd_ne _ _ _ _ hc'])
        · rw [freeH_bytes_ne (fun e => hx (by rw [e]; exact hcL))]; exact h1b x hx
        · simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · rw [hB.buffers] at hx; simp [blkOf] at hx; subst hx; exact freeH_bytes_eq _ _
          · exact freeH_none (h1st x hx)
    by_cases hd0 : s.direct = 0
    · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simpa using hd0) hc)
      obtain ⟨i, z1, sb, r, e1, hz1, hsb, he⟩ := DeflateControl.deflateEnd_inv (WB.deflate hd0).1
      cases e1; rw [hz] at hz1; cases hz1
      have hsbL : sb ∈ blkOf s.buffers ++ stBlk H s := by simp [stBlk, hz, hsb]
      have hcsb : c ≠ sb := by
        have := hnd2 hsz
        rw [hB.buffers] at this
        simp [blkOf, stBlk, hz, hsb] at this
        exact this
      obtain ⟨hsbb, -, -⟩ := hrest hsz sb hsbL
      refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
      refine GSat.bind (GSat.lm ⟨r, _, he, ?_⟩)
      refine (fin _ (by simp [upd_ne _ _ _ _ hcsb, hd]) (by simp [upd_ne _ _ _ _ hcsb, hB.hdr.2])
        (by simp [upd_ne _ _ _ _ hsbb.symm, hdb]) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun j hj => by simp [upd_ne _ _ _ _ hj]) ⟨{ z with state := none }, by simp⟩)
      · have : x ≠ sb := fun e => hx (e ▸ hsbL)
        simp [upd_ne _ _ _ _ this]
      · by_cases e : x = sb
        · subst e; simp
        · simp [upd_ne _ _ _ _ e, hx]
      · simp [stBlk, hz, hsb] at hx; subst hx; simp
    · refine GSat.ite (fun hc => absurd (by simpa using hc) hd0) (fun _ => ?_)
      have hns : stBlk H s = [] := by simp [stBlk, hz, WB.nostate hd0]
      exact fin H hd hB.hdr.2 hdb (fun _ _ => rfl) (fun _ e => e) (by rw [hns]; simp)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl) ⟨z, hz⟩

/-! ## `gzclose_w` -/

/-- A step of the file followed by a frame of the file is a frame of the file. -/
theorem gzframe_comp {w W1 W2 : World} {h H1 H2 : Heap} {b : Nat} {s s1 : GzState} (g : GStep w h W1 H1 b [])
    (hs : w.gz h b = some s) (hs1 : W1.gz H1 b = some s1) (f : GzFrame W1 H1 W2 H2 (some b) []) :
    GzFrame w h W2 H2 (some b) [] := by
  obtain ⟨⟨⟨f1, d1⟩, c1, g1⟩, o1, t1⟩ := g
  obtain ⟨⟨f2, d2⟩, c2, g2⟩ := f
  have k1 : h.nextBlk ≤ H1.nextBlk := f1.2.2.2.2.2.2.2.2.2
  simp only [hs, hs1] at f1 f2
  rw [t1 s s1 hs hs1] at f2
  have f2' := frame_consts f2 h.consts
  have hL : ∀ c ∈ GzOwned W1 H1 (some b), c < h.nextBlk → c ∈ GzOwned w h (some b) := o1
  refine ⟨⟨?_, fun c hc hc' => ?_⟩, fun k a e => c2 k a (c1 k a e), fun b' hb' hlt => (g2 b' hb' (by omega)).trans
    (g1 b' hb' hlt)⟩
  · simp only [hs]
    exact frame_trans f1 f2' hL
  · have hc2 : c ∉ GzOwned W1 H1 (some b) := fun m => hc' (hL c m hc)
    exact ⟨(d2 c (by omega) hc2).1.trans (d1 c hc hc').1, (d2 c (by omega) hc2).2.trans (d1 c hc hc').2⟩

/-- What `gzclose_w` leaves: the frame and the release of the file. -/
def CloseQ (w : World) (h : Heap) (b : Nat) (_r : Int32) (W : World) (H : Heap) : Prop :=
  GzFrame w h W H (some b) [] ∧ GzReleased w h W H (some b)

theorem comp_part_ok (G : DeflateGz) {w W1 : World} {h H1 : Heap} {b : Nat} {s s1 : GzState}
    (hv1 : GzInvWS W1 H1 (some b)) (hs1 : W1.gz H1 b = some s1) (g1 : GStep w h W1 H1 b [])
    (R1 : Ret w h W1 H1 b) (hs : w.gz h b = some s) (hlt : ∀ c ∈ GzOwned w h (some b), c < h.nextBlk)
    (hfd : s1.fd = s.fd) (r0 : Int32) :
    GSat W1 H1 (compPartW b r0) (CloseQ w h b) := by
  obtain ⟨ψ, Gr, hP⟩ := psi_of G
  obtain ⟨sh1, -⟩ := inv_of hs1 hv1.1
  obtain ⟨z1, hz1⟩ := sh1.strm
  have fin : ∀ (W2 : World) (H2 : Heap) (s2 : GzState), GzInvWS W2 H2 (some b) → W2.gz H2 b = some s2 →
      GStep W1 H1 W2 H2 b [] → Ret W1 H1 W2 H2 b → s2.fd = s1.fd → ∀ r1,
      GSat W2 H2 (closeTailW b r1) (CloseQ w h b) := by
    intro W2 H2 s2 hv2 hs2 g2 R2 hfd2 r1
    have g12 := g1.trans g2 ⟨s, hs⟩ ⟨s1, hs1⟩
    have R := Ret.trans R1 R2 hs1 g2 (fun c hc => Nat.lt_of_lt_of_le (hlt c hc) (GStep.next g1))
    have hst : s2.strm = s.strm := g12.strm s s2 hs hs2
    refine GSat.mono (closeTailW_ok hv2 hs2 r1) fun _ W H T => ⟨gzframe_comp g12 hs hs2 T.1, ?_⟩
    intro b' s' e1 e2
    cases e1; rw [hs] at e2; cases e2
    refine ⟨fun c hc => ?_, T.2.2.2.1, by rw [← hst]; exact T.2.2.2.2.1, by rw [← hfd, ← hfd2]; exact T.2.2.2.2.2⟩
    rcases R c hc with m | d
    · exact T.2.1 c m
    · exact T.2.2.1 c d
  unfold compPartW
  refine GSat.bind (GSat.mono (gsat_and (gz_comp_spec G ψ Gr hP W1 H1 b ZlibNg.Inflate.Z_FINISH s1 z1 hs1 hz1
    (Or.inl hv1)) (comp_keep G hv1 hs1 _)) fun r W2 H2 q => ?_)
  obtain ⟨⟨s2, z2, hs2, -, fx, -, g2, -, -, -, -, hinv, -⟩, R2⟩ := q
  have hv2 := hinv hv1
  dsimp only
  refine GSat.ite (fun _ => ?_) (fun _ => fin W2 H2 s2 hv2 hs2 g2 R2 fx.fd _)
  refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
  exact fin W2 H2 s2 hv2 hs2 g2 R2 fx.fd _

/-- **`gzclose_w` of a write handle** returns, stays in the frame of the file, and releases every block the file
owned at entry, given the obligations of the deflate side (`DeflateGz`). The proposition is `CloseW` of
`Proof/public-gz-open.lean`, stated here without that import. -/
theorem closeW_of (G : DeflateGz) : ∀ (w : World) (h : Heap) (b : Nat) (s : GzState), GzWF w h →
    GzInvWS w h (some b) → w.gz h b = some s →
    ∃ r w' h', GzRun (gzclose_w (some b)) w h r w' h' ∧ GzFrame w h w' h' (some b) [] ∧
      GzReleased w h w' h' (some b) := by
  intro w h b s _ hv hs
  have hwm := modeOf hs hv.2.1
  have hlt := own_lt hv hs
  suffices H : GSat w h (gzclose_w (some b)) (CloseQ w h b) by
    obtain ⟨r, W, H', e, f, rel⟩ := H
    exact ⟨r, W, H', e, f, rel⟩
  rw [gzclose_w_eq]
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hc => absurd hwm (by simpa using hc)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  dsimp only
  refine GSat.ite (fun hk => ?_) (fun _ => comp_part_ok G hv hs (GStep.refl w h b []) (Ret.refl w h b) hs hlt rfl _)
  refine GSat.bind (GSat.mono (gz_zero_keep G hv hs (by simpa using hk)) fun r W1 H1 q => ?_)
  obtain ⟨⟨s1, hs1, hv1, g1, zf, -, -⟩, R1⟩ := q
  refine GSat.ite (fun _ => ?_) (fun _ => comp_part_ok G hv1 hs1 g1 R1 hs hlt zf.fd _)
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  exact comp_part_ok G hv1 hs1 g1 R1 hs hlt zf.fd _

end ZlibNgF.Proof.GzWrite
