import ZlibNgF.Proof.«gzwrite.c.compok»

/-!
# `gz_comp` meets its specification (`ZlibNgF`)

`gz_comp_spec_of`: `GzCompSpec` from the pending obligations of the deflate side. The proof follows `gz_comp`:
`gz_write_init` when there are no buffers yet (`init_strm` adds what it does to the stream and `reset`), then on a
handle in the state `GzWX` (`compRest`): the direct `write`, or the `deflateReset` of a pending reset
(`reset_stepX`), the loop (`loop_spec`) and the store of `reset` for `Z_FINISH`. `Trk` collects the facts these
steps keep; `rest_spec` gives them for `compRest`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- Two facts of the same deterministic run. -/
theorem gsat_and {α : Type} {w : World} {h : Heap} {m : G α} {P Q : α → World → Heap → Prop}
    (p : GSat w h m P) (q : GSat w h m Q) : GSat w h m (fun a W H => P a W H ∧ Q a W H) := by
  obtain ⟨a, W, H, e, pa⟩ := p
  obtain ⟨a', W', H', e', qa⟩ := q
  rw [e] at e'
  simp only [Except.ok.injEq, Prod.mk.injEq] at e'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e'
  exact ⟨a, W, H, e, pa, qa⟩

/-- A step between the actual heaps is one between heaps that differ from them in the record of the file's stream
(with the same `state` field). -/
theorem gstep_flat {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') {z z' a a' : ZStream} (hz : h.streams s.strm = some z)
    (hz' : H.streams s.strm = some z') (ha : a.state = z.state) (ha' : a'.state = z'.state) (hst : s'.strm = s.strm)
    (g : GStep w h W H b []) : GStep w (setZ h s.strm a) W (setZ H s.strm a') b [] := by
  have hsF : w.gz (setZ h s.strm a) b = some s := hs
  have hsF' : W.gz (setZ H s.strm a') b = some s' := hs'
  refine gstep_unflat hsF hsF' (setZ_streams_same _ _ _) (setZ_streams_same _ _ _) ha.symm ha'.symm hst ?_
  rw [setZ_setZ, setZ_setZ, setZ_self hz, setZ_self hz']
  exact g

/-! ## The stream across `gz_write_init` -/

/-- `gz_error` on a write handle keeps the streams. -/
theorem gz_error_streamsW {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ _ H => H.streams = h.streams) := by
  have hlit : LitOk w h := hv.2.2.lit
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, -, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hn hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, -⟩ := err0_keep sh hn e
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, -, -, -, -, -, x, -, -⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  exact ⟨r, W, H, by rw [gz_error_run hs sh.msg (msg_ne_b hn) e msg]; exact eq,
    x.streams.trans (freeMsg_streams h s)⟩

/-- `gz_error(state, e, lit)` on a write handle keeps the streams. -/
theorem gzlit_err_streams (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hl : gzLits[i]? = some lit) (hn : NoNul lit) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (e : Int32) {α : Type} (r : α) :
    GSat w h (do gz_error (some b) e (← gzLit lit); pure r) (fun _ _ H => H.streams = h.streams) := by
  refine GSat.bind (GSat.mono (gzLit_spec lit i hi hl hn hv.2.2.lit) fun p W1 H1 q => ?_)
  obtain ⟨hg, -, x, hL, hc, hk⟩ := q
  obtain ⟨hv1, hs1, -⟩ := invWS_ext hv hs x hg hL
  refine GSat.bind (GSat.mono (gz_error_streamsW hv1 hs1 e p (Or.inr ⟨_, hc⟩) hk) fun _ W H q => ?_)
  exact GSat.pure (q.trans x.streams)

/-- `gz_buffer_alloc` on a write handle without buffers keeps the streams. -/
theorem alloc_streams {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hz : s.size = 0) :
    GSat w h (gz_buffer_alloc (some b)) (fun _ _ H => H.streams = h.streams) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  cases hok : h.allocOk h.nalloc with
  | true =>
    have hfr : h.bytes h.nextBlk = none := (hv.2.2.2.1.1 h.nextBlk (Nat.le_refl _)).2.2
    exact ⟨_, _, _, gz_buffer_alloc_okW hs hwm sh.want_lo sh.want_hi hfr hok, (HExt.alloc_aligned h _ _).streams⟩
  | false =>
    obtain ⟨v1, s1, -⟩ := invWS_bf hv hs hz
    obtain ⟨r, W, H, e, q⟩ := gzlit_err_streams "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom v1 s1
      ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)
    exact ⟨r, W, H, by rw [gz_buffer_alloc_failW hs hwm hok]; exact e, q⟩

/-- What `gz_write_init` does to the stream and to `reset`: `avail_in` stays (it is 0), `next_in` too on a direct
handle, and `reset` stays. -/
def InitS (b : Nat) (s : GzState) (z : ZStream) (W : World) (H : Heap) : Prop :=
  ∃ s1 z1, W.gz H b = some s1 ∧ s1.reset = s.reset ∧ H.streams s.strm = some z1 ∧ z1.avail_in = z.avail_in ∧
    (s.direct ≠ 0 → z1.next_in = z.next_in)

open ZlibNgF.Proof.GzWriteNeeds in
/-- **`gz_write_init`**: the stream and `reset` (`InitS`). -/
theorem init_strm (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (hz : s.size = 0) (hzs : h.streams s.strm = some z) :
    GSat w h (gz_write_init (some b)) (fun _ W H => InitS b s z W H) := by
  unfold gz_write_init
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.mono (gsat_and (gz_buffer_alloc_specW hv hs hz) (alloc_streams hv hs hz))
    fun r W1 H1 q => ?_)
  obtain ⟨q, hst1⟩ := q
  rcases q with ⟨rfl, s1, hs1, he1, hv1, -, -⟩ | ⟨rfl, hok, rfl, rfl⟩
  · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by decide) hc)
    refine GSat.mono (gsat_and (gz_error_litW "out of memory" 0 GzReach.lit_oom lit_oom_get nonul_oom hv1 hs1
      ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32)) (gzlit_err_streams "out of memory" 0 GzReach.lit_oom lit_oom_get
      nonul_oom hv1 hs1 ZlibNg.Inflate.Z_MEM_ERROR (-1 : Int32))) fun r' W H q => ?_
    obtain ⟨⟨-, s2, hs2, he2, -⟩, hst2⟩ := q
    refine ⟨s2, z, hs2, ?_, by rw [hst2, hst1]; exact hzs, rfl, fun _ => rfl⟩
    rw [(errOf_keep he2).2.2.2.2.2.2.2.2.1, (errOf_keep he1).2.2.2.2.2.2.2.2.1]; rfl
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
      rw [hzs] at hz0; cases hz0
      have hz1 : (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))).streams s.strm = some z := by
        rw [x.streams]; exact hzs
      have hfr1 : DFreshBlocks (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) :=
        ⟨x.fresh fr, fun c e' => by rw [x.dstates, x.dallocs]; exact hv.2.2.2.1.2 c (by simp [alH] at e'; omega)⟩
      have hi1 : DInitReady (alH h (8 + wBytes s + 64) (alOff (h.baseAddr (.heap h.nextBlk)))) (some s.strm) :=
        Or.inr ⟨z, ⟨s.strm, rfl, hz1⟩, hza, hzf⟩
      obtain ⟨r, H2, e, f⟩ := init2__run _ (some s.strm) (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).level
        ZlibNg.Inflate.Z_DEFLATED.toUInt32.toInt32 (ZlibNg.Inflate.MAX_WBITS + 16) ZlibNg.Deflate.DEF_MEM_LEVEL
        (baStW s h.nextBlk (alOff (h.baseAddr (.heap h.nextBlk)))).strategy SIZEOF_Z_STREAM.toInt32 hfr1 hi1
      obtain ⟨z2, ⟨i2, e2, hz2⟩, -, hai2, -⟩ := G.1 _ H2 (some s.strm) _ _ _ _ _ _ _ r z ⟨s.strm, rfl, hz1⟩ hi1 hfr1
        (by simpa [C.run] using e)
      cases e2
      refine GSat.bind (GSat.lm ⟨r, H2, e, ?_⟩)
      have hb2 : H2.bytes b = h.bytes b := by
        rw [frame_bytes_eq f.1 (by simp [alH]; omega) (List.not_mem_nil), (x.old b hbn).1]
      by_cases hr : r = ZlibNg.Inflate.Z_OK
      · subst hr
        refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
        obtain ⟨z', hz2', -, hs3, -⟩ := invWS_initOk G hv hs hz hd e
        rw [hz2] at hz2'; cases hz2'
        let p : BPtr := .ref (.heap h.nextBlk) (alOff (h.baseAddr (.heap h.nextBlk)) + 2 * s.want.toNat)
        let z3 : ZStream := { z2 with next_in := .null, avail_out := s.want, next_out := p }
        refine ⟨0, _, _, ?_, _, z3, hs3, by simp [baStW], by simp; rfl, hai2, fun hc => absurd hd hc⟩
        have hd2 : H2.bytes b = some db := by rw [hb2, hdb]
        simp [ZlibNg.Inflate.wrZ, ZlibNg.Inflate.rdZ, ldStream, stStream, hz2, rdG_updS hd2, ldGz_updS hd2,
          wrG_updS hd2, Ival.get, liftM, monadLift, MonadLift.monadLift,
          InflateInv.upd_upd, baStW, hd]
      · refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simpa using hr) hc)
        obtain ⟨d, hdc, hod, hsv, -, hv3, hs3, -⟩ := invWS_initFail G hv hs hz e hr
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
                (do gz_error (some b) e (← gzLit lit); pure (-1 : Int32)) (fun _ W H => InitS b s z W H) := by
            intro lit i e hi hl hn
            refine GSat.mono (gsat_and (gz_error_litW lit i hi hl hn hv3 hs3 e (-1 : Int32))
              (gzlit_err_streams lit i hi hl hn hv3 hs3 e (-1 : Int32))) fun r' W H q => ?_
            obtain ⟨⟨-, s4, hs4, he4, -⟩, hst4⟩ := q
            refine ⟨s4, z2, hs4, ?_, by rw [hst4]; exact hz2, hai2, fun hc => absurd hd hc⟩
            rw [(errOf_keep he4).2.2.2.2.2.2.2.2.1]; rfl
          refine GSat.ite (fun _ => hfin _ 0 _ GzReach.lit_oom lit_oom_get nonul_oom) (fun _ => ?_)
          exact hfin "invalid compression parameters" 1 _ (by simp [gzLits, List.findIdx?_cons]) (by decide) (by decide)
    · refine GSat.ite (fun hc => absurd (by simpa [baStW] using hc) hd) (fun _ => ?_)
      exact GSat.pure ⟨_, z, hs1, by simp [baStW], by rw [x.streams]; exact hzs, rfl, fun _ => rfl⟩

/-! ## The facts kept once the buffers exist -/

/-- The fields of the state that `gz_comp` keeps once the buffers exist (all but `reset`, `next`, `msg`, `err`,
`have`). -/
structure CFix (s s' : GzState) : Prop where
  fix : WFix s s'
  size : s'.size = s.size
  buffers : s'.buffers = s.buffers
  inp : s'.«in» = s.«in»
  out : s'.out = s.out
  path : s'.path = s.path

theorem CFix.refl (s : GzState) : CFix s s := ⟨WFix.refl s, rfl, rfl, rfl, rfl, rfl⟩

theorem CFix.trans {s1 s2 s3 : GzState} (a : CFix s1 s2) (b : CFix s2 s3) : CFix s1 s3 :=
  ⟨a.1.trans b.1, b.2.trans a.2, b.3.trans a.3, b.4.trans a.4, b.5.trans a.5, b.6.trans a.6⟩

theorem inOk_congr {s s' : GzState} {z : ZStream} (hb : s'.buffers = s.buffers) (hsz : s'.size = s.size)
    (hd : s'.direct = s.direct) (hi : InOk s z) : InOk s' z := by
  obtain ⟨c, base, eb, hi⟩ := hi
  refine ⟨c, base, by rw [hb]; exact eb, ?_⟩
  simp only [InpOk] at hi ⊢; rw [hsz, hd]; exact hi

/-- The input of a write handle with the invariant and buffers is where `GzWBuf.inp` allows. -/
theorem inOk_of_inv {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) (hz : h.streams s.strm = some z) : InOk s z := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨c, base, z0, hB, hz0, WB⟩ := (sh.write hwm).bufs hsz
  rw [hz] at hz0; cases hz0
  exact ⟨c, base, hB.buffers, WB.inp⟩

/-- The facts that `gz_comp` keeps once the buffers exist, from `W1`, `H1`, `s1`, `z1` to `W`, `H`, `s'`, `z'`. -/
def Trk (W1 : World) (H1 : Heap) (b : Nat) (s1 : GzState) (z1 : ZStream) (W : World) (H : Heap) (s' : GzState)
    (z' : ZStream) : Prop :=
  GzWX W H b s' z' ∧ CFix s1 s' ∧ FdWrites s1.fd W1.fs W.fs ∧
    GStep W1 (setZ H1 s1.strm (flatZ z1)) W (setZ H s1.strm (flatZ z')) b [] ∧ z'.avail_in ≤ z1.avail_in ∧
    (s1.direct = 0 → Adv z1.next_in z'.next_in (z1.avail_in.toNat - z'.avail_in.toNat)) ∧
    (s1.direct ≠ 0 → z'.next_in = z1.next_in) ∧ (InOk s1 z1 → InOk s' z') ∧ MKeep s1 s' H ∧ z'.state = z1.state

theorem Trk.refl {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z) :
    Trk W H b s z W H s z :=
  ⟨hx, CFix.refl s, FdWrites.refl _ _, GStep.refl _ _ _ _, UInt32.le_refl _,
    fun _ => by simpa using adv_zero z.next_in, fun _ => rfl, id, Or.inl rfl, rfl⟩

theorem Trk.trans {W1 W2 W3 : World} {H1 H2 H3 : Heap} {b : Nat} {s1 s2 s3 : GzState} {z1 z2 z3 : ZStream}
    (a : Trk W1 H1 b s1 z1 W2 H2 s2 z2) (hs1 : W1.gz H1 b = some s1) (c : Trk W2 H2 b s2 z2 W3 H3 s3 z3) :
    Trk W1 H1 b s1 z1 W3 H3 s3 z3 := by
  obtain ⟨hx2, f1, d1, g1, a1, v1, n1, o1, m1, t1⟩ := a
  obtain ⟨hx3, f2, d2, g2, a2, v2, n2, o2, m2, t2⟩ := c
  have mono := wx_mono hx2 g2
  have hst : s2.strm = s1.strm := f1.fix.strm
  have hfd : s2.fd = s1.fd := f1.fix.fd
  have hdd : s2.direct = s1.direct := f1.fix.direct
  rw [hst] at g2; rw [hfd] at d2
  have l1 := UInt32.le_iff_toNat_le.mp a1
  have l2 := UInt32.le_iff_toNat_le.mp a2
  refine ⟨hx3, f1.trans f2, d1.trans d2, g1.trans g2 ⟨s1, hs1⟩ ⟨s2, hx2.1⟩, UInt32.le_trans a2 a1, fun hd => ?_,
    fun hd => (n2 (by rw [hdd]; exact hd)).trans (n1 hd), fun hi => o2 (o1 hi), m1.trans m2 mono, t2.trans t1⟩
  have := adv_trans (v1 hd) (v2 (by rw [hdd]; exact hd))
  have e : z1.avail_in.toNat - z2.avail_in.toNat + (z2.avail_in.toNat - z3.avail_in.toNat) =
      z1.avail_in.toNat - z3.avail_in.toNat := by omega
  rw [e] at this; exact this

theorem trk_lfacts {w0 W : World} {h0 H : Heap} {b : Nat} {s0 s : GzState} {z0 z : ZStream} (hd : s0.direct = 0)
    (F : LFacts w0 h0 b s0 z0 W H s z) : Trk w0 h0 b s0 z0 W H s z :=
  ⟨F.1, ⟨F.2.1.fix, F.2.1.size, F.2.1.buffers, F.2.1.inp, F.2.1.out, F.2.1.path⟩, F.2.2.1, F.2.2.2.1, F.2.2.2.2.1,
    fun _ => F.2.2.2.2.2.1, fun h => absurd hd h, F.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2⟩

/-- `gz_error` in the state `GzWX`. -/
theorem trk_err {W W' : World} {H H' : Heap} {b : Nat} {s : GzState} {z : ZStream} {e : Int32}
    (hx : GzWX W H b s z) (q : ErrPostX W H b s z e W' H')
    (hf : ∀ c ∈ blkOf s.msg, H'.bytes c = none ∧ c < H'.nextBlk) : ∃ s', Trk W H b s z W' H' s' z ∧ ErrOf s e s' := by
  obtain ⟨s', hx', he, hfs, g⟩ := wx_err hx q
  obtain ⟨-, k2, k3, k4, k5, -, -, k8, -, -, -⟩ := errOf_keep he
  exact ⟨s', ⟨hx', ⟨WFix.of_err he, k2, k3, k4, k5, errOf_path he⟩, by rw [hfs]; exact FdWrites.refl _ _, g,
    UInt32.le_refl _, fun _ => by simpa using adv_zero z.next_in, fun _ => rfl, inOk_congr k3 k2 k8, Or.inr hf, rfl⟩,
    he⟩

/-- **A store of `reset`** into a write handle in the state `GzWX`. -/
theorem wx_reset {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z) (v : Int32) :
    GzWX { W with gzs := upd W.gzs b (some { s with reset := v }) } H b { s with reset := v } z ∧
      GStep W (setZ H s.strm (flatZ z)) { W with gzs := upd W.gzs b (some { s with reset := v }) }
        (setZ H s.strm (flatZ z)) b [] := by
  obtain ⟨hs, hz, hsz, hv, hX⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hsF hv.1
  have sh' : GzShape (setZ H s.strm (flatZ z)) { s with reset := v } :=
    shape_congr sh ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨sh.msg.1, sh.msg.2⟩
  obtain ⟨v', -, g⟩ := invWS_store hv hsF sh' hn hwm rfl (fun c hc _ => by
    simp only [GzOwned, gz_upd_same hsF, hsF] at hc ⊢; exact hc)
  have h1 : ({ W with gzs := upd W.gzs b (some { s with reset := v }) } : World).gz H b =
      some { s with reset := v } := gz_upd_same hs _
  have hown : GzOwned { W with gzs := upd W.gzs b (some { s with reset := v }) } H (some b) =
      GzOwned W H (some b) := by
    simp only [GzOwned, h1, hs]
  refine ⟨⟨h1, hz, hsz, v', ?_⟩, g⟩
  rcases hX with ⟨c, base, eb, hi⟩ | ⟨hr, ho⟩
  · exact Or.inl ⟨c, base, eb, hi⟩
  · exact Or.inr ⟨hr, fun c hc => by rw [hown] at hc; exact ho c hc⟩

theorem trk_reset {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z) (v : Int32) :
    Trk W H b s z { W with gzs := upd W.gzs b (some { s with reset := v }) } H { s with reset := v } z :=
  ⟨(wx_reset hx v).1, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, FdWrites.refl _ _,
    (wx_reset hx v).2, UInt32.le_refl _, fun _ => by simpa using adv_zero z.next_in, fun _ => rfl,
    inOk_congr rfl rfl rfl, Or.inl rfl, rfl⟩

/-- The buffer block of a write handle in the state `GzWX`. -/
theorem wx_buf {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z) :
    ∃ c base d, s.buffers = .val (.ref (.heap c) base) ∧ H.bytes c = some d ∧ base + inSize s ≤ d.size := by
  obtain ⟨hs, -, hsz, hv, -⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, -⟩ := inv_of hsF hv.1
  obtain ⟨c, base, zF, hB, -, -⟩ := (sh.write hwm).bufs hsz
  obtain ⟨d, hdc, hds⟩ := hB.fits
  exact ⟨c, base, d, hB.buffers, hdc, by omega⟩

/-- The input of a write handle in the state `GzWX` is readable. -/
theorem wx_read {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z) :
    z.avail_in.toUInt64 = 0 ∨ ∃ r off a, z.next_in = .ref r off ∧ Space.get H r = some a ∧
      off + z.avail_in.toUInt64.toNat ≤ a.size := by
  obtain ⟨c, base, d, eb, hdc, hle⟩ := wx_buf hx
  rcases hx.2.2.2.2 with ⟨c1, base1, eb1, hi⟩ | ⟨⟨r, off, a, ep, ha, hle'⟩, -⟩
  · rw [eb] at eb1
    simp only [Ival.val.injEq, Ptr.ref.injEq, BRef.heap.injEq] at eb1
    obtain ⟨rfl, rfl⟩ := eb1
    rcases hi with ⟨k, ek, -, hk⟩ | ⟨e1, -⟩
    · exact Or.inr ⟨.heap c, base + k, d, ek, hdc, by simp only [UInt32.toNat_toUInt64]; omega⟩
    · exact Or.inl (by rw [e1]; rfl)
  · exact Or.inr ⟨r, off, a, ep, ha, by simp only [UInt32.toNat_toUInt64]; exact hle'⟩

/-! ## `deflateReset` -/

/-- **`deflateReset`** on the stream of a write handle in the state `GzWX` (not direct): no fault, the buffer
fields stay, and `GzWX` again, with a step of the file between the flat heaps. -/
theorem reset_stepX (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream}
    (hx : GzWX W H b s z) (hd : s.direct = 0) :
    ∃ r H' z', ZlibNg.Deflate.deflateReset (some s.strm) H = .ok (r, H') ∧ H'.streams s.strm = some z' ∧
      BufSame z z' ∧ GzWX W H' b s z' ∧ GStep W (setZ H s.strm (flatZ z)) W (setZ H' s.strm (flatZ z')) b [] := by
  obtain ⟨hs, hz, hsz, hv, hin⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, -⟩ := inv_of hsF hv.1
  obtain ⟨c, base, zF, hB, hzF, WB⟩ := (sh.write hwm).bufs hsz
  rw [setZ_streams_same] at hzF; cases hzF
  obtain ⟨hdiF, hsideF⟩ := WB.deflate hd
  have hHe : setZ (setZ H s.strm (flatZ z)) s.strm z = H := by rw [setZ_setZ]; exact setZ_self hz
  have hnhF : ∀ sb0 st0 k, (flatZ z).state = some sb0 → (setZ H s.strm (flatZ z)).dstate sb0 = some st0 →
      st0.gzhead ≠ .val (some k) := fun sb0 st0 k e1 e2 => WB.nohdr sb0 st0 k e1 e2
  obtain ⟨hdi, -⟩ := dinv_setZ (a := z) (setZ_streams_same _ _ _) (flat_eq z) hdiF hsideF hnhF
  rw [hHe] at hdi
  obtain ⟨i, z0, sb, e0, hz0, hsb, r, H', e, -, hdi', f, hfo⟩ := DeflateReset.reset_inv hdi
  cases e0; rw [hz] at hz0; cases hz0
  obtain ⟨z', ⟨i', e1, hz'⟩, hsame, hk⟩ := G.2.1 H H' (some s.strm) r z hdi ⟨_, rfl, hz⟩ (by simpa [C.run] using e)
  cases e1
  obtain ⟨n1, n2, n3, n4, n5⟩ := hsame
  have f' : DFrame H H' [s.strm] [sb] [] [] := by simpa [streamIds] using f
  have fF := dframe_setZ f' (flatZ z) (flatZ z')
  have hst' : (flatZ z').state = (flatZ z).state := n5
  have hkF := dkeep_setZ hz hz' rfl rfl hk (a := flatZ z) (a' := flatZ z')
  have hside' := DeflateSide.side_fresh hdi' hfo
  have hnh' : ∀ sb0 st0 k, z'.state = some sb0 → H'.dstate sb0 = some st0 → st0.gzhead ≠ .val (some k) := by
    intro sb0 st0 k e1 e2 e3
    rcases hk.2.2 (some k) ⟨sb0, st0, ⟨⟨z', ⟨_, rfl, hz'⟩, e1⟩, e2⟩, e3⟩ with e4 | e4
    · cases e4
    · obtain ⟨b0, st1, ⟨⟨z1, ⟨i1, e5, hz1⟩, hb0⟩, hst1⟩, hg1⟩ := e4
      cases e5; rw [hz] at hz1; cases hz1
      exact WB.nohdr b0 st1 k hb0 hst1 hg1
  have hdiF' := dinv_setZ (a := flatZ z') hz' (flat_eq' z') hdi' hside' hnh'
  have houtF : ∃ ko kx, (flatZ z').next_out = .ref (.heap c) (base + inSize s + ko) ∧
      s.next = .val (.ref (.heap c) (base + inSize s + kx)) ∧ kx ≤ ko ∧
      ko + (flatZ z').avail_out.toNat = s.size.toNat := by
    obtain ⟨ko, kx, a1, a2, a3, a4⟩ := WB.out hd
    refine ⟨ko, kx, ?_, a2, a3, ?_⟩
    · show z'.next_out = _; rw [n3]; exact a1
    · show ko + z'.avail_out.toNat = _; rw [n4]; exact a4
  obtain ⟨hv', hs', g⟩ := invWS_dcall hv hsF hsz hd hB (setZ_streams_same _ _ _) hsb fF
    (fun x hx => by simp at hx) (setZ_streams_same _ _ _) hst' (Or.inr ⟨rfl, rfl⟩) houtF hkF hdiF'
  have hsH' : W.gz H' b = some s := hs'
  refine ⟨r, H', z', e, hz', ⟨n1, n2, n3, n4, n5⟩, ⟨hsH', hz', hsz, hv', ?_⟩, g⟩
  rcases hin with ⟨c1, base1, eb, hi⟩ | hc
  · exact Or.inl ⟨c1, base1, eb, by rw [n1, n2]; exact hi⟩
  · exact Or.inr (callerIn_step g hv.2.2.2.1.1 (gzOwned_setZ W H b hs hz rfl)
      (gzOwned_setZ W H' b hsH' hz' rfl) hc (Or.inl n1) (fun _ => by rw [n2]; exact Nat.le_refl _))

theorem trk_bufsame {W : World} {H H' : Heap} {b : Nat} {s : GzState} {z z' : ZStream} (hx' : GzWX W H' b s z')
    (hs : BufSame z z') (g : GStep W (setZ H s.strm (flatZ z)) W (setZ H' s.strm (flatZ z')) b []) :
    Trk W H b s z W H' s z' := by
  obtain ⟨n1, n2, -, -, n5⟩ := hs
  refine ⟨hx', CFix.refl s, FdWrites.refl _ _, g, by rw [n2]; exact UInt32.le_refl _, fun _ => ?_, fun _ => n1,
    fun hi => ?_, Or.inl rfl, n5⟩
  · rw [n1, n2]; simpa using adv_zero z.next_in
  · obtain ⟨c, base, eb, hi⟩ := hi
    exact ⟨c, base, eb, by rw [n1, n2]; exact hi⟩

/-! ## `gz_comp` once the buffers exist -/

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The loop of `gz_comp` and what follows it (copied from the translation). -/
def compTail (state : GzPtr) (strm : StreamPtr) (flush : Int32) : G Int32 := do
  let ret : Int32 := Z_OK
  let lp ← gdoWhile (compBody state strm flush) compCond ⟨ret, 0, .go⟩
  if lp.ctl == .ret then
    return -1
  if flush == Z_FINISH then
    wrG state fun s => { s with reset := 1 }
  return 0

open ZlibNg.Inflate ZlibNg.Deflate in
/-- `gz_comp` after `gz_write_init` (copied from the translation). -/
def compRest (state : GzPtr) (strm : StreamPtr) (flush : Int32) : G Int32 := do
  if (← rdG state (·.direct)) != 0 then
    let got ← writeG (← rdG state (·.fd)) (← lm (rdZ strm (·.next_in))) (← lm (rdZ strm (·.avail_in))).toUInt64
    if got < 0 || got.toUInt64.toUInt32 != (← lm (rdZ strm (·.avail_in))) then
      gz_error state Z_ERRNO (← zstrerror)
      return -1
    lm (wrZ strm fun z => { z with avail_in := 0 })
    return 0
  if (← rdG state (·.reset)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) == 0 && flush == Z_NO_FLUSH then
      return 0
    let _ ← lm (deflateReset strm)
    wrG state fun s => { s with reset := 0 }
  compTail state strm flush

theorem compAll_eq (state : GzPtr) (flush : Int32) : compAll state flush = (do
    let strm ← strmOf state
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return -1
    compRest state strm flush) := rfl

/-- What `compTail` leaves, from `W`, `H`, `s`, `z`. -/
def TPost (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (W : World) (H : Heap) (b : Nat) (s : GzState)
    (z : ZStream) (r : Int32) (W' : World) (H' : Heap) : Prop :=
  ∃ s' z', Trk W H b s z W' H' s' z' ∧ (r = 0 ∨ r = -1) ∧
    (r = 0 → (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0) ∧ z'.avail_out ≠ 0 ∧
      pot ψ flush s.size.toNat H' s.strm ≤ pot ψ flush s.size.toNat H s.strm) ∧
    (flush ≠ ZlibNg.Inflate.Z_FINISH → s'.reset = s.reset)

/-- **`compTail`** on a write handle in the state `GzWX` (not direct). -/
theorem tail_specC (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) (flush : Int32) :
    GSat W H (compTail (some b) (some s.strm) flush) (TPost ψ flush W H b s z) := by
  unfold compTail
  refine GSat.bind (GSat.mono (loop_spec P hP hx hd flush) fun lp W2 H2 q => ?_)
  obtain ⟨s2, z2, F, hr⟩ := q
  have T := trk_lfacts hd F
  have hre2 : s2.reset = s.reset := F.2.1.reset
  apply GSat.ite
  · intro _
    exact GSat.pure ⟨s2, z2, T, Or.inr rfl, fun e => absurd e (by decide), fun _ => hre2⟩
  · intro hc
    rcases hr with e | ⟨-, pl, ao, ai⟩
    · simp [e] at hc
    apply GSat.ite
    · intro hf
      have hf' : flush = ZlibNg.Inflate.Z_FINISH := by simpa using hf
      refine GSat.bind (GSat.of_eq (wrG_app F.1.1 _) ?_)
      exact GSat.pure ⟨_, z2, T.trans hx.1 (trk_reset F.1 1), Or.inl rfl,
        fun _ => ⟨fun h => absurd hf' h, ao, pl⟩, fun h => absurd hf' h⟩
    · intro _
      exact GSat.pure ⟨s2, z2, T, Or.inl rfl, fun _ => ⟨ai, ao, pl⟩, fun _ => hre2⟩

/-- What `compRest` leaves, from `W`, `H`, `s`, `z`. -/
def RPost (ψ : Int32 → C.DeflateState → Nat) (flush : Int32) (W : World) (H : Heap) (b : Nat) (s : GzState)
    (z : ZStream) (r : Int32) (W' : World) (H' : Heap) : Prop :=
  ∃ s' z', Trk W H b s z W' H' s' z' ∧ (r = 0 ∨ r = -1) ∧
    (r = 0 → (flush ≠ ZlibNg.Inflate.Z_FINISH → z'.avail_in = 0) ∧
      (s.direct = 0 → flush ≠ ZlibNg.Deflate.Z_NO_FLUSH → z'.avail_out ≠ 0 ∧
        (flush ≠ ZlibNg.Inflate.Z_FINISH → s'.reset = 0))) ∧
    (flush ≠ ZlibNg.Inflate.Z_FINISH → s'.reset = s.reset ∨ s'.reset = 0) ∧
    (r = 0 → flush ≠ ZlibNg.Inflate.Z_FINISH → s.direct = 0 → s.reset = 0 →
      pot ψ flush s.size.toNat H' s.strm ≤ pot ψ flush s.size.toNat H s.strm)

/-- **`compRest`** on a write handle in the state `GzWX`. -/
theorem rest_spec (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat}
    (hP : DeflatePsi ψ Gr) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream}
    (hx : GzWX W H b s z) (flush : Int32) :
    GSat W H (compRest (some b) (some s.strm) flush) (RPost ψ flush W H b s z) := by
  have hs := hx.1
  have hz := hx.2.1
  unfold compRest
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hc
    have hd : s.direct ≠ 0 := by simpa using hc
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
    obtain ⟨r, bs, ew⟩ := writeG_fd W H s.fd z.next_in z.avail_in.toUInt64 (wx_read hx)
    refine GSat.bind (GSat.of_eq ew ?_)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
    have hx1 : GzWX { W with fs := (W.fs.writeCall s.fd bs).2 } H b s z := hx
    have T1 : Trk W H b s z { W with fs := (W.fs.writeCall s.fd bs).2 } H s z :=
      ⟨hx1, CFix.refl s, FdWrites.one _ _ _, gstep_fs (GStep.refl _ _ _ _) _, UInt32.le_refl _,
        fun _ => by simpa using adv_zero z.next_in, fun _ => rfl, id, Or.inl rfl, rfl⟩
    apply GSat.ite
    · intro _
      refine GSat.mono (gsat_and (gz_error_strX hz hx1.2.2.2.1 hx1.1 (-1 : Int32))
        (gz_error_strX_frees hz hx1.2.2.2.1 hx1.1 (-1 : Int32))) fun r' W2 H2 q => ?_
      obtain ⟨⟨rfl, q⟩, hfree⟩ := q
      obtain ⟨s2, T2, he⟩ := trk_err hx1 q hfree
      exact ⟨s2, z, T1.trans hs T2, Or.inr rfl, fun e => absurd e (by decide),
        fun _ => Or.inl (errOf_keep he).2.2.2.2.2.2.2.2.1, fun e => absurd e (by decide)⟩
    · intro _
      refine GSat.bind (GSat.lm ⟨(), _, wrZ_run hz _, ?_⟩)
      obtain ⟨c, base, d, eb, -, -⟩ := wx_buf hx
      have hx2 : GzWX { W with fs := (W.fs.writeCall s.fd bs).2 } (setZ H s.strm { z with avail_in := 0 }) b s
          { z with avail_in := 0 } :=
        ⟨hx1.1, setZ_streams_same _ _ _, hx.2.2.1, by rw [setZ_setZ]; exact hx1.2.2.2.1,
          Or.inl ⟨c, base, eb, Or.inr ⟨rfl, Or.inl hd⟩⟩⟩
      have T2 : Trk { W with fs := (W.fs.writeCall s.fd bs).2 } H b s z { W with fs := (W.fs.writeCall s.fd bs).2 }
          (setZ H s.strm { z with avail_in := 0 }) s { z with avail_in := 0 } :=
        ⟨hx2, CFix.refl s, FdWrites.refl _ _, by rw [setZ_setZ]; exact GStep.refl _ _ _ _,
          UInt32.le_iff_toNat_le.mpr (by simp), fun h => absurd h hd, fun _ => rfl,
          fun _ => ⟨c, base, eb, Or.inr ⟨rfl, Or.inl hd⟩⟩, Or.inl rfl, rfl⟩
      exact GSat.pure ⟨s, { z with avail_in := 0 }, T1.trans hs T2, Or.inl rfl,
        fun _ => ⟨fun _ => rfl, fun h => absurd h hd⟩, fun _ => Or.inl rfl, fun _ _ h => absurd h hd⟩
  · intro hc
    have hd : s.direct = 0 := by simpa using hc
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro hre
      have hre' : s.reset ≠ 0 := by simpa using hre
      refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
      apply GSat.ite
      · intro hc2
        have h2 : z.avail_in = 0 ∧ flush = ZlibNg.Deflate.Z_NO_FLUSH := by simpa using hc2
        exact GSat.pure ⟨s, z, Trk.refl hx, Or.inl rfl, fun _ => ⟨fun _ => h2.1, fun _ hf => absurd h2.2 hf⟩,
          fun _ => Or.inl rfl, fun _ _ _ h => absurd h hre'⟩
      · intro _
        obtain ⟨r, H', z', e, -, hsame, hx', g⟩ := reset_stepX G hx hd
        refine GSat.bind (GSat.lm ⟨r, H', e, ?_⟩)
        refine GSat.bind (GSat.of_eq (wrG_app hx'.1 _) ?_)
        have T := (trk_bufsame hx' hsame g).trans hs (trk_reset hx' 0)
        refine GSat.mono (tail_specC P hP (wx_reset hx' 0).1 hd flush) fun r W3 H3 q => ?_
        obtain ⟨s3, z3, T3, hr, h0, hrs⟩ := q
        exact ⟨s3, z3, T.trans hs T3, hr, fun e => ⟨(h0 e).1, fun _ _ => ⟨(h0 e).2.1, fun hf => (hrs hf)⟩⟩,
          fun hf => Or.inr (hrs hf), fun _ _ _ h => absurd h hre'⟩
    · intro hre
      have hre' : s.reset = 0 := by simpa using hre
      refine GSat.mono (tail_specC P hP hx hd flush) fun r W3 H3 q => ?_
      obtain ⟨s3, z3, T3, hr, h0, hrs⟩ := q
      exact ⟨s3, z3, T3, hr, fun e => ⟨(h0 e).1, fun _ _ => ⟨(h0 e).2.1, fun hf => (hrs hf).trans hre'⟩⟩,
        fun hf => Or.inl (hrs hf), fun e _ _ _ => (h0 e).2.2⟩

/-! ## `gz_comp` -/

/-- `CompPost` from `RPost` when the buffers existed at entry. -/
theorem post_bufs {ψ : Int32 → C.DeflateState → Nat} {flush : Int32} {w W : World} {h H : Heap} {b : Nat}
    {s : GzState} {z : ZStream} {r : Int32} (hx : GzWX w h b s z) (hinv : GzInvWS w h (some b) → InOk s z)
    (q : RPost ψ flush w h b s z r W H) : CompPost ψ w h b s z flush r W H := by
  obtain ⟨s', z', ⟨hx', fx, hfd, g, hai, hadv, hni, hok, -, -⟩, hr, h0, hrs, hpot⟩ := q
  have hz' : H.streams s.strm = some z' := by rw [← fx.fix.strm]; exact hx'.2.1
  have ga := gstep_unflat (a := flatZ z) (a' := flatZ z') hx.1 hx'.1 hx.2.1 hz' rfl rfl fx.fix.strm g
  exact ⟨s', z', hx'.1, hz', fx.fix, fun _ => ⟨fx.size, fx.buffers, fx.inp, fx.out⟩, ga, g, hfd,
    fun e => absurd (fx.size.symm.trans e) hx.2.2.1, fun _ => hx', fun hv => (inv_of_wx hx' (hok (hinv hv))).1, hai,
    fun _ => hadv, hni, hr, fun e => ⟨by rw [fx.size]; exact hx.2.2.1, (h0 e).1, (h0 e).2⟩, hrs,
    fun e1 e2 _ e3 e4 => hpot e1 e2 e3 e4⟩

/-- `CompPost` from `RPost` after a successful `gz_write_init`. -/
theorem post_init {ψ : Int32 → C.DeflateState → Nat} {flush : Int32} {w W1 W : World} {h H1 H : Heap} {b : Nat}
    {s s1 : GzState} {z z1 : ZStream} {r : Int32} (hs : w.gz h b = some s) (hz : h.streams s.strm = some z)
    (hsz : s.size = 0) (hs1 : W1.gz H1 b = some s1) (g1 : GStep w h W1 H1 b []) (hfs1 : W1.fs = w.fs)
    (fx1 : WFix s s1) (hre1 : s1.reset = s.reset) (hai1 : z1.avail_in = z.avail_in)
    (hni1 : s.direct ≠ 0 → z1.next_in = z.next_in) (hx1 : GzWX W1 H1 b s1 z1) (hok1 : InOk s1 z1)
    (q : RPost ψ flush W1 H1 b s1 z1 r W H) : CompPost ψ w h b s z flush r W H := by
  obtain ⟨s', z', ⟨hx', fx, hfd, g, hai, -, hni, hok, -, -⟩, hr, h0, hrs, -⟩ := q
  have e1 : s1.strm = s.strm := fx1.strm
  have hz' : H.streams s.strm = some z' := by rw [← e1, ← fx.fix.strm]; exact hx'.2.1
  have ga1 := gstep_unflat (z := z1) (z' := z') (a := flatZ z1) (a' := flatZ z') hx1.1 hx'.1 hx1.2.1 (by rw [e1]; exact hz') rfl rfl
    fx.fix.strm g
  have ga := g1.trans ga1 ⟨s, hs⟩ ⟨s1, hs1⟩
  have hst : s'.strm = s.strm := fx.fix.strm.trans e1
  refine ⟨s', z', hx'.1, hz', fx1.trans fx.fix, fun h => absurd hsz h, ga, gstep_flat hs hx'.1 hz hz' rfl rfl hst ga,
    by rw [← fx1.fd, ← hfs1]; exact hfd, fun e => absurd (fx.size.symm.trans e) hx1.2.2.1, fun _ => hx',
    fun _ => (inv_of_wx hx' (hok hok1)).1, by rw [← hai1]; exact hai, fun h => absurd hsz h,
    fun hd => by rw [hni (by rw [fx1.direct]; exact hd), hni1 hd], hr,
    fun e => ⟨by rw [fx.size]; exact hx1.2.2.1, (h0 e).1, fun hd => (h0 e).2 (by rw [fx1.direct]; exact hd)⟩,
    fun hf => by rw [← hre1]; exact hrs hf, fun _ _ h => absurd hsz h⟩

/-- **`gz_comp` meets `GzCompSpec`**, given the pending obligations of the deflate side. -/
theorem gz_comp_spec_of (P : DeflateReach.DPending) : GzCompSpec := by
  intro G ψ Gr hP w h b flush s z hs hz hin
  rw [gz_comp_eq, compAll_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hsz : s.size = 0
  · have hv : GzInvWS w h (some b) := hin.resolve_right fun hx => hx.2.2.1 hsz
    refine GSat.ite (fun _ => ?_) (fun hc => absurd (by simp [hsz]) hc)
    refine GSat.bind (GSat.mono (gsat_and (gz_write_init_spec G hv hs hsz) (init_strm G hv hs hsz hz))
      fun r W1 H1 q => ?_)
    obtain ⟨⟨s1, hs1, hv1, g1, hfs1, fx1, hr⟩, s1', z1, hs1', hre1, hz1, hai1, hni1⟩ := q
    rw [hs1] at hs1'; cases hs1'
    have e1 : s1.strm = s.strm := fx1.strm
    have hz1' : H1.streams s1.strm = some z1 := by rw [e1]; exact hz1
    have hgx : s1.size ≠ 0 → GzWX W1 H1 b s1 z1 := fun h1 => by
      obtain ⟨z2, hx2, -⟩ := wx_of_inv hv1 hs1 h1
      have := hx2.2.1
      rw [hz1'] at this; cases this
      exact hx2
    apply GSat.ite
    · intro hc
      have hr' : r = -1 := by simpa using hc
      subst hr'
      exact GSat.pure ⟨s1, z1, hs1, hz1, fx1, fun h => absurd hsz h, g1, gstep_flat hs hs1 hz hz1 rfl rfl e1 g1,
        by rw [hfs1]; exact FdWrites.refl _ _, fun _ => hv1, hgx, fun _ => hv1, by rw [hai1]; exact UInt32.le_refl _,
        fun h => absurd hsz h, hni1, Or.inr rfl, fun e => absurd e (by decide), fun _ => Or.inl hre1,
        fun e => absurd e (by decide)⟩
    · intro hc
      have hsz1 : s1.size ≠ 0 := by
        rcases hr with ⟨-, h1⟩ | rfl
        · exact h1
        · simp at hc
      have hx1 := hgx hsz1
      have hok1 := inOk_of_inv hv1 hs1 hsz1 hz1'
      rw [← e1]
      exact GSat.mono (rest_spec P hP G hx1 flush) fun r W H q =>
        post_init hs hz hsz hs1 g1 hfs1 fx1 hre1 hai1 hni1 hx1 hok1 q
  · refine GSat.ite (fun hc => absurd (by simpa using hc) hsz) (fun _ => ?_)
    have hx : GzWX w h b s z := by
      rcases hin with hv | hx
      · obtain ⟨z2, hx2, -⟩ := wx_of_inv hv hs hsz
        have := hx2.2.1
        rw [hz] at this; cases this
        exact hx2
      · exact hx
    exact GSat.mono (rest_spec P hP G hx flush) fun r W H q =>
      post_bufs hx (fun hv => inOk_of_inv hv hs hsz hz) q

end ZlibNgF.Proof.GzWrite
