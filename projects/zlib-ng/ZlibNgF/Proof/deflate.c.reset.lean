import ZlibNgF.Proof.«deflate.c.init»

/-!
# `deflateReset`, `deflateResetKeep` on an invariant stream (`ZlibNgF`)

From the runs on `SH` heaps in `Proof/deflate.c.init.lean`: on a stream with the structural invariant both calls
return `Z_OK`, keep the invariant and change only the stream record and the stream's block; on a stream that the
state check rejects they return `Z_STREAM_ERROR` and change nothing.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateReset
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat)
open ZlibNgF.Proof.InflateInv (upd_upd)

theorem upd_self {β : Type} (t : Tbl (Option β)) (k : Nat) (v : β) (h : t k = some v) : upd t k (some v) = t := by
  have hk : k < t.arr.size := Tbl.lt_size_of_get_ne t k (by rw [h]; simp [default])
  unfold upd Tbl.set
  simp only [hk, ite_true]
  congr 1
  apply Array.ext_getElem?
  intro x
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · rename_i e; subst e
    have := h; simp only [Tbl.get_eq] at this
    rw [Array.getElem?_eq_getElem hk] at this ⊢
    simp at this; simp [this]
  · rfl

theorem SH_self {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (hz : h.streams i = some z) (hs : h.dstates b = some st) (hd : h.bytes b = some d) : SH h i z b st d = h := by
  simp only [SH, upd_self _ _ _ hz, upd_self _ _ _ hs, upd_self _ _ _ hd]

theorem dframe_SH (h : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    DFrame h (SH h i z b st d) [i] [b] [] [] := by
  refine ⟨⟨fun j hj => ?_, fun _ _ => rfl, fun c _ hc => ⟨rfl, rfl⟩, fun c _ hc data hd => ⟨data, ?_, rfl,
    fun _ _ _ => rfl⟩, fun c _ hc hn => ?_, rfl, rfl, rfl, rfl, Nat.le_refl _⟩, fun c _ hc => ⟨?_, rfl⟩⟩
  · simp only [SH]; exact upd_ne _ _ _ _ (by simpa using hj)
  · simp only [SH]; rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hd
  · simp only [SH]; rw [upd_ne _ _ _ _ (by simpa using hc)]; exact hn
  · simp only [SH]; exact upd_ne _ _ _ _ (by simpa using hc)

/-- What `deflateReset` / `deflateResetKeep` leave: `Z_OK`, the invariant, and a change of the stream record and
the stream's block only. -/
def ResetPost (h : Heap) (i b : Nat) (r : Int32) (h' : Heap) (Q : Heap → Prop) : Prop :=
  r = Z_OK ∧ DInv h' (some i) ∧ DFrame h h' [i] [b] [] [] ∧ Q h'

/-- What `deflateResetKeep` leaves on the state record, from state `st`: no symbols, no flush yet, the first header
state, and the window positions, `level`, `strategy`, `sym_end` kept. -/
def KeepSt (st st' : DeflateState) : Prop :=
  st'.sym_next = 0 ∧ st'.last_flush = -2 ∧ (st'.status = GZIP_STATE ∨ st'.status = INIT_STATE) ∧
    (st'.status = GZIP_STATE → st'.wrap = 2) ∧ st'.strstart = st.strstart ∧ st'.block_start = st.block_start ∧
    st'.lookahead = st.lookahead ∧ st'.level = st.level ∧ st'.strategy = st.strategy ∧ st'.sym_end = st.sym_end ∧
    st'.bi_valid = 0 ∧ st'.head = st.head ∧ st'.prev = st.prev ∧ st'.w_size = st.w_size

theorem keep_trS (b : Nat) (st : DeflateState) (A B C : Array Ct) : KeepSt st (trS b (rkS st) A B C) := by
  by_cases hw : (st.wrap == 2) = true
  · have e : st.wrap = 2 := by simpa using hw
    simp [KeepSt, trS, rkS, e]
  · simp only [KeepSt, trS, rkS, hw, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, trivial, Or.inr trivial, fun e => absurd e (by decide), trivial, trivial, trivial, trivial,
      trivial, trivial, by first | trivial | rfl, by first | trivial | rfl, by first | trivial | rfl,
      by first | trivial | rfl⟩

/-- The post of `deflateResetKeep` on block `b`, from heap `h`. -/
def KeepPost (h : Heap) (i b : Nat) (h' : Heap) : Prop :=
  (∀ z', h'.streams i = some z' → z'.state = some b) ∧ h'.bytes b = h.bytes b ∧
    ∀ st, h.dstate b = some st → ∃ st', h'.dstate b = some st' ∧ KeepSt st st'

/-- The layout facts of `RLay` from the invariant's clauses. -/
theorem rlay_of {h : Heap} {s : StreamPtr} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    {d : Array UInt8} (c : DCore h s z b (dview st) al) (hd : h.bytes b = some d) : RLay b st d.size := by
  obtain ⟨w1, w2, wsz, l1, l2, pbs, se⟩ := c.sizes
  obtain ⟨d0, wo, po, ho, pbo, hd0, hw, hp, hh, hpb, h1, h2, h3, h4, hs, -⟩ := c.lay
  obtain rfl : d0 = d := Option.some.inj (hd0.symm.trans hd)
  refine ⟨⟨w1, w2⟩, ⟨l1, l2⟩, pbs, se, ⟨wo, po, ho, pbo, hw, hp, hh, hpb, ?_, h2, h3, h4, hs⟩, c.strategy⟩
  have : st.window_size = W_BUF_SIZE st.w_size := wsz
  rw [← this]; exact h1

theorem reset_inv_nn {h : Heap} {s : StreamPtr} (hv : DInv h s)
    (hw : ∀ b st, StateBlock h s b → h.dstate b = some st → st.wrap = 0 ∨ st.wrap = 1 ∨ st.wrap = 2) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateReset s) (fun r h' => ResetPost h i b r h' (DFreshOf · (some i))) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, hh, hho⟩ := c.head
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  rw [← SH_self L.hz L.hst hd]
  refine Sat.mono (reset_SH ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩ (hw b st ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩ L.dstate) hpb c.trees.1 c.trees.2.1 c.trees.2.2
    hh hho c.level.1 c.level.2 (rlay_of c hd)) ?_
  rintro r h' ⟨rfl, A, B, C, cf, lm, ib, hib, d', rfl, hd', hA, hB, hC, hF, RL, hz⟩
  obtain ⟨q1, q2, q0, q3, q4, q5, q6, q7⟩ := RL.post _ d' (SH_bytes _ _ _ _ _ _) hd' A B C cf lm ib hib
  refine ⟨rfl, ⟨i, rkZ z st.wrap, b, lmS (trS b (rkS st) A B C) cf (.val lm) (.val ib), al, rfl, by simp [SH], L.hb,
    by simp [Heap.dstate, SH], ?_, ?_⟩, ?_, i, rkZ z st.wrap, b, lmS (trS b (rkS st) A B C) cf (.val lm) (.val ib), rfl, by simp [SH], L.hb,
    by simp [Heap.dstate, SH], fresh_lmS _ _ _ _ _ _ _ _, ho, d', SH_bytes _ _ _ _ _ _,
    by simp only [lmS, trS, rkS]; exact hh, hz⟩
  · simp [Heap.dallocsOf, SH, hda]
  · exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := st_lo _
      status_hi := st_hi _
      wrap := c.wrap
      gzhead := ⟨_, rfl⟩
      w_size := c.w_size
      pbuf := ⟨pb, hpb⟩
      head := ⟨ho, d', (by simp [SH]), hh, (by omega)⟩
      level := c.level
      trees := ⟨hA, hB, hC⟩
      sizes := q1
      lay := q2
      pout := q0
      syms := q3
      bits := q4
      look := q5
      strategy := q6
      fns := q7
      symv := by
        obtain ⟨d0, _, _, _, pbo0, hd0, -, -, -, -, -, -, -, -, hs, -⟩ := q2
        exact ⟨d0, _, hd0, hs, by simp only [dview, lmS, trS, rkS]; exact SymOk.empty hF.1 hF.2.1⟩
      psym := fun hn => absurd (by simp [dview, lmS, trS, rkS]) hn
      hdr := fun _ _ => by simp [dview, lmS, trS, rkS]
      bstart := by simp [dview, lmS, trS, rkS]
      ins := by simp [dview, lmS, trS, rkS]
      wpow := c.wpow
      lmod := c.lmod
      lpow := c.lpow
      scratch := c.scratch
      blk := by simp only [dview, lmS, trS, rkS]; exact ⟨by simp, by simp, hF.2.2⟩
      fe_mod := by
        have := lm_fill_end _ q1.1 q1.2.1
        simpa [dview, lmS, trS, rkS] using this.1
      fe_hi := by
        have := lm_fill_end _ q1.1 q1.2.1
        simpa [dview, lmS, trS, rkS] using this.2
      bs_lo := by simp [dview, lmS, trS, rkS]
      descs := by simp [dview, lmS, trS, rkS] }
  · rw [SH_self L.hz L.hst hd]
    exact dframe_SH _ _ _ _ _ _

theorem resetKeep_inv_nn {h : Heap} {s : StreamPtr} (hv : DInv h s)
    (hw : ∀ b st, StateBlock h s b → h.dstate b = some st → st.wrap = 0 ∨ st.wrap = 1 ∨ st.wrap = 2) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateResetKeep s) (fun r h' => ResetPost h i b r h' (KeepPost h i b)) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, hh, hho⟩ := c.head
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  refine ⟨i, z, b, rfl, L.hz, L.hb, ?_⟩
  rw [← SH_self L.hz L.hst hd]
  refine Sat.mono (resetKeep_SH ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩ (hw b st ⟨z, ⟨i, rfl, L.hz⟩, L.hb⟩ L.dstate) hpb c.trees.1 c.trees.2.1
    c.trees.2.2) ?_
  rintro r h' ⟨rfl, A, B, C, rfl, hA, hB, hC, hF⟩
  refine ⟨rfl, ⟨i, rkZ z st.wrap, b, trS b (rkS st) A B C, al, rfl, by simp [SH], L.hb,
    by simp [Heap.dstate, SH], ?_, ?_⟩, ?_, fun z' hz' => by
      simp only [SH, upd_same] at hz'; rw [← Option.some.inj hz']; exact L.hb, by simp only [SH_bytes],
    fun st0 e0 => ⟨trS b (rkS st) A B C, by simp [Heap.dstate, SH], ?_⟩⟩
  · simp [Heap.dallocsOf, SH, hda]
  · exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := c.strm
      alloc_bufs := c.alloc_bufs
      al_state := c.al_state
      al_zfree := c.al_zfree
      al_buf := c.al_buf
      status_lo := st_lo _
      status_hi := st_hi _
      wrap := c.wrap
      gzhead := ⟨_, rfl⟩
      w_size := c.w_size
      pbuf := ⟨pb, hpb⟩
      head := ⟨ho, d, (by simp [SH]), hh, hho⟩
      level := c.level
      trees := ⟨hA, hB, hC⟩
      sizes := c.sizes
      lay := by
        obtain ⟨d0, wo, po, ho', pbo, hd0, hw, hp, hh', hpb', h1, h2, h3, h4, hs, -⟩ := c.lay
        obtain rfl : d0 = d := Option.some.inj (hd0.symm.trans hd)
        exact ⟨d0, wo, po, ho', pbo, by simp [SH], hw, hp, hh', hpb', h1, h2, h3, h4, hs, pbo,
          by simpa [dview, trS, rkS] using hpb', Nat.le_refl _, by simp [dview, trS, rkS]⟩
      pout := fun _ => by simp [dview, trS, rkS]
      syms := ⟨by simp [dview, trS, rkS], by simp [dview, trS, rkS]⟩
      bits := ⟨by simp [dview, trS, rkS], by simp [dview, trS, rkS]⟩
      look := c.look
      strategy := c.strategy
      fns := c.fns
      symv := by
        obtain ⟨d0, _, _, _, pbo0, hd0, -, -, -, -, -, -, -, -, hs, -⟩ := c.lay
        obtain rfl : d0 = d := Option.some.inj (hd0.symm.trans hd)
        exact ⟨d0, _, by simp [SH], hs, by simp only [dview, trS, rkS]; exact SymOk.empty hF.1 hF.2.1⟩
      psym := fun hn => absurd (by simp [dview, trS, rkS]) hn
      hdr := fun _ _ => by simp [dview, trS, rkS]
      bstart := c.bstart
      ins := c.ins
      wpow := c.wpow
      lmod := c.lmod
      lpow := c.lpow
      scratch := c.scratch
      blk := by simp only [dview, trS, rkS]; exact ⟨by simp, by simp, hF.2.2⟩
      fe_mod := c.fe_mod
      fe_hi := c.fe_hi
      bs_lo := c.bs_lo
      descs := by simp [dview, trS, rkS] }
  · rw [SH_self L.hz L.hst hd]
    exact dframe_SH _ _ _ _ _ _
  · rw [SH_self L.hz L.hst hd] at e0
    obtain rfl := Option.some.inj (e0.symm.trans L.dstate)
    exact keep_trS _ _ _ _ _

/-! ## A negative `wrap` (after `deflate` wrote the trailer) -/

theorem resetKeep_neg {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (k : DOk i z b st) {pb : BPtr} (hpb : st.pending_buf = .val pb) (w : Int32)
    (hw : (st.wrap = -1 ∧ w = 1) ∨ (st.wrap = -2 ∧ w = 2)) :
    deflateResetKeep (some i) (SH H i z b st d) =
      deflateResetKeep (some i) (SH H i z b { st with wrap := w } d) := by
  have k' : DOk i z b { st with wrap := w } := ⟨k.za, k.zf, k.hb, k.ab, k.sm, k.lo, k.hi⟩
  have hneg : st.wrap < 0 := by rcases hw with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hpos : ¬ w < 0 := by rcases hw with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> decide
  have hchk : chkI32 (-st.wrap.toInt) = pure w := by
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> exact DeflateAlloc.chk_eq _ (by decide)
  unfold deflateResetKeep
  simp only [bind_app, check_SH k, check_SH k', Bool.false_eq_true, ↓reduceIte, wrZ_SH, rdZ_SH, k.hb, wrD_SH,
    ldDState_SH, Ival.get, dstateOf]
  simp only [hpb, bind_app, ↓reduceIte, wrD_SH, ldDState_SH, pure_app, hneg, hpos, hchk, rdD_SH]

theorem dframe_trans {h1 h2 h3 : Heap} {S B G : List Nat} {W : List (BPtr × Nat)} (f : DFrame h1 h2 S B G W)
    (g : DFrame h2 h3 S B G W) : DFrame h1 h3 S B G W := by
  obtain ⟨⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩, e1⟩ := f
  obtain ⟨⟨s2, g2, i2, b2, n2, c2, r2, x2, a2, k2⟩, e2⟩ := g
  refine ⟨⟨fun j hj => (s2 j hj).trans (s1 j hj), fun j hj => (g2 j hj).trans (g1 j hj),
    fun c hc hn => ⟨((i2 c (by omega) hn).1).trans (i1 c hc hn).1, ((i2 c (by omega) hn).2).trans (i1 c hc hn).2⟩,
    fun c hc hn data hd => ?_, fun c hc hn hd => n2 c (by omega) hn (n1 c hc hn hd), c2.trans c1, r2.trans r1,
    x2.trans x1, a2.trans a1, Nat.le_trans k1 k2⟩, fun c hc hn =>
      ⟨((e2 c (by omega) hn).1).trans (e1 c hc hn).1, ((e2 c (by omega) hn).2).trans (e1 c hc hn).2⟩⟩
  obtain ⟨d2, f2, s2', q2⟩ := b1 c hc hn data hd
  obtain ⟨d3, f3, s3, q3⟩ := b2 c (by omega) hn d2 f2
  exact ⟨d3, f3, s3.trans s2', fun j hj hw => (q3 j (by omega) hw).trans (q2 j hj hw)⟩

/-- An invariant stream whose `wrap` is negative is, for `deflateResetKeep`, the same as the stream with `wrap`
negated in its state (`deflateResetKeep` negates it first). -/
theorem neg_view {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (L : DLive h i z b st) (hal : h.dallocsOf b = some al) (c : DCore h (some i) z b (dview st) al)
    (hn : st.wrap = -1 ∨ st.wrap = -2) :
    ∃ h0, DInv h0 (some i) ∧ DFrame h h0 [i] [b] [] [] ∧ deflateResetKeep (some i) h = deflateResetKeep (some i) h0 ∧
      h0.streams i = some z ∧ (∃ w, h0.dstate b = some { st with wrap := w }) ∧
      (∀ b' st', StateBlock h0 (some i) b' → h0.dstate b' = some st' → st'.wrap = 0 ∨ st'.wrap = 1 ∨ st'.wrap = 2) ∧
      h0.bytes b = h.bytes b := by
  obtain ⟨pb, hpb⟩ := c.pbuf
  obtain ⟨ho, d, hd, -, -⟩ := c.head
  obtain ⟨w, hw⟩ : ∃ w : Int32, (st.wrap = -1 ∧ w = 1) ∨ (st.wrap = -2 ∧ w = 2) := by
    rcases hn with e | e
    · exact ⟨1, Or.inl ⟨e, rfl⟩⟩
    · exact ⟨2, Or.inr ⟨e, rfl⟩⟩
  have hw3 : w = 1 ∨ w = 2 := by rcases hw with ⟨-, e⟩ | ⟨-, e⟩ <;> simp [e]
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  have hwc : (dview { st with wrap := w }).wrap = 0 ∨ (dview { st with wrap := w }).wrap = 1 ∨
      (dview { st with wrap := w }).wrap = 2 ∨ (dview { st with wrap := w }).wrap = -1 ∨
      (dview { st with wrap := w }).wrap = -2 := by
    rcases hw3 with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  have c' : DCore (SH h i z b { st with wrap := w } d) (some i) z b (dview { st with wrap := w }) al :=
    DCore.of_heap (h := h) (by simp [SH, hd]) { c with wrap := hwc }
  refine ⟨SH h i z b { st with wrap := w } d, ⟨i, z, b, _, al, rfl, by simp [SH], L.hb, by simp [Heap.dstate, SH],
    by simp [Heap.dallocsOf, SH, hda], c'⟩, dframe_SH _ _ _ _ _ _, ?_, by simp [SH], ⟨w, by simp [Heap.dstate, SH]⟩, ?_, by simp [SH, hd]⟩
  · rw [← SH_self L.hz L.hst hd]
    rw [show SH (SH h i z b st d) i z b { st with wrap := w } d = SH h i z b { st with wrap := w } d by
      simp [SH, upd_upd]]
    exact resetKeep_neg ⟨L.za, L.zf, L.hb, L.ab, L.sm, L.lo, L.hi⟩ hpb w hw
  · rintro b' st' ⟨z', ⟨i', e1, e2⟩, e3⟩ e4
    obtain rfl := Option.some.inj e1
    simp only [SH] at e2; rw [upd_same] at e2
    obtain rfl := Option.some.inj e2
    rw [L.hb] at e3; obtain rfl := Option.some.inj e3
    simp only [Heap.dstate, SH, upd_same] at e4
    obtain rfl := Option.some.inj e4
    rcases hw3 with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

theorem resetKeep_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateResetKeep s) (fun r h' => ResetPost h i b r h' (KeepPost h i b)) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  by_cases hn : st.wrap = -1 ∨ st.wrap = -2
  · obtain ⟨h0, hv0, f0, e0, hz0, ⟨w, hw⟩, hw0, hb0⟩ := neg_view L hal c hn
    obtain ⟨i', z', b', e1, hz', hb', r, h', e, hr, hi, hf, hk⟩ := resetKeep_inv_nn hv0 hw0
    obtain rfl : i' = i := (Option.some.inj e1).symm
    obtain rfl : z' = z := Option.some.inj (hz'.symm.trans hz0)
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans L.hb)
    refine ⟨_, _, _, rfl, L.hz, L.hb, r, h', by rw [e0]; exact e, hr, hi, dframe_trans f0 hf, hk.1, hk.2.1.trans hb0, fun st0 hs0 => ?_⟩
    obtain rfl := Option.some.inj (hs0.symm.trans L.dstate)
    obtain ⟨st', h1, h2⟩ := hk.2.2 _ hw
    exact ⟨st', h1, h2⟩
  · refine resetKeep_inv_nn hv fun b' st' hb' hs' => ?_
    obtain ⟨z', ⟨i', e1, e2⟩, e3⟩ := hb'
    obtain rfl := Option.some.inj e1
    obtain rfl := Option.some.inj (e2.symm.trans L.hz)
    obtain rfl : b' = b := Option.some.inj (e3.symm.trans L.hb)
    obtain rfl := Option.some.inj (hs'.symm.trans L.dstate)
    rcases c.wrap with e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · exact absurd (Or.inl e) hn
    · exact absurd (Or.inr e) hn

theorem reset_inv {h : Heap} {s : StreamPtr} (hv : DInv h s) :
    ∃ i z b, s = some i ∧ h.streams i = some z ∧ z.state = some b ∧
      Sat h (deflateReset s) (fun r h' => ResetPost h i b r h' (DFreshOf · (some i))) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  by_cases hn : st.wrap = -1 ∨ st.wrap = -2
  · obtain ⟨h0, hv0, f0, e0, hz0, -, hw0, -⟩ := neg_view L hal c hn
    have e0' : deflateReset (some i) h = deflateReset (some i) h0 := by
      unfold deflateReset; rw [bind_app, bind_app, e0]
    obtain ⟨i', z', b', e1, hz', hb', r, h', e, hr, hi, hf, hq⟩ := reset_inv_nn hv0 hw0
    obtain rfl : i' = i := (Option.some.inj e1).symm
    obtain rfl : z' = z := Option.some.inj (hz'.symm.trans hz0)
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans L.hb)
    exact ⟨_, _, _, rfl, L.hz, L.hb, r, h', by rw [e0']; exact e, hr, hi, dframe_trans f0 hf, hq⟩
  · refine reset_inv_nn hv fun b' st' hb' hs' => ?_
    obtain ⟨z', ⟨i', e1, e2⟩, e3⟩ := hb'
    obtain rfl := Option.some.inj e1
    obtain rfl := Option.some.inj (e2.symm.trans L.hz)
    obtain rfl : b' = b := Option.some.inj (e3.symm.trans L.hb)
    obtain rfl := Option.some.inj (hs'.symm.trans L.dstate)
    rcases c.wrap with e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · exact absurd (Or.inl e) hn
    · exact absurd (Or.inr e) hn

theorem resetKeep_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    deflateResetKeep s h = .ok (Z_STREAM_ERROR, h) := by
  simp only [deflateResetKeep, bind_app, stateCheck_noState hn, ↓reduceIte]; rfl

theorem reset_noState {h : Heap} {s : StreamPtr} (hn : DNoState h s) :
    deflateReset s h = .ok (Z_STREAM_ERROR, h) := by
  simp only [deflateReset, bind_app, resetKeep_noState hn]; rfl

end ZlibNgF.Proof.DeflateReset
