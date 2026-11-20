import ZlibNgF.Proof.«deflate_p.h.tally»
import ZlibNgF.Proof.«deflate_p.h.flush»

/-!
# `FLUSH_BLOCK_ONLY` / `FLUSH_BLOCK` (`ZlibNgF`)

`flush_block_only_ok`: from an invariant stream with valid and set buffers, no pending bytes, a level above 0 and the
window at offset `wo` of the block, `FLUSH_BLOCK_ONLY(s, window, last)` (the block `[block_start, strstart)` through
`zng_tr_flush_block` (`TreesFacts.flush_block`), then `block_start = strstart` and `flush_pending`) does not fault and
leaves `FBPost`: the invariant, valid and set buffers, a change of the stream record, the stream's block and the
first `L` output bytes only, `L` bytes written to `next_out`, no symbols (`sym_next == 0`), `block_start == strstart`,
and no pending bytes when output room is left. The `int` length `strstart - block_start` is in range by the
invariant's `bstart` / `bs_lo`; the block's bytes lie in the window below `strstart`.

`zng_tr_flush_block` is used through `TreesFacts.flush_block` and `FlushExtra`: its result has no symbols
(`init_block`), and the heap after it differs from the heap before only in the stream record and the stream's block
(an `SH` heap). Both are facts of the translated `trees.c` that `TreesFacts` does not state yet.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FlushBlock
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.InflateInv (ldStream_app)
open ZlibNg.DeflateP

/-! ## Frames -/

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

/-- A frame with fewer protected bytes: every byte outside `W'` is outside `W`. -/
theorem dframe_wmono {h h' : Heap} {S B G : List Nat} {W W' : List (BPtr × Nat)} (f : DFrame h h' S B G W)
    (hW : ∀ c j, (∀ w ∈ W', ∀ off, w.1 = .ref (.heap c) off → j < off ∨ off + w.2 ≤ j) →
      ∀ w ∈ W, ∀ off, w.1 = .ref (.heap c) off → j < off ∨ off + w.2 ≤ j) : DFrame h h' S B G W' := by
  obtain ⟨⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩, e1⟩ := f
  refine ⟨⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩, e1⟩
  obtain ⟨d2, f2, s2, q2⟩ := b1 c hc hn data hd
  exact ⟨d2, f2, s2, fun j hj hw => q2 j hj (hW c j hw)⟩

theorem dframe_nil {h h' : Heap} {S B G : List Nat} (W : List (BPtr × Nat)) (f : DFrame h h' S B G []) :
    DFrame h h' S B G W :=
  dframe_wmono f fun _ _ _ _ hw => nomatch hw

theorem dframe_one {h h' : Heap} {S B G : List Nat} {p : BPtr} {n m : Nat} (f : DFrame h h' S B G [(p, n)])
    (hnm : n ≤ m) : DFrame h h' S B G [(p, m)] := by
  refine dframe_wmono f fun c j hw w hm off he => ?_
  rw [List.mem_singleton] at hm; subst hm
  have := hw _ (List.mem_singleton_self _) off he
  dsimp only at this ⊢; omega

/-! ## `zng_tr_flush_block` -/

/-- What `zng_tr_flush_block` leaves beyond `TreesFacts`, under its precondition: only the stream record
(`data_type`) and the stream's block changed (the heap after is `SH h i { z with data_type } b st' d'`).
`TreesFacts.flush_block`'s frame (`DFrame`) says this only for the blocks numbered below `nextBlk`, so it does not
carry a caller buffer of a block above `nextBlk` (`DStreamIO` after the call). -/
def FlushExtra : Prop :=
  ∀ (i b : Nat) (z : ZStream) (buf : BPtr) (len : UInt32) (last : Int32) (h h' : Heap) (st : DeflateState),
    DWork h (some i) → h.streams i = some z → z.state = some b → h.dstate b = some st →
    FlushBlockPre b buf len st →
    C.run (ZlibNg.Trees.zng_tr_flush_block (some b) buf len last) h = .ok ((), h') →
    ∃ dt st' d', h' = SH h i { z with data_type := dt } b st' d'

/-- The state after `FLUSH_BLOCK_ONLY` from `st`: the state `st1` after `zng_tr_flush_block` (`EmitKeeps`), with
`block_start = strstart` and the fields of `flush_pending`. -/
def FBKeeps (st st' : DeflateState) : Prop :=
  ∃ st1, EmitKeeps st st1 ∧ st' = { st1 with
    block_start := st.strstart.toInt32
    pending := st'.pending
    pending_out := st'.pending_out
    bi_buf := st'.bi_buf
    bi_valid := st'.bi_valid }

/-- What `FLUSH_BLOCK_ONLY` leaves (stream `i` with record `z`, block `b` with state `st` before). -/
structure FBPost (h h' : Heap) (i b : Nat) (z : ZStream) (st : DeflateState) : Prop where
  inv : DInv h' (some i)
  io : DStreamIO h' (some i)
  set : DBufsSet h' (some i)
  frame : DFrame h h' [i] [b] [] [(z.next_out, z.avail_out.toNat)]
  out : ∃ (z' : ZStream) (st' : DeflateState) (L : Nat), h'.streams i = some z' ∧ h'.dstate b = some st' ∧
    L ≤ z.avail_out.toNat ∧ z'.avail_out.toNat = z.avail_out.toNat - L ∧
    z' = { z with
      next_out := z'.next_out
      avail_out := z'.avail_out
      total_out := z'.total_out
      data_type := z'.data_type } ∧
    (∀ ob oo, z.next_out = .ref (.heap ob) oo → z'.next_out = .ref (.heap ob) (oo + L)) ∧
    (z'.avail_out ≠ 0 → st'.pending = 0) ∧ st'.sym_next = 0 ∧ FBKeeps st st'

/-- `FLUSH_BLOCK_ONLY(s, window, last)` from an invariant stream with no pending bytes at a level above 0; `window`
evaluates to the window (offset `wo` of the block) without changing the heap. -/
theorem flush_block_only_ok (T : TreesFacts) (X : FlushExtra) {h : Heap} {i : Nat} {z : ZStream} {b : Nat}
    {st : DeflateState} {wo : Nat} (window : M BPtr) (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (hv : DInv h (some i))
    (hio : DStreamIO h (some i)) (hset : DBufsSet h (some i)) (hz : h.streams i = some z)
    (hb : z.state = some b) (hst : h.dstate b = some st) (hp0 : st.pending = 0) (hlv : 0 < st.level)
    (hwin : st.window = .val (.ref (.heap b) wo)) (hwm : window h = .ok (.ref (.heap b) wo, h)) :
    ∃ h', C.run (FLUSH_BLOCK_ONLY (some b) window last) h = .ok ((), h') ∧ FBPost h h' i b z st := by
  have hw0 := DWork.of_inv hv
  obtain ⟨i', z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c⟩ := hv
  obtain rfl : i = i' := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd⟩ : ∃ d, h.bytes b = some d := by
    unfold Heap.dstate at hst; split at hst <;> simp_all
  have hsts : h.dstates b = some st := by simpa [Heap.dstate, hd] using hst
  obtain ⟨d1, wo1, po, ho, pbo, hd1, hw1, -, -, -, h1, h2, h3, h4, -⟩ := c.lay
  obtain rfl : d = d1 := Option.some.inj (hd.symm.trans hd1)
  simp only [dview] at hw1 h1 h2 h3 h4
  rw [hwin] at hw1
  obtain rfl : wo = wo1 := by injection hw1 with e; injection e
  have hlook := c.look
  have hbs := c.bstart
  have hbl := c.bs_lo
  have hsm := c.strm
  simp only [dview] at hlook hbs hbl hsm
  have hss := (strstart_toInt32 c).1
  have hss2 := (strstart_toInt32 c).2
  simp only [dview] at hss hss2
  have hv0 : -2147483648 ≤ st.strstart.toInt32.toInt - st.block_start.toInt := by omega
  have hv1 : st.strstart.toInt32.toInt - st.block_start.toInt < 2147483648 := by omega
  have e1 := ZlibNgF.Proof.DeflatePrime.ofInt_toInt _ hv0 hv1
  generalize hL32 : Int32.ofInt (st.strstart.toInt32.toInt - st.block_start.toInt) = len32 at e1
  have hlen : (len32.toUInt32.toNat : Int) = st.strstart.toNat - st.block_start.toInt := by
    rw [ZlibNgF.Proof.DeflatePrime.toUInt32_toNat _ (by omega), e1]; omega
  -- the output buffer
  have hio0 := hio
  obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
  obtain rfl : i = i2 := Option.some.inj e2
  obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
  obtain rfl : b = b2 := Option.some.inj (hb.symm.trans hb2)
  obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, hni⟩ := hset
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain ⟨ob, oo, ad, hno, had, hoo⟩ := hout.resolve_left hnn
  have hob : ob ≠ b := fun e => hnb oo (by rw [hno, e])
  have hS := ZlibNgF.Proof.DeflateReset.SH_self hz hsts hd
  suffices S : Sat (SH h i z b st d) (FLUSH_BLOCK_ONLY (some b) window last) (fun _ h' => FBPost h h' i b z st) by
    rw [hS] at S
    obtain ⟨_, h', e, q⟩ := S
    exact ⟨h', e, q⟩
  unfold FLUSH_BLOCK_ONLY
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only []
  split
  rename_i hge
  have hge' : 0 ≤ st.block_start.toInt := by
    have := Int32.le_iff_toInt_le.mp hge; simpa using this
  refine Sat.bind (Sat.of_eq (show window (SH h i z b st d) = .ok (.ref (.heap b) wo, SH h i z b st d) by
    rw [hS]; exact hwm) ?_)
  refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH (off := wo) st.block_start.toInt.toNat
    (by omega)) ?_)
  have hbuf : Ptr.ref (BRef.heap b) (wo + st.block_start.toInt.toNat) = .null ∨
      WindowBuf b st (Ptr.ref (BRef.heap b) (wo + st.block_start.toInt.toNat)) len32.toUInt32 :=
    Or.inr (Or.inr ⟨wo, _, hwin, rfl, by omega⟩)
  generalize Ptr.ref (BRef.heap b) (wo + st.block_start.toInt.toNat) = buf at hbuf ⊢
  rotate_left
  refine Sat.bind (Sat.pure ?_)
  generalize hbe : (Ptr.null : BPtr) = buf
  have hbuf : buf = .null ∨ WindowBuf b st buf len32.toUInt32 := Or.inl hbe.symm
  all_goals
    rw [ZlibNgF.Proof.DeflatePrime.chk_ok _ hv0 hv1, hL32]
    refine Sat.bind (Sat.pure ?_)
    rw [hS]
    have hpre : FlushBlockPre b buf len32.toUInt32 st := ⟨hp0, hlv, c.bits.2, hbuf⟩
    obtain ⟨h1', ef, W1, F1, K1, -, E1, -⟩ := T.flush_block (some i) b buf len32.toUInt32 last hl0 hl1 h st hw0
      ⟨i, z, rfl, hz, hb, hst⟩ hpre (pendRoom_of_core c) (fun hn => c.psym hn)
    have hclr := T.flush_block_clears (some i) b buf len32.toUInt32 last hl0 hl1 h h1' st hw0 ⟨i, z, rfl, hz, hb, hst⟩
      hpre ef
    obtain ⟨dt, st1, d1', rfl⟩ := X i b z buf len32.toUInt32 last h _ st hw0 hz hb hst hpre ef
    have hzero : st1.sym_next = 0 := hclr st1 ⟨i, _, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _⟩
    have hK1 := (E1 st1 ⟨i, _, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _⟩).1
    refine Sat.bind ⟨(), _, ef, ?_⟩
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    have hsm1 : st1.strm = .val (some i) := by rw [hK1]; exact hsm
    have hss1 : st1.strstart = st.strstart := by rw [hK1]
    have eg : ({ st1 with block_start := st1.strstart.toInt32 } : DeflateState).strm.get =
        (pure (some i) : M StreamPtr) := by
      show st1.strm.get = _; rw [hsm1]; rfl
    rw [eg]
    refine Sat.bind (Sat.pure ?_)
    -- the working state after `block_start = strstart`
    obtain ⟨i4, z4, b4, st4, al1, e4, hz4, hb4, hst4, hal1, v0, v64, c1, R1, R2⟩ := W1
    obtain rfl : i = i4 := Option.some.inj e4
    obtain rfl : z4 = { z with data_type := dt } := Option.some.inj (hz4.symm.trans (SH_streams _ _ _ _ _ _))
    obtain rfl : b = b4 := Option.some.inj (hb.symm.trans hb4)
    obtain rfl : st1 = st4 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst4)
    have hx := (strstart_toInt32 c1).1
    simp only [dview] at hx
    generalize hH2 : SH h i { z with data_type := dt } b
      { st1 with block_start := st1.strstart.toInt32 } d1' = H2
    have hw2 : DWork H2 (some i) := by
      rw [← hH2]
      refine ⟨i, { z with data_type := dt }, b, { st1 with block_start := st1.strstart.toInt32 }, al1, rfl,
        SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _, by simpa [Heap.dallocsOf, SH] using hal1, v0, v64,
        DCore.of_heap (by simp) (ZlibNgF.Proof.Tally.dcore_bs _ c1 hx), R1, R2⟩
    have hz2' : H2.streams i = some { z with data_type := dt } := by rw [← hH2]; exact SH_streams _ _ _ _ _ _
    have hst2' : H2.dstate b = some { st1 with block_start := st1.strstart.toInt32 } := by
      rw [← hH2]; exact SH_dstate _ _ _ _ _ _
    have hob2 : H2.bytes ob = h.bytes ob := by
      rw [← hH2]; simp only [SH]; rw [upd_ne _ _ _ _ hob]
    obtain ⟨h', ew, hv', P⟩ := flush_work hw2 hz2' hb hst2' ⟨ob, oo, ad, hno, by rw [hob2]; exact had, hoo⟩ hnb
    refine ⟨(), h', ew, ?_⟩
    obtain ⟨L, z', st', hz', hst', hLm, hpen, hst'e, hav, hz'e, hadv, F2, O2, -⟩ := P
    have hLo : L ≤ z.avail_out.toNat := by rw [hLm]; exact Nat.min_le_right _ _
    have O : OutOnly h h' b ob oo L := by
      obtain ⟨o1, o2, o3⟩ := O2 ob oo hno
      refine ⟨by rw [o1, ← hH2]; rfl, by rw [o2, ← hH2]; rfl, fun c' hc data hdc => o3 c' hc data ?_⟩
      rw [← hH2]; simp only [SH]; rw [upd_ne _ _ _ _ hc]; exact hdc
    have hzs : z'.state = z.state := by rw [hz'e]
    have hdtz : z'.data_type = dt := by rw [hz'e]
    have hgz : st'.gzhead = st.gzhead := by rw [hst'e]; show st1.gzhead = st.gzhead; rw [hK1]
    refine ⟨hv', streamIO_out hio hz hb hst hno hLo O hz' hzs (by rw [hz'e]) (by rw [hz'e]) (hadv ob oo hno) hav hst'
      hgz, ⟨z', ⟨i, rfl, hz'⟩, by rw [hadv ob oo hno]; simp, fun ha => ?_⟩, ?_, ⟨z', st', L, hz', hst', hLo, hav,
      ?_, hadv, fun ha => ?_, ?_, st1, hK1, ?_⟩⟩
    · have : z'.next_in = z.next_in := by rw [hz'e]
      rw [this]; exact hni (by rw [hz'e] at ha; exact ha)
    · -- the frame
      refine dframe_trans ?_ (dframe_one F2 hLo)
      rw [← hH2]; exact dframe_nil _ (ZlibNgF.Proof.DeflateReset.dframe_SH _ _ _ _ _ _)
    · conv => lhs; rw [hz'e]
      rw [hdtz]
    · have h0 : z'.avail_out.toNat ≠ 0 := fun e => ha (UInt32.toNat_inj.mp (by rw [e]; rfl))
      have h0' := h0
      rw [hav] at h0'
      have hp' : st'.pending.toNat = 0 := by rw [hpen]; omega
      exact UInt32.toNat_inj.mp (by rw [hp']; rfl)
    · rw [hst'e]; exact hzero
    · conv => lhs; rw [hst'e]
      rw [hss1]

/-- `FLUSH_BLOCK(s, window, last)`: `FLUSH_BLOCK_ONLY`, then the early return when no output room is left. -/
theorem flush_block_ok (T : TreesFacts) (X : FlushExtra) {h : Heap} {i : Nat} {z : ZStream} {b : Nat}
    {st : DeflateState} {wo : Nat} (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1) (hv : DInv h (some i))
    (hio : DStreamIO h (some i)) (hset : DBufsSet h (some i)) (hz : h.streams i = some z)
    (hb : z.state = some b) (hst : h.dstate b = some st) (hp0 : st.pending = 0) (hlv : 0 < st.level)
    (hwin : st.window = .val (.ref (.heap b) wo)) :
    ∃ r h', C.run (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) h = .ok (r, h') ∧ FBPost h h' i b z st ∧
      ∃ z' st', h'.streams i = some z' ∧ h'.dstate b = some st' ∧
        (r = none ∧ st'.pending = 0 ∨ z'.avail_out = 0 ∧ r = some (if last != 0 then .finish_started else .need_more)) := by
  obtain ⟨h', e, P⟩ := flush_block_only_ok T X (pure (.ref (.heap b) wo)) last hl0 hl1 hv hio hset hz hb hst hp0 hlv hwin rfl
  obtain ⟨z', st', L, hz', hst', -, -, hze, -, hpz, -⟩ := P.out
  obtain ⟨i2, z2, b2, st2, al2, e2, L2, -, c2⟩ := live P.inv
  obtain rfl : i = i2 := Option.some.inj e2
  have ez : z2 = z' := Option.some.inj (L2.hz.symm.trans hz')
  have hb' : z'.state = some b := by rw [hze]; exact hb
  have eb : b = b2 := Option.some.inj ((by rw [ez]; exact hb' : z2.state = some b).symm.trans L2.hb)
  subst eb
  have es : st2 = st' := Option.some.inj (L2.dstate.symm.trans hst')
  have hsm' : st'.strm = .val (some i) := by rw [← es]; exact c2.strm
  suffices S : Sat h (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r h'' => h'' = h' ∧
      (r = none ∧ st'.pending = 0 ∨ z'.avail_out = 0 ∧
        r = some (if last != 0 then .finish_started else .need_more))) by
    obtain ⟨r, h'', e', rfl, q⟩ := S
    exact ⟨r, h'', e', P, z', st', hz', hst', q⟩
  unfold FLUSH_BLOCK
  refine Sat.bind ⟨(), h', e, ?_⟩
  simp only []
  refine Sat.bind (Sat.of_eq (ldDState_app hst') ?_)
  rw [hsm']
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.bind (Sat.of_eq (ldStream_app hz') (Sat.pure ?_)))
  by_cases ha : z'.avail_out = 0
  · have : (z'.avail_out == 0) = true := by simp [ha]
    simp only [this, ↓reduceIte]
    exact Sat.pure ⟨rfl, Or.inr ⟨ha, rfl⟩⟩
  · have : (z'.avail_out == 0) = false := by simpa using ha
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨rfl, Or.inl ⟨rfl, hpz ha⟩⟩

end ZlibNgF.Proof.FlushBlock
