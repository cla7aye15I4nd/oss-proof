import ZlibNgF.Proof.«gzwrite.c.flat»

/-!
# `deflate` on a write handle whose input is in `in` or in a caller range (`ZlibNgF`)

`deflate_stepX`: `deflate` on the stream of a write handle in the state `GzWX` (the invariant of the flat heap, the
input described by `InX`): no fault, the buffer fields move (`BufAdv`), the potential and progress facts of
`DeflateGz`, and `GzWX` again, with a step of the file between the flat heaps.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

theorem dframe_setZ {H H' : Heap} {i : Nat} {L G : List Nat} {wr : List (BPtr × Nat)} (f : DFrame H H' [i] L G wr)
    (a a' : ZStream) : DFrame (setZ H i a) (setZ H' i a') [i] L G wr := by
  obtain ⟨⟨fS, fG, fI, fB, fN, fC, fcrc, fx2n, fbase, fnext⟩, fD⟩ := f
  refine ⟨⟨fun j hj => ?_, fG, fI, fB, fN, fC, fcrc, fx2n, fbase, fnext⟩, fD⟩
  have hne : j ≠ i := by simpa using hj
  rw [setZ_streams_ne _ _ hne, setZ_streams_ne _ _ hne]; exact fS j hj

theorem dkeep_setZ {H H' : Heap} {i : Nat} {z z' a a' : ZStream} (hz : H.streams i = some z)
    (hz' : H'.streams i = some z') (ha : a.state = z.state) (ha' : a'.state = z'.state) (hk : DKeep H H' (some i)) :
    DKeep (setZ H i a) (setZ H' i a') (some i) := by
  obtain ⟨k1, k2, k3⟩ := hk
  refine ⟨fun c hc hst => k1 c hc fun z0 ⟨j, e, hz0⟩ e2 => ?_, k2, fun hp hr => ?_⟩
  · cases e; rw [hz] at hz0; cases hz0
    exact hst a ⟨i, rfl, setZ_streams_same _ _ _⟩ (ha.trans e2)
  · obtain ⟨sb, st, ⟨⟨z0, ⟨j, e, hz0⟩, hsb⟩, hst⟩, hg⟩ := hr
    cases e; rw [setZ_streams_same] at hz0; cases hz0
    rcases k3 hp ⟨sb, st, ⟨⟨z', ⟨i, rfl, hz'⟩, ha' ▸ hsb⟩, hst⟩, hg⟩ with e3 | e3
    · exact Or.inl e3
    · obtain ⟨sb2, st2, ⟨⟨z2, ⟨j2, e2, hz2⟩, hsb2⟩, hst2⟩, hg2⟩ := e3
      cases e2; rw [hz] at hz2; cases hz2
      exact Or.inr ⟨sb2, st2, ⟨⟨a, ⟨i, rfl, setZ_streams_same _ _ _⟩, ha.trans hsb2⟩, hst2⟩, hg2⟩

/-- `a` is `z` with other buffer fields. -/
def SameBut (z a : ZStream) : Prop :=
  a = { z with next_in := a.next_in, avail_in := a.avail_in, next_out := a.next_out, avail_out := a.avail_out }

/-- The caller's change of the buffer fields of stream `i`. -/
theorem dcaller_setZ {H : Heap} {i : Nat} {z a : ZStream} (hz : H.streams i = some z)
    (he : SameBut z a)
    {sb : Nat} {st : DeflateState} (hsb : z.state = some sb) (hst : H.dstate sb = some st)
    (hhd : ∀ k, st.gzhead ≠ .val (some k)) : DCallerStep H (setZ H i a) (some i) :=
  ⟨i, z, a, sb, st, rfl, hz, setZ_streams_same _ _ _, hsb, hst, he, rfl, rfl, rfl,
    fun k _ hk _ => absurd hk (hhd k), rfl, Nat.le_refl _⟩

/-- The deflate invariant and `DSide` carry over between heaps that differ in the buffer fields of stream `i`. -/
theorem dinv_setZ {H : Heap} {i : Nat} {z a : ZStream} (hz : H.streams i = some z)
    (he : SameBut z a)
    (hdi : DeflateInv.DInv H (some i)) (hds : DeflateSide.DSide H (some i))
    (hnh : ∀ sb st k, z.state = some sb → H.dstate sb = some st → st.gzhead ≠ .val (some k)) :
    DeflateInv.DInv (setZ H i a) (some i) ∧ DeflateSide.DSide (setZ H i a) (some i) := by
  have hdi0 := hdi
  obtain ⟨j, z0, sb, st, al, e0, hz0, hsb, hst, -, -⟩ := hdi0
  cases e0; rw [hz] at hz0; cases hz0
  have hc := dcaller_setZ hz he hsb hst (fun k => hnh sb st k hsb hst)
  exact ⟨DeflateReach.caller_inv hdi hc, DeflateSide.caller_side hds hc⟩

theorem flat_eq (z : ZStream) : SameBut (flatZ z) z := rfl

theorem flat_eq' (z : ZStream) : SameBut z (flatZ z) := rfl


/-- **The buffer fields of a write handle with buffers, and `x.next`, change** to ones that `GzWBuf` allows: the
invariant holds of the new heap and state, and it is a step of the file. -/
theorem invWS_gen {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b))
    (hs : w.gz h b = some s) (hsz : s.size ≠ 0) {z : ZStream} (hz : h.streams s.strm = some z) (z' : ZStream)
    (he : SameBut z z') (nx : Ival BPtr)
    (hinp : ∀ c base, GzBufs h s c base → InpOk s c base z'.next_in z'.avail_in)
    (hout : s.direct = 0 → ∀ c base, GzBufs h s c base → ∃ ko kx,
      z'.next_out = .ref (.heap c) (base + inSize s + ko) ∧ nx = .val (.ref (.heap c) (base + inSize s + kx)) ∧
      kx ≤ ko ∧ ko + z'.avail_out.toNat = s.size.toNat) :
    GzInvWS { w with gzs := upd w.gzs b (some { s with next := nx }) } (setZ h s.strm z') (some b) ∧
      ({ w with gzs := upd w.gzs b (some { s with next := nx }) } : World).gz (setZ h s.strm z') b =
        some { s with next := nx } ∧
      GStep w h { w with gzs := upd w.gzs b (some { s with next := nx }) } (setZ h s.strm z') b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hwf := hv.2.2
  obtain ⟨c, base, z1, hB, hz1, WB⟩ := (sh.write hwm).bufs hsz
  rw [hz] at hz1; cases hz1
  have hz' : (setZ h s.strm z').streams s.strm = some z' := setZ_streams_same _ _ _
  have hsW := gz_upd_same (h := setZ h s.strm z') hs { s with next := nx }
  have hB' : GzBufs (setZ h s.strm z') { s with next := nx } c base :=
    ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩
  have hst : z'.state = z.state := by rw [he]
  have hWB' : GzWBuf (setZ h s.strm z') { s with next := nx } c base z' := by
    refine ⟨fun hdir => ?_, fun sb st k e1 e2 => WB.nohdr sb st k (hst ▸ e1) e2, hinp c base hB,
      fun e => hst ▸ WB.nostate e, fun e => hout e c base hB⟩
    obtain ⟨hd, hsd⟩ := WB.deflate hdir
    exact dinv_setZ hz he hd hsd WB.nohdr
  have hstB : stBlk (setZ h s.strm z') { s with next := nx } = stBlk h s := by simp [stBlk, hz, hst]
  have hown' : ownL (setZ h s.strm z') b { s with next := nx } = ownL h b s := by simp only [ownL, hstB]
  have shape : GzShape (setZ h s.strm z') { s with next := nx } := by
    refine ⟨sh.mode, sh.path, ⟨_, hz'⟩, sh.want_lo, sh.want_hi, sh.size,
      (by obtain ⟨⟩ := sh.pos; constructor <;> assumption), ⟨sh.msg.1, sh.msg.2⟩,
      fun hr => absurd (hwm.symm.trans hr) write_ne_read,
      fun _ => ⟨fun _ => ⟨c, base, z', hB', hz', hWB'⟩, fun e => absurd e hsz, (sh.write hwm).have0⟩,
      fun e => absurd e hsz⟩
  have wf : GzWFw { w with gzs := upd w.gzs b (some { s with next := nx }) } (setZ h s.strm z') := by
    have w1 := wfw_store hwf hs { s with next := nx } rfl
    refine ⟨w1.1, w1.2.1, w1.2.2.1, fun x s2 hx => ?_, w1.lit⟩
    obtain ⟨z5, hz5⟩ := w1.2.2.2.1 x s2 hx
    by_cases e5 : s2.strm = s.strm
    · rw [e5]; exact ⟨_, hz'⟩
    · exact ⟨z5, by rw [setZ_streams_ne _ _ e5]; exact hz5⟩
  refine ⟨⟨⟨b, _, rfl, hsW, shape, by rw [hown']; exact hn⟩, ⟨b, _, rfl, hsW, hwm⟩, wf⟩, hsW, ?_⟩
  refine gstep_mk' hs hsW rfl (fun c hc _ => by simp [upd_ne _ _ _ _ hc]) (fun i hi => setZ_streams_ne _ _ hi)
    (fun _ => rfl) (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) (fun _ _ e => e) rfl rfl rfl (Nat.le_refl _)
    (fun x hx _ => ?_)
  simp only [GzOwned, hsW, hs, hz', hz, hst] at hx ⊢; exact hx

/-- **`deflate`** on the stream of a write handle in the state `GzWX` (not direct). -/
theorem deflate_stepX (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {G : Nat}
    (hD : DeflateClause ψ G) {W : World} {H : Heap} {b : Nat} {s : GzState} {z : ZStream} (hx : GzWX W H b s z)
    (hd : s.direct = 0) (flush : Int32) :
    ∃ r H' z', ZlibNg.Deflate.deflate (some s.strm) flush H = .ok (r, H') ∧ H'.streams s.strm = some z' ∧
      BufAdv z z' ∧
      (∀ sb st st', DStateOf H (some s.strm) sb st → DStateOf H' (some s.strm) sb st' →
        ψ flush st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
          ψ flush st + G * (z.avail_in.toNat - z'.avail_in.toNat) + (if z'.avail_out = 0 then 5 else 0)) ∧
      (flush ≠ ZlibNg.Inflate.Z_FINISH → r ≠ ZlibNg.Inflate.Z_STREAM_ERROR → z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      GzWX W H' b s z' ∧ GStep W (setZ H s.strm (flatZ z)) W (setZ H' s.strm (flatZ z')) b [] := by
  obtain ⟨hs, hz, hsz, hv, hin⟩ := hx
  have hsF : W.gz (setZ H s.strm (flatZ z)) b = some s := hs
  have hwm := modeOf hsF hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hsF hv.1
  obtain ⟨c, base, zF, hB, hzF, WB⟩ := (sh.write hwm).bufs hsz
  rw [setZ_streams_same] at hzF; cases hzF
  obtain ⟨hdiF, hsideF⟩ := WB.deflate hd
  have hdiF0 := hdiF
  obtain ⟨i, z0, sb, st, al, e0, hz0, hsb, hst, -, core⟩ := hdiF0
  cases e0; rw [setZ_streams_same] at hz0; cases hz0
  have hsb' : z.state = some sb := hsb
  -- back to the actual heap
  have hHe : setZ (setZ H s.strm (flatZ z)) s.strm z = H := by rw [setZ_setZ]; exact setZ_self hz
  have hnhF : ∀ sb0 st0 k, (flatZ z).state = some sb0 → (setZ H s.strm (flatZ z)).dstate sb0 = some st0 →
      st0.gzhead ≠ .val (some k) := fun sb0 st0 k e1 e2 => WB.nohdr sb0 st0 k e1 e2
  obtain ⟨hdi, hside⟩ := dinv_setZ (a := z) (setZ_streams_same _ _ _) (flat_eq z) hdiF hsideF hnhF
  rw [hHe] at hdi hside
  -- the owned blocks
  have hcs : c ≠ sb := by
    have hsplit : ownL (setZ H s.strm (flatZ z)) b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ [c, sb] := by
      simp [ownL, hsz, hB.buffers, blkOf, stBlk, hsb]
    have := (List.nodup_append.mp (hsplit ▸ hn)).2.1
    simp at this; exact this
  have hcO : c ∈ GzOwned W H (some b) := by simp [GzOwned, hs, hB.buffers]
  have hsbO : sb ∈ GzOwned W H (some b) := by simp [GzOwned, hs, hz, hsb']
  obtain ⟨d, hdc, hds⟩ := hB.fits
  have hin2 : inSize s = 2 * s.want.toNat := by simp [inSize, hwm]
  have hout2 : outSize s = s.want.toNat := by simp [outSize, hwm, hd]
  obtain ⟨ko, kx, eo, -, -, hko⟩ := WB.out hd
  have eo' : z.next_out = .ref (.heap c) (base + inSize s + ko) := eo
  have hko' : ko + z.avail_out.toNat = s.size.toNat := hko
  have hsw : s.size.toNat = s.want.toNat := by rw [hB.size]
  -- the input
  have hinR : NullOrRead H z.next_in z.avail_in.toNat ∧ Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat ∧
      NotInBlock sb z.next_in := by
    rcases hin with ⟨c1, base1, eb, hi⟩ | ⟨hr, ho⟩
    · rw [hB.buffers] at eb; cases eb
      rcases hi with ⟨k, ek, -, hk⟩ | ⟨e1, e2⟩
      · refine ⟨Or.inr ⟨.heap c, base + k, d, ek, hdc, by rw [hin2, hout2] at hds; omega⟩, ?_, ?_⟩
        · rw [eo', ek]; simp only [Disjoint]; right; right; rw [hin2]; omega
        · intro off e; rw [ek] at e; cases e; exact hcs rfl
      · rcases e2 with e2 | e2
        · exact absurd hd e2
        · rw [e2]; exact ⟨Or.inl rfl, by simp [Disjoint, eo'], fun off e => by cases e⟩
    · refine ⟨Or.inr hr, ?_, ho sb hsbO⟩
      obtain ⟨r, off, d1, ep, -, -⟩ := hr
      rw [eo', ep]; simp only [Disjoint]
      left; intro e; subst e; exact ho c hcO off ep
  have hreg : DRegisteredHeader H (some s.strm) none := by
    refine ⟨sb, st, ⟨⟨z, ⟨_, rfl, hz⟩, hsb'⟩, hst⟩, ?_⟩
    obtain ⟨hp, hhp⟩ := core.gzhead
    have hhp' : st.gzhead = .val hp := hhp
    cases hp with
    | none => exact hhp'
    | some k => exact absurd hhp' (WB.nohdr sb st k hsb hst)
  have hio : DStreamIO H (some s.strm) := by
    refine ⟨z, sb, none, ⟨_, rfl, hz⟩, hsb', hreg, fun k e => absurd e (by simp),
      hinR.1, Or.inr ⟨c, _, d, eo', hdc, by rw [hin2, hout2] at hds; omega⟩, fun off e => by
        rw [eo'] at e; cases e; exact hcs rfl, fun r hr => ?_⟩
    rcases hr with rfl | ⟨k, e, -⟩
    · exact ⟨hinR.2.1, hinR.2.2⟩
    · cases e
  obtain ⟨r, H', e, f, -, hdi', hside'⟩ := P.deflate H (some s.strm) flush hdi hside hv.2.2.1 hio
  obtain ⟨hco, hk, hdone⟩ := hD H H' (some s.strm) flush r hdi hside hv.2.2.1 hio hreg e
  obtain ⟨z', ⟨i', e1, hz'⟩, hadv, hmu⟩ := hco z ⟨_, rfl, hz⟩
  cases e1
  have hsi : stateIds H (some s.strm) = [sb] := by simp [stateIds, hz, hsb']
  have hdo : dOutputRanges H (some s.strm) = [(z.next_out, z.avail_out.toNat)] := by simp [dOutputRanges, hz]
  rw [hsi, hdo] at f
  have f' : DFrame H H' [s.strm] [sb] [] [(z.next_out, z.avail_out.toNat)] := by simpa [streamIds] using f
  have fF := dframe_setZ f' (flatZ z) (flatZ z')
  have hst' : (flatZ z').state = (flatZ z).state := hadv.2.2.2.2
  have hkF := dkeep_setZ hz hz' rfl rfl hk (a := flatZ z) (a' := flatZ z')
  have hnh' : ∀ sb0 st0 k, z'.state = some sb0 → H'.dstate sb0 = some st0 → st0.gzhead ≠ .val (some k) := by
    intro sb0 st0 k e1 e2 e3
    rcases hk.2.2 (some k) ⟨sb0, st0, ⟨⟨z', ⟨_, rfl, hz'⟩, e1⟩, e2⟩, e3⟩ with e4 | e4
    · cases e4
    · obtain ⟨b0, st1, ⟨⟨z1, ⟨i1, e5, hz1⟩, hb0⟩, hst1⟩, hg1⟩ := e4
      cases e5; rw [hz] at hz1; cases hz1
      exact WB.nohdr b0 st1 k hb0 hst1 hg1
  have hdiF' := dinv_setZ (a := flatZ z') hz' (flat_eq' z') hdi' hside' hnh'
  have hadvF : BufAdv (flatZ z) (flatZ z') :=
    ⟨UInt32.le_refl _, hadv.2.1, ⟨by simp [flatZ], rfl⟩, hadv.2.2.2.1, hadv.2.2.2.2⟩
  obtain ⟨-, houtF⟩ := wbuf_adv hd (Or.inr ⟨rfl, Or.inr rfl⟩) (WB.out hd) hadvF
  obtain ⟨hv', hs', g⟩ := invWS_dcall hv hsF hsz hd hB (setZ_streams_same _ _ _) hsb fF
    (fun x hx c' off e2 => by simp at hx; rw [hx, eo'] at e2; cases e2; rfl) (setZ_streams_same _ _ _) hst'
    (Or.inr ⟨rfl, rfl⟩) houtF hkF hdiF'
  have hsH' : W.gz H' b = some s := hs'
  refine ⟨r, H', z', e, hz', hadv, hmu, fun h1 h2 => hdone h1 h2 z' ⟨_, rfl, hz'⟩,
    ⟨hsH', hz', hsz, hv', ?_⟩, g⟩
  rcases hin with ⟨c1, base1, eb, hi⟩ | hc
  · refine Or.inl ⟨c1, base1, eb, ?_⟩
    rw [hB.buffers] at eb; cases eb
    exact ((wbuf_adv hd hi (WB.out hd) hadv).1).imp_right fun ⟨e1, e2⟩ => ⟨e1, Or.inr e2⟩
  · refine Or.inr (callerIn_step g hv.2.2.2.1.1 (gzOwned_setZ W H b hs hz rfl)
      (gzOwned_setZ W H' b hsH' hz' rfl) hc ?_ ?_)
    · obtain ⟨⟨r0, o0, d0, ep, -, -⟩, -⟩ := hc
      have ha := hadv.2.2.1
      rw [ep] at ha; simp only [Adv] at ha
      have l1 := UInt32.le_iff_toNat_le.mp hadv.1
      exact Or.inr ⟨r0, o0, z.avail_in.toNat - z'.avail_in.toNat, ep, ha, by omega⟩
    · intro _; exact UInt32.le_iff_toNat_le.mp hadv.1

end ZlibNgF.Proof.GzWrite
