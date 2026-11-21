import ZlibNgF.Proof.«gzwrite.c.write»

/-!
# The direct path of `gz_write` (`ZlibNgF`)

For `len >= size`, `gz_write` points `next_in` at the caller's buffer and runs `gz_comp` on it in pieces of at most
`2^32 - 1` bytes (`wdBody`). Between the pieces the stream holds no input and `next_in` lies in the caller's buffer,
which `GzWBuf.inp` does not allow: the invariant holds of the *flat* heap (`flatZ`), and the caller's range is
described apart (`WDState`). `gz_comp` is entered through `GzWX` with `CallerIn`. When `gz_comp` fails, patch 0011
points `next_in` back at `in` with no input, and after the loop `gz_write` does the same, so the invariant holds of
the actual heap again (`invWS_unflat`).

Then `gz_write` itself (`gz_write_spec`): the buffers (`gz_write_init`), the pending seek (`gz_zero_spec`), the
position bound of patch 0014 (`Z_DATA_ERROR` when `len` exceeds the room left below `GZ_OFF_MAX`), and the two paths
(`wmid_spec`). It keeps the invariant `GzInvWS` and is a step of the file (`WPost`), given `GzCompSpec` and
`DeflateGz`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

theorem flatZ_with (z : ZStream) (p : BPtr) (n : UInt32) : flatZ { z with next_in := p, avail_in := n } = flatZ z := rfl

theorem flatZ_avail (z : ZStream) (n : UInt32) : flatZ { z with avail_in := n } = flatZ z := rfl

theorem flatZ_next (z : ZStream) (p : BPtr) : flatZ { z with next_in := p } = flatZ z := rfl

/-- The blocks of a file depend only on its `path`, `msg`, `buffers` and the state of its stream. -/
theorem owned_eq {w W : World} {h H : Heap} {b : Nat} {s s' : GzState} {z z' : ZStream} (hs : w.gz h b = some s)
    (hs' : W.gz H b = some s') (hp : s'.path = s.path) (hm : s'.msg = s.msg) (hb : s'.buffers = s.buffers)
    (hst : s'.strm = s.strm) (hz : h.streams s.strm = some z) (hz' : H.streams s.strm = some z')
    (hzs : z'.state = z.state) : GzOwned W H (some b) = GzOwned w h (some b) := by
  simp only [GzOwned, hs, hs', hp, hm, hb, hst, hz, hz', hzs]

/-- A caller pointer outside the blocks of a file stays outside when it moves within its block, and the blocks do not
grow. -/
theorem outside_mv {w W : World} {h H : Heap} {b : Nat} {r : BRef} {o : Nat}
    (hsub : ∀ c ∈ GzOwned W H (some b), c ∈ GzOwned w h (some b)) (ho : OutsideGz w h (some b) (.ref r o)) (k : Nat) :
    OutsideGz W H (some b) (.ref r (o + k)) := by
  intro c hc off e
  cases e
  exact ho c (hsub c hc) o rfl

/-- The state of the direct loop of `gz_write` on the file `b`, from `w0`, `h0`, with the stream of `s` and the
caller's buffer `L` bytes from `.ref r o`: the invariant of the flat heap, no input in the stream, and either the loop
goes on with `next_in` inside the caller's buffer and room for the rest in `x.pos`, or it stopped with `next_in` back
at `in`. -/
def WDState (w0 : World) (h0 : Heap) (b : Nat) (s : GzState) (r : BRef) (o L : Nat) (st : WriteLoop) (W : World)
    (H : Heap) : Prop :=
  ∃ s2 z2, W.gz H b = some s2 ∧ H.streams s.strm = some z2 ∧ z2.avail_in = 0 ∧
    GzInvWS W (setZ H s.strm (flatZ z2)) (some b) ∧ GStep w0 h0 W (setZ H s.strm (flatZ z2)) b [] ∧
    ZFix s s2 ∧ s2.size ≠ 0 ∧ s2.skip = 0 ∧ ReadSlice H (.ref r o) L ∧ OutsideGz W H (some b) (.ref r o) ∧
    ((st.ctl = .go ∧ ∃ k, z2.next_in = .ref r (o + k) ∧ k + st.len.toNat ≤ L ∧
        s2.pos.toInt + st.len.toNat ≤ GZ_OFF_MAX.toInt) ∨
      (st.ctl = .ret ∧ s2.«in» = .val z2.next_in))

/-- The `in` pointer of a write handle with buffers. -/
theorem in_of {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s)
    (hsz : s.size ≠ 0) : ∃ c base, s.«in» = .val (.ref (.heap c) base) ∧ s.buffers = .val (.ref (.heap c) base) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, -, -⟩ := (sh.write hwm).bufs hsz
  exact ⟨c, base, hB.inp, hB.buffers⟩

/-- Back from the flat heap with no input and `next_in` at `in`. -/
theorem unflat_in {w : World} {h : Heap} {b : Nat} {s : GzState} {z : ZStream} (hz : h.streams s.strm = some z)
    (hv : GzInvWS w (setZ h s.strm (flatZ z)) (some b)) (hs : w.gz h b = some s) (hsz : s.size ≠ 0)
    (ha : z.avail_in = 0) (hi : s.«in» = .val z.next_in) :
    GzInvWS w h (some b) ∧ GStep w (setZ h s.strm (flatZ z)) w h b [] := by
  refine invWS_unflat hz hv hs hsz fun c base hb => ?_
  rw [hb.inp] at hi
  have e : z.next_in = .ref (.heap c) base := (Ival.val.inj hi).symm
  rw [e]
  exact Or.inl ⟨0, by simp, Nat.le_refl _, by rw [ha]; simp⟩

/-! ## A round of the direct path -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- The direct round after the piece `n` is chosen (copied from the translation). -/
def wdTail (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) (n : UInt32) : G WriteLoop := do
  lm (wrZ strm fun z => { z with avail_in := n })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
    return { s with ctl := .ret }
  return { s with len := s.len - n.toUInt64 }

theorem wdBody_eq (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) :
    wdBody state strm s = wdTail state strm s
      (if (0xFFFFFFFF : UInt32).toUInt64 > s.len then s.len.toUInt32 else 0xFFFFFFFF) := by
  unfold wdBody wdTail
  dsimp only
  by_cases hc : (0xFFFFFFFF : UInt32).toUInt64 > s.len
  · simp only [hc, ↓reduceIte]
  · simp only [hc, ↓reduceIte]

theorem wd_tail (C : GzCompSpec) (G : DeflateGz) {w0 W : World} {h0 H : Heap} {b : Nat} {s : GzState} {r : BRef}
    {o L : Nat} (hs0 : ∃ s0, w0.gz h0 b = some s0) (st : WriteLoop) (hst : WDState w0 h0 b s r o L st W H)
    (hgo : st.ctl = .go) (n : UInt32) (hn1 : 1 ≤ n.toNat) (hn2 : n.toNat ≤ st.len.toNat) :
    GSat W H (wdTail (some b) (some s.strm) st n) (fun st' W' H' => WDState w0 h0 b s r o L st' W' H' ∧
      (st'.ctl = .go → st'.len.toNat < st.len.toNat)) := by
  obtain ⟨s2, z2, hs2, hz2, ha2, hv2, g2, zf2, hsz2, hsk2, hr2, ho2, hc2⟩ := hst
  obtain ⟨-, k, hk, hkL, hpos⟩ := hc2.resolve_right (fun ⟨e, _⟩ => by rw [hgo] at e; cases e)
  have hstrm : s2.strm = s.strm := zf2.strm
  have hs2F : W.gz (setZ H s.strm (flatZ z2)) b = some s2 := hs2
  have hwm := modeOf hs2F hv2.2.1
  obtain ⟨sh, hn⟩ := inv_of hs2F hv2.1
  have hP := sh.pos
  have hpw := hP.write_pos hwm
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  unfold wdTail
  -- `avail_in = n`
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s.strm { z2 with avail_in := n })
    (by simp [lm_app, wrZ_run hz2]) ?_)
  have hs2a : W.gz (setZ H s.strm { z2 with avail_in := n }) b = some s2 := hs2
  refine GSat.bind (GSat.of_eq (rdG_app' hs2a _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s2.pos.toInt + n.toNat))
    (by simp only [lm_app, chkI64_ok (v := s2.pos.toInt + n.toNat) (by omega) (by omega)]; rfl) ?_)
  refine GSat.bind (GSat.of_eq (wrG_app hs2a _) ?_)
  have hp1 : (Int64.ofInt (s2.pos.toInt + n.toNat)).toInt = s2.pos.toInt + n.toNat :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hsk0 : s2.skip.toInt = 0 := by rw [hsk2]; rfl
  -- the store of `x.pos`, on the flat heap
  have sh3 := shape_posW sh hwm (Int64.ofInt (s2.pos.toInt + n.toNat)) s2.skip
    ⟨by dsimp only; omega, by dsimp only; rw [hp1]; omega, by dsimp only; rw [hp1]; omega,
      fun _ => by dsimp only; rw [hp1]; omega⟩
  obtain ⟨hv3, hs3, g3⟩ := invWS_store hv2 hs2F sh3 hn hwm rfl (fun c' hc _ => by
    simp only [GzOwned, gz_upd_same hs2F, hs2F] at hc ⊢; exact hc)
  generalize hW2 : ({ W with gzs := upd W.gzs b (some { s2 with pos := Int64.ofInt (s2.pos.toInt + n.toNat) }) } : World) = W2 at hv3 hs3 g3 ⊢
  have hfl : setZ (setZ H s.strm { z2 with avail_in := n }) s.strm (flatZ { z2 with avail_in := n }) =
      setZ H s.strm (flatZ z2) := by rw [setZ_setZ, flatZ_avail]
  -- `gz_comp` from `GzWX` with the caller's range
  obtain ⟨ψ, Gr, hψ⟩ := psi_of G
  have hs3a : W2.gz (setZ H s.strm { z2 with avail_in := n }) b =
      some { s2 with pos := Int64.ofInt (s2.pos.toInt + n.toNat) } := hs3
  have hz3 : (setZ H s.strm { z2 with avail_in := n }).streams
      ({ s2 with pos := Int64.ofInt (s2.pos.toInt + n.toNat) } : GzState).strm = some { z2 with avail_in := n } := by
    show (setZ H s.strm _).streams s2.strm = _
    rw [hstrm]; exact setZ_streams_same _ _ _
  have hsub3 : ∀ c ∈ GzOwned W2 (setZ H s.strm { z2 with avail_in := n }) (some b), c ∈ GzOwned W H (some b) := by
    intro c hc
    rw [owned_eq (z := z2) (z' := { z2 with avail_in := n }) hs2 hs3a rfl rfl rfl rfl (by rw [hstrm]; exact hz2)
      (by rw [hstrm]; exact setZ_streams_same _ _ _) rfl] at hc
    exact hc
  have wx : GzWX W2 (setZ H s.strm { z2 with avail_in := n }) b { s2 with pos := Int64.ofInt (s2.pos.toInt + n.toNat) }
      { z2 with avail_in := n } := by
    refine ⟨hs3a, hz3, hsz2, ?_, Or.inr ⟨?_, ?_⟩⟩
    · show GzInvWS W2 (setZ (setZ H s.strm { z2 with avail_in := n }) s2.strm (flatZ { z2 with avail_in := n })) (some b)
      rw [hstrm, hfl]; exact hv3
    · obtain ⟨r', off, d, ep, hd, hle⟩ := hr2
      cases ep
      exact ⟨r, o + k, d, hk, hd, by show o + k + n.toNat ≤ d.size; omega⟩
    · intro c hc off e'
      exact outside_mv hsub3 ho2 k c hc off (hk.symm.trans e')
  refine GSat.bind (GSat.mono (C G ψ Gr hψ W2 _ b ZlibNg.Deflate.Z_NO_FLUSH _ _ hs3a hz3 (Or.inr wx))
    fun rc W4 H4 q => ?_)
  obtain ⟨s4, z4, hs4, hz4, fx, hbuf, -, gF, -, -, hwx, -, -, hadv, hdir, hrc, hok, -, -⟩ := q
  dsimp only at hz4 hadv hdir
  rw [hstrm] at hz4
  have hsz4 : s4.size ≠ 0 := by rw [(hbuf hsz2).1]; exact hsz2
  obtain ⟨-, -, -, hv4, -⟩ := hwx hsz4
  have hstrm4 : s4.strm = s.strm := by rw [fx.strm]; exact hstrm
  rw [hstrm4] at hv4
  rw [hstrm, hfl] at gF
  -- the whole run so far, between flat heaps
  have g4 : GStep w0 h0 W4 (setZ H4 s.strm (flatZ z4)) b [] :=
    (g2.trans g3 hs0 ⟨s2, hs2F⟩).trans gF hs0 ⟨_, hs3⟩
  have zf4 : ZFix s s4 := zf2.trans (ZFix.trans
    (⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ : ZFix s2 { s2 with pos := Int64.ofInt (s2.pos.toInt + n.toNat) })
    (ZFix.of_w fx))
  have hsk4 : s4.skip = 0 := by rw [fx.skip]; exact hsk2
  -- the caller's buffer after `gz_comp`
  have hfr : FreshBlocks (setZ H s.strm (flatZ z2)) := hv2.2.2.2.1.1
  have hoF : OutsideGz W2 (setZ H s.strm (flatZ z2)) (some b) (.ref r o) := by
    have := outside_mv (W := W2) (H := setZ H s.strm (flatZ z2)) (fun c hc => by
      rw [owned_eq (z := z2) (z' := flatZ z2) hs2 hs3 rfl rfl rfl rfl (by rw [hstrm]; exact hz2)
        (by rw [hstrm]; exact setZ_streams_same _ _ _) rfl] at hc
      exact hc) ho2 0
    simpa using this
  obtain ⟨hr4, ho4⟩ := callerBuf_step (gF : GStep W2 (setZ H s.strm (flatZ z2)) W4 (setZ H4 s.strm (flatZ z4)) b [])
    hfr hr2 hoF
  have hown4 : GzOwned W4 (setZ H4 s.strm (flatZ z4)) (some b) = GzOwned W4 H4 (some b) := by
    have := gzOwned_setZ W4 H4 b hs4 (z := z4) (z' := flatZ z4) (by rw [hstrm4]; exact hz4) rfl
    rw [hstrm4] at this; exact this
  have ho4' : OutsideGz W4 H4 (some b) (.ref r o) := fun c hc => ho4 c (by rw [hown4]; exact hc)
  have hr4' : ReadSlice H4 (.ref r o) L := hr4
  refine GSat.ite (fun _ => ?_) (fun hne => ?_)
  · -- `gz_comp` failed: no input, `next_in` back at `in`
    obtain ⟨c, base, hin, -⟩ := in_of hv4 hs4 hsz4
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W4) (h' := setZ H4 s.strm { z4 with avail_in := 0 })
      (by simp [lm_app, wrZ_run hz4]) ?_)
    have hs5 : W4.gz (setZ H4 s.strm { z4 with avail_in := 0 }) b = some s4 := hs4
    refine GSat.bind (GSat.of_eq (ldGz_app hs5) ?_)
    rw [hin]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W4)
      (h' := setZ H4 s.strm { z4 with avail_in := 0, next_in := .ref (.heap c) base })
      (by simp [lm_app, wrZ_run (setZ_streams_same H4 s.strm { z4 with avail_in := 0 }), setZ_setZ]) ?_)
    have hfl6 : setZ (setZ H4 s.strm { z4 with avail_in := 0, next_in := .ref (.heap c) base }) s.strm
        (flatZ { z4 with avail_in := 0, next_in := .ref (.heap c) base }) = setZ H4 s.strm (flatZ z4) := by
      rw [setZ_setZ]; rfl
    have hown6 : GzOwned W4 (setZ H4 s.strm { z4 with avail_in := 0, next_in := .ref (.heap c) base }) (some b) =
        GzOwned W4 H4 (some b) := by
      have := gzOwned_setZ W4 H4 b hs4 (z := z4) (z' := { z4 with avail_in := 0, next_in := .ref (.heap c) base })
        (by rw [hstrm4]; exact hz4) rfl
      rw [hstrm4] at this; exact this
    refine GSat.pure ⟨⟨s4, _, hs4, setZ_streams_same _ _ _, rfl, by rw [hfl6]; exact hv4, by rw [hfl6]; exact g4,
      zf4, hsz4, hsk4, hr4', fun c hc => ho4' c (by rw [← hown6]; exact hc), Or.inr ⟨rfl, hin⟩⟩, fun e => by cases e⟩
  · -- `gz_comp` succeeded: the piece is consumed
    have hr0 : rc = 0 := by rcases hrc with e | e; exact e; simp [e] at hne
    have ha4 : z4.avail_in = 0 := ((hok hr0).2.1 (by decide))
    have hnl : n.toUInt64 ≤ st.len := UInt64.le_iff_toNat_le.mpr (by rw [UInt32.toNat_toUInt64]; omega)
    have hlen : (st.len - n.toUInt64).toNat = st.len.toNat - n.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hnl, UInt32.toNat_toUInt64]
    have hpos4 : s4.pos.toInt = s2.pos.toInt + n.toNat := by rw [fx.pos]; exact hp1
    have hk4 : ∃ k', z4.next_in = .ref r (o + k') ∧ k' + (st.len - n.toUInt64).toNat ≤ L := by
      by_cases hd : s2.direct = 0
      · have a := hadv hsz2 hd
        rw [hk, ha4] at a
        simp only [Adv] at a
        exact ⟨k + n.toNat, by rw [a]; simp [Nat.add_assoc], by rw [hlen]; omega⟩
      · exact ⟨k, by rw [hdir hd, hk], by rw [hlen]; omega⟩
    obtain ⟨k', hk', hkL'⟩ := hk4
    exact GSat.pure ⟨⟨s4, z4, hs4, hz4, ha4, hv4, g4, zf4, hsz4, hsk4, hr4', ho4',
      Or.inl ⟨hgo, k', hk', hkL', by rw [hpos4, hlen]; omega⟩⟩, fun _ => by dsimp only; rw [hlen]; omega⟩

/-- The piece of a direct round: `min(len, 2^32 - 1)`. -/
theorem wd_n (len : UInt64) (hl : len ≠ 0) :
    1 ≤ (if (0xFFFFFFFF : UInt32).toUInt64 > len then len.toUInt32 else 0xFFFFFFFF).toNat ∧
      (if (0xFFFFFFFF : UInt32).toUInt64 > len then len.toUInt32 else 0xFFFFFFFF).toNat ≤ len.toNat := by
  have hl' : len.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  split
  · next hc =>
    have hc' := UInt64.lt_iff_toNat_lt.mp hc
    have e : (0xFFFFFFFF : UInt32).toUInt64.toNat = 2 ^ 32 - 1 := by decide
    rw [e] at hc'
    rw [UInt64.toNat_toUInt32]; omega
  · next hc =>
    have hc' : ¬ len.toNat < (0xFFFFFFFF : UInt32).toUInt64.toNat := fun h' => hc (UInt64.lt_iff_toNat_lt.mpr h')
    have e : (0xFFFFFFFF : UInt32).toUInt64.toNat = 2 ^ 32 - 1 := by decide
    rw [e] at hc'
    have e2 : (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 - 1 := by decide
    rw [e2]; omega

/-- **The direct loop of `gz_write`**: it ends, with no input in the stream, and with `next_in` at `in` when it
stopped on a failed `gz_comp`. -/
theorem wd_loop (C : GzCompSpec) (G : DeflateGz) {w0 W : World} {h0 H : Heap} {b : Nat} {s : GzState} {r : BRef}
    {o L : Nat} (hs0 : ∃ s0, w0.gz h0 b = some s0) (st : WriteLoop) (hst : WDState w0 h0 b s r o L st W H)
    (hgo : st.ctl = .go) (hl0 : st.len ≠ 0) :
    GSat W H (gdoWhile (wdBody (some b) (some s.strm)) wCond st)
      (fun lp W' H' => WDState w0 h0 b s r o L lp W' H' ∧ (lp.ctl = .go → lp.len = 0)) := by
  refine gsat_gdoWhile (fun st W H => st.ctl = .go ∧ st.len ≠ 0 ∧ WDState w0 h0 b s r o L st W H)
    (fun st _ _ => st.len.toNat) _ ?_ ⟨hgo, hl0, hst⟩ ?_
  · rintro st W1 H1 ⟨hgo1, hl1, hst1⟩
    rw [wdBody_eq]
    obtain ⟨hn1, hn2⟩ := wd_n st.len hl1
    refine GSat.mono (wd_tail C G hs0 st hst1 hgo1 _ hn1 hn2) fun r3 W3 H3 q => ?_
    obtain ⟨hst3, hlt⟩ := q
    unfold wCond
    by_cases hc : r3.ctl = .go
    · refine GSat.ite (fun hc' => by simp [hc] at hc') (fun _ => GSat.pure ⟨fun e => ⟨⟨hc, by simpa using e, hst3⟩,
        hlt hc⟩, fun e => ⟨hst3, fun _ => by simpa using e⟩⟩)
    · refine GSat.ite (fun _ => GSat.pure ⟨fun e => by simp at e, fun _ => ⟨hst3, fun e => absurd e hc⟩⟩)
        (fun hc' => by simp at hc'; exact absurd hc' hc)
  · show st.len.toNat < fuel
    have := st.len.toNat_lt
    unfold fuel; omega

theorem lit_wpos : gzLits.findIdx? (· == "write position does not fit in z_off64_t") = some 13 := by
  simp [gzLits, List.findIdx?_cons]

theorem lit_wpos_get : gzLits[13]? = some "write position does not fit in z_off64_t" := by decide

theorem nonul_wpos : NoNul "write position does not fit in z_off64_t" := by decide

/-- What `gz_write` leaves: the invariant, a step of the file, and the fields of `ZFix`. -/
def WPost (w : World) (h : Heap) (b : Nat) (s : GzState) (_r : UInt64) (W : World) (H : Heap) : Prop :=
  ∃ s', W.gz H b = some s' ∧ GzInvWS W H (some b) ∧ GStep w h W H b [] ∧ ZFix s s'

/-- After the direct loop: `next_in` back at `in`, the invariant again. -/
theorem wd_after {w0 W : World} {h0 H : Heap} {b : Nat} {s : GzState} {r : BRef} {o L : Nat} {lp : WriteLoop}
    (hst : WDState w0 h0 b s r o L lp W H) (hs0 : ∃ s0, w0.gz h0 b = some s0) (put : UInt64) :
    GSat W H (do
      if lp.ctl == .ret then
        return 0
      let i ← (← ldGz (some b)).«in».get
      lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with next_in := i })
      return put) (WPost w0 h0 b s) := by
  obtain ⟨s2, z2, hs2, hz2, ha2, hv2, g2, zf2, hsz2, -, -, -, hc⟩ := hst
  have hstrm : s2.strm = s.strm := zf2.strm
  have hz2' : H.streams s2.strm = some z2 := by rw [hstrm]; exact hz2
  have hv2' : GzInvWS W (setZ H s2.strm (flatZ z2)) (some b) := by rw [hstrm]; exact hv2
  have hs2F : W.gz (setZ H s.strm (flatZ z2)) b = some s2 := hs2
  by_cases hr : lp.ctl = .ret
  · have hi : s2.«in» = .val z2.next_in := by
      rcases hc with ⟨e, -⟩ | ⟨-, e⟩
      · rw [hr] at e; cases e
      · exact e
    obtain ⟨hv, g⟩ := unflat_in hz2' hv2' hs2 hsz2 ha2 hi
    rw [hstrm] at g
    simp only [hr]
    exact GSat.pure ⟨s2, hs2, hv, g2.trans g hs0 ⟨s2, hs2F⟩, zf2⟩
  · obtain ⟨c, base, hin, -⟩ := in_of hv2 hs2F hsz2
    have hr' : (lp.ctl == .ret) = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte]
    refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
    rw [hin]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s.strm { z2 with next_in := .ref (.heap c) base })
      (by simp [lm_app, wrZ_run hz2]) ?_)
    have hz3 : (setZ H s.strm { z2 with next_in := .ref (.heap c) base }).streams s2.strm =
        some { z2 with next_in := .ref (.heap c) base } := by rw [hstrm]; exact setZ_streams_same _ _ _
    have hfl : setZ (setZ H s.strm { z2 with next_in := .ref (.heap c) base }) s2.strm
        (flatZ { z2 with next_in := .ref (.heap c) base }) = setZ H s.strm (flatZ z2) := by
      rw [hstrm, setZ_setZ]; rfl
    obtain ⟨hv, g⟩ := unflat_in hz3 (by rw [hfl]; exact hv2) hs2 hsz2 ha2 hin
    rw [hfl] at g
    exact GSat.pure ⟨s2, hs2, hv, g2.trans g hs0 ⟨s2, hs2F⟩, zf2⟩

/-- The direct path of `gz_write` after the input left in `in` is compressed. -/
theorem wd_path (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState} {z : ZStream}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip = 0) (hs0 : ∃ s0, w.gz h b = some s0) (hz : H.streams s.strm = some z)
    (ha : z.avail_in = 0) (buf : BPtr) (len put : UInt64) (hl0 : len ≠ 0)
    (hpos : s1.pos.toInt + len.toNat ≤ GZ_OFF_MAX.toInt) (hr : ReadSlice H buf len.toNat)
    (ho : OutsideGz W H (some b) buf) :
    GSat W H (do
      lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with next_in := buf })
      let lp ← gdoWhile (wdBody (some b) (some s.strm)) wCond ⟨buf, len, .go⟩
      if lp.ctl == .ret then
        return 0
      let i ← (← ldGz (some b)).«in».get
      lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with next_in := i })
      return put) (WPost w h b s) := by
  have hstrm : s1.strm = s.strm := zf.strm
  obtain ⟨r, o, d, ebuf, hd, hle⟩ := hr
  subst ebuf
  refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := setZ H s.strm { z with next_in := .ref r o })
    (by simp [lm_app, wrZ_run hz]) ?_)
  obtain ⟨hvF, gF⟩ := invWS_flat hv hs hsz (z := z) (by rw [hstrm]; exact hz)
  rw [hstrm] at hvF gF
  have hfl : setZ (setZ H s.strm { z with next_in := .ref r o }) s.strm (flatZ { z with next_in := .ref r o }) =
      setZ H s.strm (flatZ z) := by rw [setZ_setZ]; rfl
  have hst : WDState w h b s r o len.toNat ⟨.ref r o, len, .go⟩ W (setZ H s.strm { z with next_in := .ref r o }) := by
    refine ⟨s1, _, hs, setZ_streams_same _ _ _, ha, by rw [hfl]; exact hvF, by rw [hfl]; exact g.trans gF hs0 ⟨s1, hs⟩,
      zf, hsz, hsk, ⟨r, o, d, rfl, hd, hle⟩, ?_, Or.inl ⟨rfl, 0, by simp, by simp, hpos⟩⟩
    intro c hc
    refine ho c ?_
    rw [owned_eq (z := z) (z' := { z with next_in := .ref r o }) (H := setZ H s.strm { z with next_in := .ref r o }) hs hs rfl rfl rfl rfl (by rw [hstrm]; exact hz)
      (by rw [hstrm]; exact setZ_streams_same _ _ _) rfl] at hc
    exact hc
  refine GSat.bind (GSat.mono (wd_loop C G hs0 _ hst rfl hl0) fun lp W3 H3 q => ?_)
  exact wd_after q.1 hs0 put

theorem room_toNat (p : Int64) (h1 : 0 ≤ p.toInt) (h2 : p.toInt ≤ GZ_OFF_MAX.toInt) :
    (Int64.ofInt (GZ_OFF_MAX.toInt - p.toInt)).toUInt64.toNat = (GZ_OFF_MAX.toInt - p.toInt).toNat := by
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  have e : (Int64.ofInt (GZ_OFF_MAX.toInt - p.toInt)).toInt = GZ_OFF_MAX.toInt - p.toInt :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  rw [i64_toNat_toUInt64 _ (by omega), e]

/-- **`gz_write` after the buffers are made and the pending seek is done** (`wMid`): the position bound of patch
0014, then the buffered path (`wb_loop`) or the direct path (`wd_path`). -/
theorem wmid_spec (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip = 0) (hs0 : ∃ s0, w.gz h b = some s0) (buf : BPtr) (len put : UInt64)
    (hl0 : len ≠ 0) (hr : ReadSlice H buf len.toNat) (ho : OutsideGz W H (some b) buf) :
    GSat W H (wMid (some b) buf len put) (WPost w h b s) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have hP := sh.pos
  have hpw := hP.write_pos hwm
  have hps := hP.pos_skip
  have hsk0 : s1.skip.toInt = 0 := by rw [hsk]; rfl
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  have hstrm : s1.strm = s.strm := zf.strm
  have hfr : FreshBlocks H := hv.2.2.2.1.1
  unfold wMid
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (GZ_OFF_MAX.toInt - s1.pos.toInt))
    (by simp only [lm_app, chkI64_ok (v := GZ_OFF_MAX.toInt - s1.pos.toInt) (by omega) (by omega)]; rfl) ?_)
  have hroom := room_toNat s1.pos hpw (by omega)
  refine GSat.ite (fun _ => ?_) (fun hle => ?_)
  · refine GSat.mono (gz_error_litW _ 13 lit_wpos lit_wpos_get nonul_wpos hv hs ZlibNg.Inflate.Z_DATA_ERROR
      (0 : UInt64)) fun r' W' H' q => ?_
    obtain ⟨rfl, s', hs', he, hv', -, g'⟩ := q
    exact ⟨s', hs', hv', g.trans g' hs0 ⟨s1, hs⟩, zf.trans (ZFix.of_w (WFix.of_err he))⟩
  · have hle' : ¬ (Int64.ofInt (GZ_OFF_MAX.toInt - s1.pos.toInt)).toUInt64.toNat < len.toNat :=
      fun h' => hle (UInt64.lt_iff_toNat_lt.mpr h')
    rw [hroom] at hle'
    have hpos : s1.pos.toInt + len.toNat ≤ GZ_OFF_MAX.toInt := by omega
    refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    rw [hstrm]
    refine GSat.ite (fun hlt => ?_) (fun _ => ?_)
    · have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      rw [UInt32.toNat_toUInt64] at hlt'
      obtain ⟨c, base, z0, hB, -, -⟩ := (sh.write hwm).bufs hsz
      have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
      have hw30 := sh.want_hi
      refine GSat.bind (GSat.mono (wb_loop C G hv hs g zf hsz hsk hs0 buf len hl0 (by omega) hpos hr ho)
        fun lp W3 H3 q => ?_)
      obtain ⟨s3, hs3, hv3, g3, zf3, -, -, -⟩ := q
      exact GSat.ite (fun _ => GSat.pure ⟨s3, hs3, hv3, g3, zf3⟩) (fun _ => GSat.pure ⟨s3, hs3, hv3, g3, zf3⟩)
    · obtain ⟨z, hz⟩ := sh.strm
      rw [hstrm] at hz
      refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
      refine GSat.ite (fun _ => ?_) (fun hai => ?_)
      · refine GSat.bind (GSat.mono (comp_inv C G hv hs _) fun rc W2 H2 q => ?_)
        obtain ⟨s2, z2, hs2, hz2, hv2, g2, fx, hsz2, hrc, hok⟩ := q
        refine GSat.ite (fun _ => GSat.pure ⟨s2, hs2, hv2, g.trans g2 hs0 ⟨s1, hs⟩, zf.trans (ZFix.of_w fx)⟩)
          (fun hne => ?_)
        have hr0 : rc = 0 := by rcases hrc with e | e; exact e; simp [e] at hne
        obtain ⟨hr2, ho2⟩ := callerBuf_step g2 hfr hr ho
        rw [hstrm] at hz2
        exact wd_path C G hv2 hs2 (g.trans g2 hs0 ⟨s1, hs⟩) (zf.trans (ZFix.of_w fx)) (by rw [hsz2 hsz]; exact hsz)
          (by rw [fx.skip]; exact hsk) hs0 hz2 ((hok hr0).2 (by decide)) buf len put hl0 (by rw [fx.pos]; exact hpos)
          hr2 ho2
      · exact wd_path C G hv hs g zf hsz hsk hs0 hz (by simpa using hai) buf len put hl0 hpos hr ho

/-- `gz_write` after the buffers are made (copied from the translation). -/
def wSkip (state : GzPtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  if (← rdG state (·.skip)) != 0 then
    if (← gz_zero state) == -1 then
      return 0
  wMid state buf len len

theorem gz_write_eq' (state : GzPtr) (buf : BPtr) (len : UInt64) : gz_write state buf len = (do
    if len == 0 then
      return 0
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return 0
    wSkip state buf len) := rfl

theorem wskip_spec (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hs0 : ∃ s0, w.gz h b = some s0) (buf : BPtr) (len : UInt64)
    (hl0 : len ≠ 0) (hr : ReadSlice H buf len.toNat) (ho : OutsideGz W H (some b) buf) :
    GSat W H (wSkip (some b) buf len) (WPost w h b s) := by
  unfold wSkip
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hk => ?_) (fun hk => wmid_spec C G hv hs g zf hsz (by simpa using hk) hs0 buf len len hl0 hr ho)
  refine GSat.bind (GSat.mono (gz_zero_spec C G hv hs (by simpa using hk)) fun rz W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2, zf2, hrz, hok⟩ := q
  refine GSat.ite (fun _ => GSat.pure ⟨s2, hs2, hv2, g.trans g2 hs0 ⟨s1, hs⟩, zf.trans zf2⟩) (fun hne => ?_)
  have hr0 : rz = 0 := by rcases hrz with e | e; exact e; simp [e] at hne
  obtain ⟨hr2, ho2⟩ := callerBuf_step g2 hv.2.2.2.1.1 hr ho
  exact wmid_spec C G hv2 hs2 (g.trans g2 hs0 ⟨s1, hs⟩) (zf.trans zf2) (hok hr0).2 (hok hr0).1 hs0 buf len len hl0
    hr2 ho2

/-- **`gz_write`** on a write handle, with a caller buffer for `len` bytes. -/
theorem gz_write_spec (C : GzCompSpec) (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (buf : BPtr) (len : UInt64)
    (hin : GzIn w h (some b) buf len.toNat) :
    GSat w h (gz_write (some b) buf len) (WPost w h b s) := by
  rw [gz_write_eq']
  refine GSat.ite (fun _ => GSat.pure ⟨s, hs, hv, GStep.refl w h b [], ZFix.refl s⟩) (fun hl => ?_)
  have hl0 : len ≠ 0 := by simpa using hl
  have hl' : len.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
  obtain ⟨hr, ho⟩ := hin.resolve_left hl'
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  by_cases hz : s.size = 0
  · refine GSat.ite (fun _ => ?_) (fun hc => by simp [hz] at hc)
    refine GSat.bind (GSat.mono (gz_write_init_spec G hv hs hz) fun r W H q => ?_)
    obtain ⟨s', hs', hv', g, -, fx, hr'⟩ := q
    refine GSat.ite (fun _ => GSat.pure ⟨s', hs', hv', g, ZFix.of_w fx⟩) (fun hc => ?_)
    rcases hr' with ⟨rfl, hsz⟩ | rfl
    · obtain ⟨hr2, ho2⟩ := callerBuf_step g hv.2.2.2.1.1 hr ho
      exact wskip_spec C G hv' hs' g (ZFix.of_w fx) hsz ⟨s, hs⟩ buf len hl0 hr2 ho2
    · simp at hc
  · refine GSat.ite (fun hc => by simp at hc; exact absurd hc hz) (fun _ => ?_)
    exact wskip_spec C G hv hs (GStep.refl w h b []) (ZFix.refl s) hz ⟨s, hs⟩ buf len hl0 hr ho

end ZlibNgF.Proof.GzWrite
