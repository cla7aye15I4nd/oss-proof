import ZlibNgF.Proof.«deflate_fast.c.cont»

/-!
# One trip of `deflate_fast` (`ZlibNgF`)

`trip_ok`: one trip of the outer loop of `deflate_fast` (`deflate_fast.c:27-127`) from `SLC` (the state holds
`lookahead` / `strstart`), the hash chains (`ChainOk`) and `match_len < WANT_MIN_MATCH`: `fill_window` when the
lookahead is short (keeping the chains, `FillFacts.fill_window_chain`); the insertion of `strstart` and, when the
returned head is within `MAX_DIST`, the match search on the chains (`fast_search`: a match of at most `lookahead` and
258 bytes at a distance in `1 .. MAX_DIST`); the tally of a literal or of the match, the insertions of the matched
positions after it (`sl_insert_spread`, `sl_insert_knuth`: the tally may have filled the symbol buffer), the
continuation loop of a match of 258 bytes (`cloop_ok`), and `FLUSH_BLOCK` when the buffer is full. The chains are
grown from the start of the trip and checked once `strstart` has moved past the inserted positions (`ck_of_cg`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FastTrip
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop ZlibNgF.Proof.InsertLoopW ZlibNgF.Proof.InsertChain
open ZlibNgF.Proof.FastSteps ZlibNgF.Proof.FastFrame ZlibNgF.Proof.FastCont
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateFast

/-- The invariant of the outer loop over `(exit, bflush, match_len)`. -/
def OI (h : Heap) (i b : Nat) (flush : Int32) (v : Ctl × Bool × UInt32) (H : Heap) : Prop :=
  match v.1 with
  | .cont => SLC h i b H ∧ CK b H ∧ v.2.2.toNat < 4
  | .brk => SLC h i b H ∧ CK b H ∧ (∀ st, H.dstate b = some st → st.lookahead = 0) ∧ avIn H i = 0
  | .ret r => StratPost h (some i) flush r H ∧ CK b H

/-- The measure of the outer loop. -/
def OM (i b : Nat) (v : Ctl × Bool × UInt32) (H : Heap) : Nat :=
  match v.1 with
  | .cont => avIn H i + LaS b H + 1
  | _ => 0

theorem u32_add_toNat {a b : UInt32} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add]; omega

theorem u32_sub_toNat {a b : UInt32} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)

/-- The end of a trip (`if (bflush) FLUSH_BLOCK(s, 0);`), as a statement about any `Sat` of it: from `SLW` of the
state, the chains, `match_len < 4` and a consumed byte. -/
theorem fin_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss ml : UInt32} {bf : Bool} {K : Nat}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.level = 2)
    (W : SLW h i b la ss H) (hH : Held b la ss H) (I : bf = false → SLI h i b la ss H) (Ck : CK b H)
    (hml : ml.toNat < 4) (hK : avIn H i + la.toNat + 1 ≤ K) (hz : bf = true → NZ b H) :
    Sat H (do
      if bf = true then do
        let __do_lift ← FLUSH_BLOCK (some b) (.ref (.heap b) wo) 0
        match __do_lift with
          | some r => pure (Ctl.ret r, bf, ml)
          | none => pure (Ctl.cont, bf, ml)
      else pure (Ctl.cont, bf, ml)) (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) := by
  cases bf with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨H0, z, st, d, rfl, C⟩ := I rfl
    obtain ⟨e1, e2⟩ := hH st (SH_dstate _ _ _ _ _ _)
    subst e1 e2
    refine Sat.pure ⟨⟨sli_slc ⟨H0, z, st, d, rfl, C⟩, Ck, hml⟩, ?_⟩
    simp only [OM, LaS_SH]; omega
  | true =>
    simp only [↓reduceIte]
    refine Sat.bind (Sat.mono (flush0_ok T W hH Ck hw0 hn (hz rfl)) ?_)
    rintro r H4 ⟨hav4, Ck4, hnone, hsome⟩
    cases r with
    | none =>
      obtain ⟨C4, hH4⟩ := hnone rfl
      obtain ⟨z4, st4, -, -, -, hst4, -, -⟩ := C4.1.live
      refine Sat.pure ⟨⟨C4, Ck4, hml⟩, ?_⟩
      simp only [OM, LaS, hst4]; rw [(hH4 st4 hst4).1, hav4]; omega
    | some v =>
      obtain ⟨e, hP⟩ := hsome (by simp)
      obtain rfl := Option.some.inj e
      exact Sat.pure ⟨⟨hP flush, Ck4⟩, by simp only [OM]; omega⟩

/-- **One trip of the outer loop of `deflate_fast`.** -/
theorem trip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {mi ml : UInt32} (bf : Bool)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.level = 2)
    (hl : ∀ st0, h.dstate b = some st0 → st0.level = 2 ∧ HASHLESS st0.level st0.strategy = false)
    (hmi : 2 ≤ mi.toNat) (C : SLC h i b H) (Ck : CK b H) (hml : ml.toNat < 4) :
    Sat H (deflate_fast_trip (some b) flush (.ref (.heap b) wo) mi bf ml) (fun v H2 =>
      OI h i b flush v H2 ∧ OM i b v H2 < avIn H i + LaS b H + 1) := by
  obtain ⟨z, st, -, hz, hb, hst, -, -⟩ := C.1.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have eH := ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd
  rw [← eH] at C Ck ⊢
  generalize hK : avIn (SH H i z b st d) i + LaS b (SH H i z b st d) = K
  unfold deflate_fast_trip
  extract_lets bf0 ml0 lc0 jpF ml00 jpZ jpM jpS
  -- the end of the trip
  have hF : ∀ (bfl : Bool) (ml' : UInt32) (H2 : Heap) (la ss : UInt32), SLW h i b la ss H2 → Held b la ss H2 →
      (bfl = false → SLI h i b la ss H2) → CK b H2 → ml'.toNat < 4 → avIn H2 i + la.toNat + 1 ≤ K →
      (bfl = true → NZ b H2) → Sat H2 (jpF () bfl ml') (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) :=
    fun bfl ml' H2 la ss W hH I Ck hml hK hz => fin_ok T hw0 hn W hH I Ck hml hK hz
  have hZ : ∀ (bfl : Bool) (H2 : Heap) (la ss : UInt32), SLW h i b la ss H2 → Held b la ss H2 →
      (bfl = false → SLI h i b la ss H2) → CK b H2 → avIn H2 i + la.toNat + 1 ≤ K → (bfl = true → NZ b H2) →
      Sat H2 (jpZ () bfl) (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) :=
    fun bfl H2 la ss W hH I Ck hK hz => hF bfl 0 H2 la ss W hH I Ck (by decide) hK hz
  -- the tally of a literal or of a match
  have hM : ∀ (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8) (S : Nat → Prop)
      (ml' : UInt32) (lc : UInt8) (st1 : DeflateState) (d1 : Array UInt8),
      ChainOk b d st → st.level = 2 →
      SLI h i b st.lookahead st.strstart (SH H0 i z b st1 d1) →
      Held b st.lookahead st.strstart (SH H0 i z b st1 d1) →
      CG b st d S (SH H0 i z b st1 d1) → (∀ q, S q → q ≤ st.strstart.toNat) →
      (4 ≤ ml'.toNat → ml'.toNat ≤ st.lookahead.toNat ∧ ml'.toNat ≤ 258 ∧
        st1.match_start.toNat < st.strstart.toNat ∧
        st.strstart.toNat ≤ st1.match_start.toNat + (MAX_DIST st).toNat) →
      1 ≤ st.lookahead.toNat → z.avail_in.toNat + st.lookahead.toNat ≤ K →
      Sat (SH H0 i z b st1 d1) (jpM () ml' lc) (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) := by
    intro H0 z st d S ml' lc st1 d1 C0 hlev I1 hH1 G1 hS hmlf hla1 hK1
    obtain ⟨po, ho, L, hpw, w1, w2, hlook, h65, hwp, hbig⟩ := slw_layw (sli_slw I1) hw0
    have hCF := cg_cf G1
    have hw5 : st.w_size = st1.w_size := hCF.2.2.2.2.symm
    have hmd := DeflateFastChain.maxDist_toNat st (by rw [hw5]; exact w1)
    have hw5' : st.w_size.toNat = st1.w_size.toNat := by rw [hw5]
    have hle1 := sli_symle I1
    have hss1 := (hH1 st1 (SH_dstate _ _ _ _ _ _)).2
    have hla1' := (hH1 st1 (SH_dstate _ _ _ _ _ _)).1
    simp -zeta only [jpM]
    by_cases hm4 : ml' ≥ WANT_MIN_MATCH
    · simp -zeta only [hm4, ↓reduceIte]
      have hm4' : 4 ≤ ml'.toNat := by
        have := UInt32.le_iff_toNat_le.mp hm4; simpa [WANT_MIN_MATCH] using this
      obtain ⟨hmla, hm258, hms1, hms2⟩ := hmlf hm4'
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      extract_lets cd
      have hcd : cd.toNat = st.strstart.toNat - st1.match_start.toNat := by
        simp only [cd]; rw [hss1]; exact u32_sub_toNat (by omega)
      have hsub : (ml' - STD_MIN_MATCH).toNat = ml'.toNat - 3 := u32_sub_toNat (by simp [STD_MIN_MATCH]; omega)
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
        (sli_tally_dist_le I1 cd (ml' - STD_MIN_MATCH) ml' (by omega) (by omega) (by omega) (by omega) hm258 hmla)
        (ZlibNgF.Proof.MediumStep.Sat.and
          (tally_dist_K (sli_slw I1) hle1 cd (ml' - STD_MIN_MATCH) (by omega) (by omega) (by omega))
          (sli_tally_dist_nz I1 cd (ml' - STD_MIN_MATCH) (by omega) (by omega) (by omega)))) ?_)
      rintro r H3 ⟨⟨-, W3, -, hle3, I3⟩, ⟨st3, d3, lo, hi, rfl, K3, Wr3, hlo⟩, hz3⟩
      have G3 := cg_tally (sli_slw I1) G1 K3 Wr3 hlo
      extract_lets bfl jpI
      obtain ⟨st4, hst4⟩ : ∃ st4 : DeflateState, st4 = { st3 with lookahead := st3.lookahead - ml' } := ⟨_, rfl⟩
      refine Sat.bind (Sat.of_eq (wrD_eq _ st4 (by rw [hst4])) ?_)
      have k4 : CF st3 st4 ∧ st4.lookahead = st.lookahead - ml' ∧ st4.strstart = st.strstart ∧
          st4.sym_next = st3.sym_next ∧ st4.sym_end = st3.sym_end := by
        rw [hst4]; exact ⟨CF.refl _, by rw [K3.2.2.1, hla1'], K3.2.1.trans hss1, rfl, rfl⟩
      have W4 : SLW h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st4 d3) := slw_wr W3 (by rw [hst4])
      have I4 : bfl = false → SLI h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st4 d3) :=
        fun e => sli_wr (I3 e) (by rw [hst4])
      have hle4 : st4.sym_next ≤ st4.sym_end := by
        rw [k4.2.2.2.1, k4.2.2.2.2]; exact hle3 st3 (SH_dstate _ _ _ _ _ _)
      have G4 := cg_st G3 k4.1
      have hss : (st.strstart + ml').toNat = st.strstart.toNat + ml'.toNat := u32_add_toNat (by omega)
      have hlam : (st.lookahead - ml').toNat = st.lookahead.toNat - ml'.toNat := u32_sub_toNat hmla
      have hcd1 : 1 ≤ cd.toNat := by omega
      have hcd2 : cd.toNat ≤ 32768 := by omega
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      rw [k4.2.1]
      -- after the insertions
      have hI : ∀ (S2 : Nat → Prop) (d5 : Array UInt8),
          SLW h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st4 d5) →
          (bfl = false → SLI h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st4 d5)) →
          CG b st d S2 (SH H0 i z b st4 d5) → (∀ q, S2 q → q < st.strstart.toNat + ml'.toNat) →
          Sat (SH H0 i z b st4 d5) (jpI ()) (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) := by
        intro S2 d5 W5 I5 G5 hS2
        simp -zeta only [jpI]
        obtain ⟨st5, hst5⟩ : ∃ st5 : DeflateState, st5 = { st4 with strstart := st4.strstart + ml' } := ⟨_, rfl⟩
        refine Sat.bind (Sat.of_eq (wrD_eq _ st5 (by rw [hst5])) ?_)
        have k5 : CF st4 st5 ∧ st5.lookahead = st.lookahead - ml' ∧ st5.strstart = st.strstart + ml' ∧
            st5.sym_next = st4.sym_next ∧ st5.sym_end = st4.sym_end := by
          rw [hst5]; exact ⟨CF.refl _, k4.2.1, by rw [k4.2.2.1], rfl, rfl⟩
        have W6 : SLW h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st5 d5) :=
          slw_wr W5 (by rw [hst5])
        have I6 : bfl = false → SLI h i b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st5 d5) :=
          fun e => sli_wr (I5 e) (by rw [hst5])
        have hH6 : Held b (st.lookahead - ml') (st.strstart + ml') (SH H0 i z b st5 d5) := fun st6 h6 => by
          obtain rfl : st6 = st5 := Option.some.inj (h6.symm.trans (SH_dstate _ _ _ _ _ _))
          exact ⟨k5.2.1, k5.2.2.1⟩
        have G6 := cg_st G5 k5.1
        have nz6 : NZ b (SH H0 i z b st5 d5) := nz_SH (by
          rw [k5.2.2.2.1, k4.2.2.2.1]; exact nz_of_SH hz3)
        have Ck6 : CK b (SH H0 i z b st5 d5) := ck_of_cg C0 G6 hlev fun st6 h6 => by
          obtain rfl : st6 = st5 := Option.some.inj (h6.symm.trans (SH_dstate _ _ _ _ _ _))
          rw [k5.2.2.1, hss]
          exact ⟨by omega, fun q hq _ => hS2 q hq⟩
        have hK6 : avIn (SH H0 i z b st5 d5) i + (st.lookahead - ml').toNat + 1 ≤ K := by
          rw [avIn_SH, hlam]; omega
        have hle6 : SymLe b (SH H0 i z b st5 d5) := symle_SH (by rw [k5.2.2.2.1, k5.2.2.2.2]; exact hle4)
        by_cases h258 : (ml' == STD_MAX_MATCH) = true
        · simp -zeta only [h258, ↓reduceIte]
          refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
          rw [k5.2.1]
          by_cases h262 : st.lookahead - ml' ≥ MIN_LOOKAHEAD
          · simp -zeta only [h262, ↓reduceIte]
            have h262' : 262 ≤ (st.lookahead - ml').toNat := by
              have := UInt32.le_iff_toNat_le.mp h262
              simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
            refine Sat.bind (Sat.mono (cloop_ok T (flush := flush) (K := K) hw0 hn hl hmi hcd1 hcd2 W6 hH6 I6
              (fun _ => hle6) h262' (by omega) Ck6 hK6 (fun _ => nz6)) ?_)
            rintro ⟨c, bf2⟩ H7 ⟨hCI, hex⟩
            cases c with
            | cont => cases hex
            | ret r => exact Sat.pure ⟨hCI, by simp [OM]⟩
            | brk =>
              obtain ⟨la2, ss2, W7, hH7, I7, Ck7, hK7, hz7⟩ := hCI
              exact hZ bf2 H7 la2 ss2 W7 hH7 I7 Ck7 hK7 hz7
          · simp -zeta only [h262, ↓reduceIte]
            exact hZ bfl _ _ _ W6 hH6 I6 Ck6 hK6 (fun _ => nz6)
        · simp -zeta only [h258, Bool.false_eq_true, ↓reduceIte]
          exact hZ bfl _ _ _ W6 hH6 I6 Ck6 hK6 (fun _ => nz6)
      obtain ⟨po4, ho4, L4, hp4, w14, -, hlook4, h654, hwp4, -⟩ := slw_layw W4 hw0
      rw [hss, hlam] at hlook4
      by_cases hl4 : st.lookahead - ml' ≥ WANT_MIN_MATCH
      · simp -zeta only [hl4, ↓reduceIte]
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        rw [k4.2.2.1]
        have hl4' : 4 ≤ (st.lookahead - ml').toNat := by
          have := UInt32.le_iff_toNat_le.mp hl4; simpa [WANT_MIN_MATCH] using this
        have hs1 : (st.strstart + 1).toNat = st.strstart.toNat + 1 := u32_add_toNat (by simp; omega)
        have hm1 : (ml' - 1).toNat = ml'.toNat - 1 := u32_sub_toNat (by simp; omega)
        refine Sat.bind (Sat.mono (sl_insert_spread (h := h) L4 hp4 hwp4 w14 (st.strstart + 1) (ml' - 1) mi
          (by omega) hmi (by omega) (by omega)) ?_)
        rintro _ _ ⟨d5, rfl, hW5, hI5, g5⟩
        exact hI _ d5 (hW5 _ _ W4) (fun e => hI5 _ _ (I4 e)) (cg_ins G4 g5) fun q hq => by
          rcases hq with hq | hq
          · have := hS q hq; omega
          · omega
      · simp -zeta only [hl4, ↓reduceIte]
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        rw [k4.2.2.1]
        have e : (st.strstart + 2 - STD_MIN_MATCH + ml').toNat = st.strstart.toNat + ml'.toNat - 1 := by
          simp only [STD_MIN_MATCH, UInt32.toNat_add, UInt32.toNat_sub, UInt32.reduceToNat]; omega
        refine Sat.bind (Sat.mono (sl_insert_knuth (h := h) L4 hp4 hwp4 w14 (st.strstart + 2 - STD_MIN_MATCH + ml')
          (by omega) (by omega)) ?_)
        rintro _ _ ⟨d5, rfl, hW5, hI5, g5⟩
        exact hI _ d5 (hW5 _ _ W4) (fun e => hI5 _ _ (I4 e)) (cg_ins G4 g5) fun q hq => by
          rcases hq with hq | hq
          · have := hS q hq; omega
          · omega
    · simp -zeta only [hm4, ↓reduceIte]
      have hml4 : ml'.toNat < 4 := by
        have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hm4); simpa [WANT_MIN_MATCH] using this
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (sli_tally_lit_le I1 hla1 lc)
        (ZlibNgF.Proof.MediumStep.Sat.and (tally_lit_K (sli_slw I1) hle1 lc) (sli_tally_lit_nz I1 lc))) ?_)
      rintro r H3 ⟨⟨-, W3, -, -, I3⟩, ⟨st3, d3, lo, hi, rfl, K3, Wr3, hlo⟩, hz3⟩
      have G3 := cg_tally (sli_slw I1) G1 K3 Wr3 hlo
      extract_lets bfl
      obtain ⟨st4, hst4⟩ : ∃ st4 : DeflateState, st4 = { st3 with lookahead := st3.lookahead - 1 } := ⟨_, rfl⟩
      refine Sat.bind (Sat.of_eq (wrD_eq _ st4 (by rw [hst4])) ?_)
      obtain ⟨st5, hst5⟩ : ∃ st5 : DeflateState, st5 = { st4 with strstart := st4.strstart + 1 } := ⟨_, rfl⟩
      refine Sat.bind (Sat.of_eq (wrD_eq _ st5 (by rw [hst5])) ?_)
      have k5 : CF st3 st5 ∧ st5.lookahead = st.lookahead - 1 ∧ st5.strstart = st.strstart + 1 := by
        rw [hst5, hst4]; exact ⟨CF.refl _, by rw [K3.2.2.1, hla1'], by rw [K3.2.1, hss1]⟩
      have W5 : SLW h i b (st.lookahead - 1) (st.strstart + 1) (SH H0 i z b st5 d3) :=
        slw_wr W3 (by rw [hst5, hst4])
      have I5 : bfl = false → SLI h i b (st.lookahead - 1) (st.strstart + 1) (SH H0 i z b st5 d3) :=
        fun e => sli_wr (I3 e) (by rw [hst5, hst4])
      have hH5 : Held b (st.lookahead - 1) (st.strstart + 1) (SH H0 i z b st5 d3) := fun st6 h6 => by
        obtain rfl : st6 = st5 := Option.some.inj (h6.symm.trans (SH_dstate _ _ _ _ _ _))
        exact ⟨k5.2.1, k5.2.2⟩
      have hss : (st.strstart + 1).toNat = st.strstart.toNat + 1 := u32_add_toNat (by simp; omega)
      have hla5 : (st.lookahead - 1).toNat = st.lookahead.toNat - 1 := u32_sub_toNat (by simp; omega)
      have Ck5 : CK b (SH H0 i z b st5 d3) := ck_of_cg C0 (cg_st G3 k5.1) hlev fun st6 h6 => by
        obtain rfl : st6 = st5 := Option.some.inj (h6.symm.trans (SH_dstate _ _ _ _ _ _))
        rw [k5.2.2, hss]
        exact ⟨by omega, fun q hq _ => by have := hS q hq; omega⟩
      exact hF bfl ml' _ _ _ W5 hH5 I5 Ck5 hml4 (by rw [avIn_SH, hla5]; omega)
        (fun _ => nz_SH (by have := nz_of_SH hz3; rw [hst5, hst4]; exact this))
  -- the insertion of `strstart` and the match search
  have hS : ∀ (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8),
      SLI h i b st.lookahead st.strstart (SH H0 i z b st d) → CK b (SH H0 i z b st d) → 1 ≤ st.lookahead.toNat →
      z.avail_in.toNat + st.lookahead.toNat ≤ K →
      Sat (SH H0 i z b st d) (jpS ()) (fun v H2 => OI h i b flush v H2 ∧ OM i b v H2 < K + 1) := by
    intro H0 z st d I0 Ck0 hla0 hK0
    have C0 : ChainOk b d st := Ck0 st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
    have hlev := slf_lev (sli_slc I0).1 hl st (SH_dstate _ _ _ _ _ _)
    obtain ⟨po, ho, L, hp, w1, w2, hlook, h65, hwp, hbig⟩ := slw_layw (sli_slw I0) hw0
    simp -zeta only [jpS]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    by_cases h4 : st.lookahead ≥ WANT_MIN_MATCH
    · simp -zeta only [h4, ↓reduceIte]
      have h4' : 4 ≤ st.lookahead.toNat := by
        have := UInt32.le_iff_toNat_le.mp h4; simpa [WANT_MIN_MATCH] using this
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine ZlibNgF.Proof.InsertSafe.winRead4 st.strstart.toNat (by omega) fun v => ?_
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
        (DeflateFastChain.insert_knuth_val_V L hp st.strstart v)
        (sli_insert_knuth_val I0 st.strstart v (by omega))) ?_)
      rintro r _ ⟨⟨d1, rfl, hsz, hr, hk⟩, d1', e1, I1, g1⟩
      obtain ⟨-, -, rfl⟩ := SH_inj e1
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      extract_lets dist lc
      refine Sat.bind (Sat.of_eq ldDState_SH ?_)
      have G1 := cg_ins (cg_start (H0 := H0) (i := i) (z := z) (b := b) (st := st) (d := d) (fun _ => False)) g1
      have hS1 : ∀ q, (False ∨ q = st.strstart.toNat) → q ≤ st.strstart.toNat := fun q hq => by
        rcases hq with hq | hq
        · exact hq.elim
        · omega
      by_cases hc : (decide (dist ≤ ↑(MAX_DIST st).toNat) && decide (dist > 0) && r != 0) = true
      · simp -zeta only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
        simp only [dist] at hc1 hc2
        have hr0 : r.toNat ≠ 0 := fun e => hc3 (UInt32.toNat_inj.mp (by rw [e]; rfl))
        obtain ⟨I, ho', po', hh', hp', c1, c2, c3⟩ := C0 (by rw [hlev.1]; decide) hlev.2
        rw [chainLim_2 hlev.1] at c1
        have e2 := L.head; rw [hh'] at e2
        obtain rfl : ho' = ho := by injection e2 with e; injection e
        have e3 := L.prev; rw [hp'] at e3
        obtain rfl : po' = po := by injection e3 with e; injection e
        have CS : ChainSet d ho' po' st.w_size.toNat st.strstart.toNat st.strstart.toNat I := ⟨c1, c2, c3⟩
        have N : ZlibNgF.Proof.LongestMatch.LN d1 wo po' ho' st :=
          ⟨w1, w2, by omega, by omega, by omega, by omega, by have := L.pw; omega, by have := L.hd; omega⟩
        refine Sat.bind (Sat.mono (DeflateFastChain.fast_search CS hp w1 L.win L.prev N hk hr hr0 (by omega)) ?_)
        rintro m _ ⟨ms, rfl, hm⟩
        refine hM H0 z st d _ m lc { st with match_start := ms } d1 C0 hlev.1 (ZlibNgF.Proof.MediumStep.sli_match_start I1 ms)
          (fun st6 h6 => by
            obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h6); exact ⟨rfl, rfl⟩)
          (cg_st G1 ⟨rfl, rfl, rfl, rfl, rfl⟩) hS1 (fun h4 => ?_) hla0 hK0
        rcases hm with hm | hm
        · omega
        · exact hm
      · simp -zeta only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hM H0 z st d _ ml0 lc st d1 C0 hlev.1 I1 held_SH G1 hS1 (fun h4 => by simp only [ml0] at h4; omega)
          hla0 hK0
    · simp -zeta only [h4, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
        (off := wo) (st.strstart.toNat : Int) (by omega) (by simp; omega)
      refine Sat.bind (Sat.of_eq ec ?_)
      exact hM H0 z st d (fun _ => False) ml0 c st d C0 hlev.1 I0 held_SH (cg_start _) (fun q hq => hq.elim)
        (fun h4 => by simp only [ml0] at h4; omega) hla0 hK0
  -- `fill_window` and the start of the trip
  have I0 : SLI h i b st.lookahead st.strstart (SH H i z b st d) := ⟨H, z, st, d, rfl, by rw [FS_self]; exact C⟩
  have hK0 : z.avail_in.toNat + st.lookahead.toNat = K := by rw [← hK, avIn_SH, LaS_SH]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  by_cases hla : st.lookahead < MIN_LOOKAHEAD
  · simp -zeta only [hla, ↓reduceIte]
    have hla' : st.lookahead.toNat < 262 := by
      have := UInt32.lt_iff_toNat_lt.mp hla; simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
    obtain ⟨_, H1, e1, hfill⟩ := sli_fill I0 hla'
    rw [wrD_eq _ st rfl] at e1
    obtain rfl : SH H i z b st d = H1 := by injection e1 with e; injection e
    obtain ⟨u, H2, e2, ⟨H0', z', st', d', rfl, I2, hsum, -, hfull⟩⟩ := hfill
    cases u
    have C0 : ChainOk b d st := Ck st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
    have Ck2 : CK b (SH H0' i z' b st' d') := by
      obtain ⟨z5, hz5, hb5⟩ := (sli_slc I2).1.blk
      intro st5 d5 h5 hd5
      exact ZlibNgF.Proof.FillFacts.fill_window_chain _ _ (some i) b st d C.1.inv
        ⟨i, z, rfl, SH_streams _ _ _ _ _ _, hb, SH_dstate _ _ _ _ _ _⟩ (SH_bytes _ _ _ _ _ _) (dinput_of C.1)
        (fun _ => C.1.crc) hla' C0 e2 st5 d5 ⟨i, z5, rfl, hz5, hb5, h5⟩ hd5
    refine Sat.bind (Sat.of_eq e2 ?_)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    rw [avIn_SH] at hsum
    by_cases hx : (decide (st'.lookahead < MIN_LOOKAHEAD) && flush == Z_NO_FLUSH) = true
    · simp -zeta only [hx, ↓reduceIte]
      have hf : flush = Z_NO_FLUSH := by simp at hx; exact hx.2
      subst hf
      have hx2 : st'.lookahead.toNat < 262 := by
        simp at hx; have hx' : st'.lookahead < 262 := by simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using hx
        exact UInt32.lt_iff_toNat_lt.mp hx'
      exact Sat.pure ⟨⟨slc_post_l (sli_slc I2) hn (cf_fill hfull hx2), Ck2⟩, by simp only [OM]; omega⟩
    · simp -zeta only [hx, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      by_cases hz0 : (st'.lookahead == 0) = true
      · simp -zeta only [hz0, ↓reduceIte]
        refine Sat.pure ⟨⟨sli_slc I2, Ck2, fun st5 h5 => ?_,
          avIn_fill hfull (by rw [show st'.lookahead = 0 by simpa using hz0]; decide)⟩, by simp only [OM]; omega⟩
        obtain rfl : st5 = st' := Option.some.inj (h5.symm.trans (SH_dstate _ _ _ _ _ _))
        simpa using hz0
      · simp -zeta only [hz0, Bool.false_eq_true, ↓reduceIte]
        have : st'.lookahead.toNat ≠ 0 := fun e => hz0 (by simp [UInt32.toNat_inj.mp (by rw [e]; rfl : st'.lookahead.toNat = (0 : UInt32).toNat)])
        exact hS H0' z' st' d' I2 Ck2 (by omega) (by omega)
  · simp -zeta only [hla, ↓reduceIte]
    have hla' : 262 ≤ st.lookahead.toNat := by
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hla); simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
    exact hS H z st d I0 Ck (by omega) (by omega)

end ZlibNgF.Proof.FastTrip
