import ZlibNgF.Proof.«deflate_medium.c.cont»

/-!
# One trip of the loop of `deflate_medium` (`ZlibNgF`)

The loop state is `OI`: between trips `MG` (the frame with no pending bytes and room for a symbol, and the hash
chains), `w_size` fixed (so `max_dist = MAX_DIST(s)` of the entry state), and the carried `next_match` of
`deflate_medium_fizzle` (`NI`): used only with at least `MIN_LOOKAHEAD` bytes of lookahead (else `fill_window` runs and
clears it), it starts at `strstart`, has length 1, or 4..258 at a distance 1..32768, and `orgstart` at most its end.
The measure `OM` is `260 * (2 * avail_in + lookahead)` plus a term that drops when the fizzle `continue` lengthens the
carried match (`nm`). `fill_window` does not raise `2 * avail_in + lookahead` and lowers it when the lookahead
changes; an emission lowers the lookahead by its length.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateMedium

/-- A match that starts at `ss`: length 1, or 4..258 at a distance 1..32768; `orgstart` at most its end. -/
def NxtOk (ss : Nat) (m : Match) : Prop :=
  m.strstart.toNat = ss ∧ m.orgstart.toNat ≤ ss + m.match_length.toNat ∧ m.match_length.toNat ≤ 258 ∧
    (m.match_length = 1 ∨
      (4 ≤ m.match_length.toNat ∧ m.match_start.toNat < ss ∧ ss ≤ m.match_start.toNat + 32768))

/-- The carried `next_match`, when it is used. -/
def NI (b : Nat) (n : Match) (H : Heap) : Prop :=
  ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat → 0 < n.match_length.toNat → NxtOk st.strstart.toNat n

/-- `w_size` of block `b`'s state. -/
def WS (b : Nat) (W : UInt32) (H : Heap) : Prop := ∀ st, H.dstate b = some st → st.w_size = W

/-- The state of the outer loop. -/
def OI (h : Heap) (i b : Nat) (W : UInt32) (flush : Int32) (fz : Bool) (v : Ctl × Match × Match) (H : Heap) :
    Prop :=
  match v.1 with
  | .cont => MG h i b H ∧ WS b W H ∧ NI b v.2.2 H ∧ (fz = false → v.2.2.match_length = 0)
  | .brk => MG h i b H ∧ (∀ st, H.dstate b = some st → st.lookahead = 0) ∧ avIn H i = 0 ∧ flush ≠ Z_NO_FLUSH
  | .ret r => StratPost h (some i) flush r H ∧ ChainAll b H

/-- The part of the measure from the carried match. -/
def nm (m : Match) : Nat := if 0 < m.match_length.toNat then 258 - m.match_length.toNat else 259

theorem nm_le (m : Match) : nm m ≤ 259 := by unfold nm; split <;> omega

/-- The measure of the outer loop. -/
def OM (i b : Nat) (v : Ctl × Match × Match) (H : Heap) : Nat :=
  match v.1 with
  | .cont => 260 * (2 * avIn H i + laOf b H) + nm v.2.2 + 1
  | _ => 0

/-- An insertion that keeps the state and grows the chains below `strstart + lookahead` keeps `MG`. -/
theorem mg_ins {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    (G : MG h i b (SH H0 i z b st d)) (hl : MedLv h b) (F' : SLF h i b (SH H0 i z b st d'))
    {S : Nat → Prop} (g : ZlibNgF.Proof.InsertLoop.GrowSt b st d d' S)
    (hS : ∀ q, S q → q ≠ 0 → q < st.strstart.toNat + st.lookahead.toNat) : MG h i b (SH H0 i z b st d') :=
  mg_of_pf (pe_ins (pe_of_mg G (SH_dstate _ _ _ _ _ _)) hl F' g hS).1

theorem sat_ite {α : Type} {H : Heap} {c : Prop} [Decidable c] {a e : M α} {Q : α → Heap → Prop}
    (ha : c → Sat H a Q) (he : ¬ c → Sat H e Q) : Sat H (if c then a else e) Q := by
  by_cases hc : c
  · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)]; exact ha hc
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]; exact he hc

theorem pf_om {h H : Heap} {i b A : Nat} {W : UInt32} {bf : Bool} (P : PF h i b W A bf H) :
    2 * avIn H i + laOf b H ≤ A ∧ WS b W H := by
  obtain ⟨H0, z, st, d, rfl, -, -, -, -, -, hA, hW⟩ := P
  refine ⟨by rw [laOf_SH]; exact hA, fun st2 h2 => ?_⟩
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact hW

open ZlibNgF.Proof.Tally (W4) in
/-- `pe_tally_lit` with the length `L = 1` as a variable. -/
theorem pe_tally_litL {h H0 : Heap} {i b A : Nat} {W : UInt32} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    {bf : Bool} (P : PE h i b W A bf (SH H0 i z b st d)) (hl : MedLv h b) (L : UInt32) (hL1 : L = 1)
    (hL : 1 ≤ st.lookahead.toNat) (c : UInt8) :
    Sat (SH H0 i z b { st with lookahead := st.lookahead - L } d) (zng_tr_tally_lit (some b) c) (fun r H2 => ∃ st2 d2,
      H2 = SH H0 i z b st2 d2 ∧ st2.lookahead = st.lookahead - L ∧ st2.strstart = st.strstart ∧
      PF h i b W (A - L.toNat) (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + L } d2) ∧
      (bf = false → SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + L } d2))) := by
  subst hL1; exact pe_tally_lit P hl hL c

/-- `MAX_DIST` in numbers. -/
theorem maxDist_toNat' (st : DeflateState) (hw : 512 ≤ st.w_size.toNat) :
    (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
  unfold MAX_DIST MIN_LOOKAHEAD STD_MAX_MATCH STD_MIN_MATCH
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; rfl

open ZlibNgF.Proof.MediumFind in
/-- A match found by `find_best_match` is a carried match at its start. -/
theorem findOk_nxt {ss la md : Nat} {m : Match} (hf : FindOk ss la md m) (hmd : md ≤ 32768) : NxtOk ss m := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  refine ⟨h1, by omega, ?_, ?_⟩
  · rcases h4 with e | ⟨-, h5, -⟩
    · rw [e]; decide
    · exact h5
  · rcases h4 with e | ⟨h5, -, -, h6, h7⟩
    · exact Or.inl e
    · exact Or.inr ⟨h5, h6, by omega⟩

open ZlibNgF.Proof.MediumFind in
/-- A found match moved back by `k` (`fizzle_matches`) is a carried match at its new start. -/
theorem fiz_nxt {ss la md k : Nat} {m n : Match} (hf : FindOk ss la md m) (hmd : md ≤ 32768) (h4 : 4 ≤ m.match_length.toNat)
    (hss : ss ≤ 65536 + 258) (hk : k ≤ m.match_start.toNat)
    (e1 : n.match_start.toNat = m.match_start.toNat - k) (e2 : n.strstart.toNat = m.strstart.toNat - k)
    (e3 : n.match_length.toNat = m.match_length.toNat + k) (e4 : n.orgstart = m.orgstart + 1)
    (e5 : n.match_length.toNat ≤ 258) : NxtOk (ss - k) n := by
  obtain ⟨h1, h2, h3, h4'⟩ := hf
  have ho : n.orgstart.toNat = m.orgstart.toNat + 1 := by
    rw [e4, UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
  rcases h4' with e | ⟨-, -, -, h6, h7⟩
  · rw [e] at h4; exact absurd h4 (by decide)
  refine ⟨by omega, by omega, e5, Or.inr ⟨by omega, by omega, by omega⟩⟩

/-- `StratPost` for `need_more` after a call without a flush, at the levels of `deflate_medium*`. -/
theorem slc_postM {h H : Heap} {i b : Nat} (C : SLC h i b H) (hl : MedLv h b) (hc : CF H i) :
    StratPost h (some i) Z_NO_FLUSH .need_more H := by
  refine slf_postM C.1 _ _ hl (exitIO_nmNF hc) fun st2 h2 => ⟨(C.2 st2 h2).2, ?_, ?_, ?_, ?_⟩
  · intro e; rcases e with e | e <;> cases e
  · intro e; exact absurd rfl e
  · intro e; rcases e with e | e <;> cases e
  · intro e; cases e

open ZlibNgF.Proof.MediumFind in
/-- The facts of a found match that the emission uses. -/
theorem findOk_cur {ss la md : Nat} {m : Match} (hf : FindOk ss la md m) (hmd : md ≤ 32768) (hla : 1 ≤ la) :
    m.strstart.toNat = ss ∧ 1 ≤ m.match_length.toNat ∧ m.match_length.toNat ≤ la ∧
      m.orgstart.toNat ≤ ss + m.match_length.toNat ∧ m.match_length.toNat ≤ 258 ∧
      (m.match_length = 1 ∨ (4 ≤ m.match_length.toNat ∧ m.match_start.toNat < ss ∧
        ss ≤ m.match_start.toNat + 32768)) ∧
      (m.match_length = 1 ∨ (4 ≤ m.match_length.toNat ∧ m.match_length.toNat ≤ 258 ∧ m.match_start.toNat < ss ∧
        ss ≤ m.match_start.toNat + 32768)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  rcases h4 with e | ⟨h5, h6, h7, h8, h9⟩
  · have : m.match_length.toNat = 1 := by rw [e]; rfl
    exact ⟨h1, by omega, by omega, by omega, by omega, Or.inl e, Or.inl e⟩
  · exact ⟨h1, by omega, h7, by omega, h6, Or.inr ⟨h5, h8, by omega⟩, Or.inr ⟨h5, h6, h8, by omega⟩⟩

theorem u32_eq_of_toNat {x y : UInt32} (h : x.toNat = y.toNat) : x = y := UInt32.toNat_inj.mp h

set_option maxHeartbeats 4000000 in
/-- One trip of the outer loop. -/
theorem trip_ok (T : TreesFacts) (fz : Bool) {h H : Heap} {i b wo : Nat} {W : UInt32} (flush : Int32)
    (mic : UInt32) (md : Int32) (hl : MedLv h b) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258)
    (hW1 : 512 ≤ W.toNat) (hW2 : W.toNat ≤ 32768) (hmd : md.toInt = ((W.toNat - 262 : Nat) : Int))
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (cur nxt : Match) (I : OI h i b W flush fz (Ctl.cont, cur, nxt) H) :
    Sat H (deflate_medium_trip fz (some b) flush (.ref (.heap b) wo) mic md cur nxt)
      (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < OM i b (Ctl.cont, cur, nxt) H) := by
  generalize hμ : OM i b (Ctl.cont, cur, nxt) H = μ0
  unfold deflate_medium_trip
  extract_lets cur0 nxt0 bf0 cml0 jE jR jC jS nz
  have hE : ∀ (c n : Match) (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8),
      MG h i b (SH H0 i z b st d) → st.w_size = W →
      c.strstart = st.strstart → 1 ≤ c.match_length.toNat → c.match_length.toNat ≤ st.lookahead.toNat →
      (c.match_length = 1 ∨ (4 ≤ c.match_length.toNat ∧ c.match_length.toNat ≤ 258 ∧
        c.match_start.toNat < st.strstart.toNat ∧ st.strstart.toNat ≤ c.match_start.toNat + 32768)) →
      (262 ≤ st.lookahead.toNat - c.match_length.toNat → 0 < n.match_length.toNat →
        NxtOk (st.strstart.toNat + c.match_length.toNat) n) →
      (c.match_length = STD_MAX_MATCH → n.match_length = 0) →
      (fz = false → n.match_length = 0) →
      260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + 1 ≤ μ0 →
      Sat (SH H0 i z b st d) (jE () c n c.match_length)
        (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
    intro c n H0 z st d G hW hcs hL1 hLa hLk hN h258 hfz hμ1
    have P := pe_of_mg G (SH_dstate _ _ _ _ _ _)
    rw [hW, avIn_SH] at P
    obtain ⟨F, -, -, -, -, -, -, -⟩ := pe_st P
    obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
    have hwin : st.window = .val (.ref (.heap b) wo) := by
      obtain ⟨st0, h0, hw⟩ := F.win
      exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
    obtain rfl : wo' = wo := by
      have := Ly.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
    simp -zeta only [jE]
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    extract_lets j1 jF cd jT
    have hA0 : 1 ≤ 2 * z.avail_in.toNat + st.lookahead.toNat := by omega
    have hF : ∀ (bf : Bool) (H3 : Heap),
        PF h i b W (2 * z.avail_in.toNat + st.lookahead.toNat - c.match_length.toNat) bf H3 →
        (∀ st3, H3.dstate b = some st3 → 262 ≤ st3.lookahead.toNat → 0 < n.match_length.toNat →
          NxtOk st3.strstart.toNat n) →
        Sat H3 (jF () bf) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
      intro bf H3 PF3 hN3
      simp -zeta only [jF]
      cases bf with
      | true =>
        simp only [ite_true]
        refine Sat.bind (Sat.mono (pf_flush T PF3 flush hw0 hl) ?_)
        rintro r2 H4 ⟨hnone, hsome⟩
        cases r2 with
        | some r' =>
          obtain ⟨rfl, SP, Ch4⟩ := hsome _ rfl
          exact Sat.pure ⟨⟨SP, Ch4⟩, by simp only [OM]; omega⟩
        | none =>
          obtain ⟨P4, hk4⟩ := hnone rfl
          obtain ⟨hm4, hw4⟩ := pf_om P4.1
          refine Sat.pure ⟨⟨mg_of_pf P4.1, hw4, fun st4 h4 hla hml => ?_, hfz⟩, ?_⟩
          · obtain ⟨st3, h3, e1, e2⟩ := hk4 st4 h4
            rw [e2]; exact hN3 st3 h3 (by rw [← e1]; exact hla) hml
          · simp only [OM]; have := nm_le n; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨hm3, hw3⟩ := pf_om PF3
        exact Sat.pure ⟨⟨mg_of_pf PF3, hw3, hN3, hfz⟩, by simp only [OM]; have := nm_le n; omega⟩
    have hT : ∀ (r : Bool) (st2 : DeflateState) (d2 : Array UInt8), st2.lookahead = st.lookahead - c.match_length →
        st2.strstart = st.strstart →
        PF h i b W (2 * z.avail_in.toNat + st.lookahead.toNat - c.match_length.toNat) r
          (SH H0 i z b { st2 with strstart := st2.strstart + c.match_length } d2) →
        SymLe b (SH H0 i z b { st2 with strstart := st2.strstart + c.match_length } d2) →
        Sat (SH H0 i z b st2 d2) (jT () r) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
      intro r st2 d2 hla2 hss2 PF2 hsl2
      have hLa' : (st.lookahead - c.match_length).toNat = st.lookahead.toNat - c.match_length.toNat :=
        u32_sub_toNat _ _ hLa
      have hss' : (st2.strstart + c.match_length).toNat = st.strstart.toNat + c.match_length.toNat := by
        rw [hss2]; exact u32_add_toNat _ _ (by omega)
      simp -zeta only [jT]
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine sat_ite (fun h258' => ?_) (fun _ => hF r _ PF2 fun st3 h3 hla hml => ?_)
      · have e258 : c.match_length = STD_MAX_MATCH := by simpa using h258'
        have hn0 := h258 e258
        have hL258 : c.match_length.toNat = 258 := by rw [e258]; rfl
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        have hcn : ∀ st3, (SH H0 i z b { st2 with strstart := st2.strstart + c.match_length } d2).dstate b = some st3 →
            262 ≤ st3.lookahead.toNat → 0 < n.match_length.toNat → NxtOk st3.strstart.toNat n :=
          fun _ _ _ hml => absurd hn0 (by intro e; rw [e] at hml; exact absurd hml (by decide))
        refine sat_ite (fun hge => ?_) (fun _ => hF r _ PF2 hcn)
        obtain hd | ⟨-, -, hd1, hd2⟩ := hLk
        · rw [hd] at hL258; exact absurd hL258 (by decide)
        have hge' : 262 ≤ st2.lookahead.toNat := UInt32.le_iff_toNat_le.mp hge
        have hdist : (c.strstart - c.match_start).toNat = st.strstart.toNat - c.match_start.toNat := by
          rw [hcs]; exact u32_sub_toNat _ _ (by omega)
        refine Sat.bind (Sat.mono (cont_loop_ok T flush mic (c.strstart - c.match_start) r hl hm2 hm3
          (by omega) (by omega) hw0 ⟨PF2, hsl2⟩ fun st3 h3 => ?_) ?_)
        · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h3)
          exact ⟨hge', by show _ ≤ (st2.strstart + c.match_length).toNat; omega⟩
        rintro ⟨c2, bf2⟩ H4 ⟨hCI, hne⟩
        cases c2 with
        | cont => exact absurd rfl hne
        | brk => exact hF bf2 H4 hCI.1 fun _ _ _ hml => absurd hn0 (by intro e; rw [e] at hml; exact absurd hml (by decide))
        | ret r' => exact Sat.pure ⟨hCI, by simp only [OM]; omega⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h3)
        show NxtOk (st2.strstart + c.match_length).toNat n
        rw [hss']
        have h2 : st2.lookahead.toNat = st.lookahead.toNat - c.match_length.toNat := by rw [hla2, hLa']
        have hla' : 262 ≤ st2.lookahead.toNat := hla
        exact hN (by omega) hml
    refine sat_ite (fun hL1' => ?_) (fun hL1' => ?_)
    · have e1 : c.match_length = 1 := by simpa using hL1'
      obtain ⟨v, ev⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b)
        (st := { st with lookahead := st.lookahead - c.match_length }) (d := d) (off := wo')
        (c.strstart.toNat : Int) (by omega) (by rw [hcs]; simp; omega)
      refine Sat.bind (Sat.of_eq ev (Sat.bind (Sat.mono (pe_tally_litL P hl c.match_length e1 (by omega) v) ?_)))
      rintro r _ ⟨st2, d2, rfl, hla2, hss2, PF2, hsl2⟩
      exact hT r st2 d2 hla2 hss2 PF2 (hsl2 rfl)
    · have hn1 : c.match_length ≠ 1 := fun e => hL1' (by simp [e])
      obtain hd | ⟨h4, h258', hd1, hd2⟩ := hLk
      · exact absurd hd hn1
      have hlen : (c.match_length - STD_MIN_MATCH).toNat < 256 := by
        rw [u32_sub_toNat _ _ (by simp [STD_MIN_MATCH]; omega)]; simp [STD_MIN_MATCH]; omega
      have hdist : (c.strstart - c.match_start).toNat = st.strstart.toNat - c.match_start.toNat := by
        rw [hcs]; exact u32_sub_toNat _ _ (by omega)
      refine Sat.bind (Sat.mono (pe_tally_dist P hl (c.strstart - c.match_start) (c.match_length - STD_MIN_MATCH)
        c.match_length hlen (by omega) (by omega) hL1 h258' hLa) ?_)
      rintro r _ ⟨st2, d2, rfl, hla2, hss2, PF2, hsl2⟩
      exact hT r st2 d2 hla2 hss2 PF2 (hsl2 rfl)
  have hC : ∀ (c n : Match) (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8),
      fz = true → MG h i b (SH H0 i z b st d) → st.w_size = W →
      c.strstart = st.strstart → 1 ≤ c.match_length.toNat → c.match_length.toNat ≤ st.lookahead.toNat →
      c.orgstart.toNat ≤ st.strstart.toNat + c.match_length.toNat → c.match_length.toNat ≤ 258 →
      (c.match_length = 1 ∨ (4 ≤ c.match_length.toNat ∧
        c.match_start.toNat < st.strstart.toNat ∧ st.strstart.toNat ≤ c.match_start.toNat + 32768)) →
      n.match_length = 0 →
      260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + 1 ≤ μ0 →
      (262 ≤ st.lookahead.toNat →
        260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + (258 - c.match_length.toNat) + 1 ≤ μ0) →
      Sat (SH H0 i z b st d) (jC () c n) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
    intro c n H0 z st d hfz1 G hW hcs hL1 hLa hor hL2 hLk hn0 hμ1 hμ2
    simp -zeta only [jC]
    extract_lets L nz2 tmp jA
    have eL : L = c.match_length := rfl
    clear_value L
    subst eL
    have hz2 : nz2.match_length = 0 := rfl
    have hz2' : nz2 = { n with match_length := 0 } := rfl
    clear_value nz2
    have P := pe_of_mg G (SH_dstate _ _ _ _ _ _)
    obtain ⟨F, -, -, -, -, -, -, -⟩ := pe_st P
    obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
    have hwin : st.window = .val (.ref (.heap b) wo) := by
      obtain ⟨st0, h0, hw⟩ := F.win
      exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
    obtain rfl : wo' = wo := by
      have := Ly.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
    have hEz : ∀ d', MG h i b (SH H0 i z b st d') →
        Sat (SH H0 i z b st d') (jE () c nz2 c.match_length)
          (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := fun d' G' =>
      hE c nz2 H0 z st d' G' hW hcs hL1 hLa
        (by rcases hLk with e | ⟨h4, h5, h6⟩; exact Or.inl e; exact Or.inr ⟨h4, hL2, h5, h6⟩)
        (fun _ hml => by rw [hz2] at hml; exact absurd hml (by decide)) (fun _ => hz2) (fun _ => hz2) hμ1
    have hA : ∀ d', MG h i b (SH H0 i z b st d') →
        Sat (SH H0 i z b st d') (jA ()) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
      intro d' G'
      simp -zeta only [jA]
      refine sat_ite (fun _ => hEz d' G') (fun h258 => ?_)
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine sat_ite (fun hc12 => ?_) (fun _ => hEz d' G')
      have hgt : 262 < st.lookahead.toNat := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc12
        exact UInt32.lt_iff_toNat_lt.mp hc12.1
      have hL258 : c.match_length.toNat ≠ 258 := fun e => h258 (by
        have : c.match_length = STD_MAX_MATCH := UInt32.toNat_inj.mp (by rw [e]; rfl)
        simp [this])
      have hsL : (c.strstart + c.match_length).toNat = st.strstart.toNat + c.match_length.toNat := by
        rw [hcs]; exact u32_add_toNat _ _ (by omega)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      have I0 := sli_of_slc G'.1 (SH_dstate _ _ _ _ _ _)
      have Im : SLI h i b st.lookahead st.strstart
          (SH H0 i z b { st with strstart := c.strstart + c.match_length } d') := sli_congr I0 rfl
      obtain ⟨wom, pom, hom, Lym, -, -, -, -, -, -, hbigm, -, -⟩ := ZlibNgF.Proof.MediumStep.sli_lay Im
      obtain rfl : wom = wo' := by
        have := Lym.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
        (ZlibNgF.Proof.InsertLoop.sli_insert_knuth Im hwin (c.strstart + c.match_length)
          (by show (c.strstart + c.match_length).toNat + 4 ≤ st.window_size.toNat; omega) (by omega))
        (ZlibNgF.Proof.MediumStep.insert_knuth_res Lym (c.strstart + c.match_length) (by have := hsL; omega))) ?_)
      rintro hh _ ⟨⟨d'', rfl, I2, g2⟩, hh6⟩
      have hmd' : md.toInt = (MAX_DIST { st with strstart := c.strstart + c.match_length }).toNat := by
        rw [maxDist_toNat' _ (by show 512 ≤ st.w_size.toNat; omega)]
        show _ = ((st.w_size.toNat - 262 : Nat) : Int); rw [hW]; exact hmd
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.sli_find I2 hh md hh6 hmd'
        (by show (c.strstart + c.match_length).toNat ≤ 65536; omega) (by show st.lookahead.toNat ≤ 65536; omega)
        (by show (c.strstart + c.match_length).toNat + st.lookahead.toNat ≤ 65536 + 512; omega)) ?_)
      rintro n2 _ ⟨ms, rfl, I3, hf2⟩
      have hf2' : ZlibNgF.Proof.MediumFind.FindOk (st.strstart.toNat + c.match_length.toNat) st.lookahead.toNat
          (W.toNat - 262) n2 := by
        have := hf2; rw [maxDist_toNat' _ (by show 512 ≤ st.w_size.toNat; omega)] at this
        rw [← hsL]; exact (show st.w_size = W from hW) ▸ this
      obtain ⟨wo3, po3, ho3, Ly3, -, -, -, -, -, -, hbig3, -, -⟩ := ZlibNgF.Proof.MediumStep.sli_lay I3
      obtain rfl : wo3 = wom := by
        have := Ly3.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
      have Ch0 : ChainOk b d' st := G'.2 st d' (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
      have hcl0 := slf_lv G'.1.1 hl (SH_dstate _ _ _ _ _ _)
      have hR : ∀ c' n' : Match, c'.strstart = c.strstart →
          (c'.match_length = 0 → 0 < n'.match_length.toNat ∧ NxtOk st.strstart.toNat n' ∧
            258 - n'.match_length.toNat < 258 - c.match_length.toNat) →
          (c'.match_length ≠ 0 → (c'.match_length = 1 ∨ c' = c) ∧
            (262 ≤ st.lookahead.toNat - c'.match_length.toNat → 0 < n'.match_length.toNat →
              NxtOk (st.strstart.toNat + c'.match_length.toNat) n')) →
          Sat (SH H0 i z b { { st with strstart := c.strstart + c.match_length } with match_start := ms } d'')
            (jR () c' n' c'.match_length) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
        intro c' n' hcs' hz0 hnz
        simp -zeta only [jR]
        refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
        have hcs2 : c'.strstart = st.strstart := hcs'.trans hcs
        have Ir : SLI h i b st.lookahead st.strstart (SH H0 i z b { { { st with strstart := c.strstart + c.match_length }
            with match_start := ms } with strstart := c'.strstart } d'') := sli_congr I3 rfl
        have Ir' : SLI h i b st.lookahead c'.strstart (SH H0 i z b { { { st with strstart := c.strstart + c.match_length }
            with match_start := ms } with strstart := c'.strstart } d'') := hcs2 ▸ Ir
        have Cr := sli_slc Ir'
        have Chr : ChainOk b d'' { { { st with strstart := c.strstart + c.match_length }
            with match_start := ms } with strstart := c'.strstart } :=
          ZlibNgF.Proof.InsertGrow.ChainOk.grow Ch0 (g2 : ZlibNgF.Proof.InsertLoop.GrowSt b st d' d'' _) rfl rfl rfl rfl rfl
            (by show _ ≤ c'.strstart.toNat; rw [hcs2]; exact Nat.le_refl _)
            (by simp only [chainLim]; rw [hcs2]; exact Nat.le_refl _)
            (fun q hq _ => by
              have e := slf_lv Cr.1 hl (SH_dstate _ _ _ _ _ _)
              rw [e]; show q < c'.strstart.toNat + st.lookahead.toNat; rw [hcs2]; rw [hq]; omega)
        have Gr : MG h i b (SH H0 i z b { { { st with strstart := c.strstart + c.match_length }
            with match_start := ms } with strstart := c'.strstart } d'') := ⟨Cr, chainAll_SH.mpr Chr⟩
        refine sat_ite (fun h0 => ?_) (fun h0 => ?_)
        · have e0 : c'.match_length = 0 := by simpa using h0
          obtain ⟨hp0, hN0, hlt0⟩ := hz0 e0
          refine Sat.pure ⟨⟨Gr, fun st4 h4 => ?_, fun st4 h4 _ _ => ?_, fun e => absurd hfz1 (by rw [e]; decide)⟩, ?_⟩
          · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h4); exact hW
          · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h4)
            show NxtOk c'.strstart.toNat n'; rw [hcs2]; exact hN0
          · simp only [OM, nm, laOf_SH, avIn_SH, hp0, ↓reduceIte]
            have := hμ2 (by omega)
            show 260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + (258 - n'.match_length.toNat) + 1 < μ0
            omega
        · have e0 : c'.match_length ≠ 0 := fun e => h0 (by simp [e])
          obtain ⟨hc1, hN1⟩ := hnz e0
          have hc'L : c'.match_length.toNat ≤ c.match_length.toNat ∧ 1 ≤ c'.match_length.toNat := by
            rcases hc1 with e | e
            · rw [e]; exact ⟨hL1, Nat.le_refl _⟩
            · rw [e]; exact ⟨Nat.le_refl _, hL1⟩
          refine hE c' n' H0 z _ d'' Gr hW (by rfl) hc'L.2 (by show _ ≤ st.lookahead.toNat; omega) ?_ ?_ ?_
            (fun e => absurd hfz1 (by rw [e]; decide)) hμ1
          · show c'.match_length = 1 ∨ (4 ≤ c'.match_length.toNat ∧ c'.match_length.toNat ≤ 258 ∧
              c'.match_start.toNat < c'.strstart.toNat ∧ c'.strstart.toNat ≤ c'.match_start.toNat + 32768)
            rw [hcs2]
            rcases hc1 with e | e
            · exact Or.inl e
            · subst e; rcases hLk with e | ⟨h4, h5, h6⟩
              · exact Or.inl e
              · exact Or.inr ⟨h4, hL2, h5, h6⟩
          · show 262 ≤ st.lookahead.toNat - c'.match_length.toNat → 0 < n'.match_length.toNat →
              NxtOk (c'.strstart.toNat + c'.match_length.toNat) n'
            rw [hcs2]; exact hN1
          · intro e; exfalso
            have : c'.match_length.toNat = 258 := by rw [e]; rfl
            omega
      refine sat_ite (fun hg => ?_) (fun hg => ?_)
      · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hg
        obtain ⟨⟨hg1, hg2⟩, hg3⟩ := hg
        have hg1' : 2 ≤ c.match_length.toNat := by
          rcases Nat.lt_or_ge c.match_length.toNat 2 with h2 | h2
          · exfalso; apply hg1
            show c.match_length - 1 = 0
            have e : c.match_length = 1 := UInt32.toNat_inj.mp (by simp; omega)
            rw [e]; rfl
          · exact h2
        have hg3' : c.match_length.toNat - 1 ≤ n2.match_start.toNat := by
          have := UInt32.le_iff_toNat_le.mp hg3; rwa [u32_sub_toNat _ _ (by simp; omega)] at this
        have hg2' : 4 ≤ n2.match_length.toNat := UInt32.le_iff_toNat_le.mp hg2
        obtain ⟨hf1, hf2a, hf3, hf4⟩ := hf2'
        have hn4 : n2.match_length.toNat ≤ 258 ∧ n2.match_start.toNat < n2.strstart.toNat := by
          rcases hf4 with e | ⟨-, h5, -, h6, -⟩
          · rw [e] at hg2'; exact absurd hg2' (by decide)
          · exact ⟨h5, by omega⟩
        refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumFizzle.fizzle_ok (r := .heap b) (a := d'')
          (by rw [ZlibNgF.Proof.InflateAlloc.space_get_heap]; exact SH_bytes _ _ _ _ _ _) c n2 md
          (by rw [hmd]; omega) (by rw [hmd]; omega) hg1' hL2 hg3' hn4.2 (by omega) hn4.1 (by omega)) ?_)
        rintro cn _ ⟨rfl, hfo⟩
        rcases hfo with ⟨hc', hn'⟩ | ⟨k, hk, ec, ecl, hkm, e1, e2, e3, e4, e5⟩
        · obtain ⟨c', n'⟩ := cn
          simp only at hc' hn'
          subst hc' hn'
          exact hR c' n' rfl (fun e => absurd e (by intro e'; rw [e'] at hL1; exact absurd hL1 (by decide)))
            fun _ => ⟨Or.inr rfl, fun _ _ => findOk_nxt ⟨hf1, hf2a, hf3, hf4⟩ (by omega)⟩
        · have hfk := fiz_nxt (ss := st.strstart.toNat + c.match_length.toNat) (la := st.lookahead.toNat)
            (md := W.toNat - 262) (k := k) ⟨hf1, hf2a, hf3, hf4⟩ (by omega) hg2' (by omega) hkm e1 e2 e3 e4 e5
          have hcs3 : cn.1.strstart = c.strstart := by have := congrArg Match.strstart ec; exact this
          show Sat _ (jR () cn.1 cn.2 cn.1.match_length) _
          refine hR cn.1 cn.2 hcs3 (fun e0 => ⟨by omega, ?_, by omega⟩) (fun e0 => ⟨?_, fun _ _ => ?_⟩)
          · rw [e0] at ecl; simp at ecl
            have : k = c.match_length.toNat := by omega
            rw [this] at hfk; simpa using hfk
          · left; apply UInt32.toNat_inj.mp; rw [ecl]
            have : cn.1.match_length.toNat ≠ 0 := fun e => e0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
            rw [ecl] at this; simp; omega
          · have : cn.1.match_length.toNat ≠ 0 := fun e => e0 (UInt32.toNat_inj.mp (by rw [e]; rfl))
            have hk1 : k + 1 = c.match_length.toNat := by omega
            have : st.strstart.toNat + c.match_length.toNat - k = st.strstart.toNat + cn.1.match_length.toNat := by
              omega
            rw [← this]; exact hfk
      · exact hR c n2 rfl (fun e => absurd e (by intro e'; rw [e'] at hL1; exact absurd hL1 (by decide)))
          fun _ => ⟨Or.inr rfl, fun _ _ => findOk_nxt hf2' (by omega)⟩
    refine sat_ite (fun h4 => ?_) (fun _ => hA d G)
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine sat_ite (fun hgt => ?_) (fun _ => hA d G)
    have h4' : 4 ≤ c.match_length.toNat := UInt32.le_iff_toNat_le.mp h4
    have hgt' : c.match_length.toNat + 4 < st.lookahead.toNat := by
      have := UInt32.lt_iff_toNat_lt.mp hgt
      rw [UInt32.toNat_add] at this; simp [WANT_MIN_MATCH] at this; omega
    refine Sat.bind (Sat.mono (slf_insert_match F hwin c mic hm2 hm3 (by omega) (by rw [hcs]; exact hor)
      (by rw [hcs]; omega) (by rw [hcs]; omega)) ?_)
    rintro _ _ ⟨d', rfl, F', g⟩
    exact hA d' (mg_ins G hl F' g fun q hq _ => by rw [hcs] at hq; omega)
  -- `insert_knuth` at `strstart` (with at least `WANT_MIN_MATCH` bytes) and `find_best_match`
  have hIF : ∀ (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8), MG h i b (SH H0 i z b st d) →
      st.w_size = W → 4 ≤ st.lookahead.toNat →
      Sat (SH H0 i z b st d) (ZlibNg.InsertStringP.insert_knuth (some b) (.ref (.heap b) wo) st.strstart)
        (fun hh H' => ∃ d', H' = SH H0 i z b st d' ∧ MG h i b H' ∧ hh.toNat < 65536) := by
    intro H0 z st d G hW h4
    have P := pe_of_mg G (SH_dstate _ _ _ _ _ _)
    obtain ⟨F, -, -, -, -, -, -, -⟩ := pe_st P
    obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
    have hwin : st.window = .val (.ref (.heap b) wo) := by
      obtain ⟨st0, h0, hw⟩ := F.win
      exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
    obtain rfl : wo' = wo := by
      have := Ly.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
    refine Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (slf_insert_knuth F hwin st.strstart (by omega) (by omega))
      (ZlibNgF.Proof.MediumStep.insert_knuth_res Ly st.strstart (by omega))) ?_
    rintro hh _ ⟨⟨d', rfl, F', g⟩, hh6⟩
    exact ⟨d', rfl, mg_ins G hl F' g (fun q hq _ => by rw [hq]; omega), hh6⟩
  have hFB : ∀ (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8) (hh : UInt32),
      MG h i b (SH H0 i z b st d) → st.w_size = W → hh.toNat < 65536 →
      Sat (SH H0 i z b st d) (find_best_match (some b) hh md) (fun m H' => ∃ ms, H' =
        SH H0 i z b { st with match_start := ms } d ∧ MG h i b H' ∧
        ZlibNgF.Proof.MediumFind.FindOk st.strstart.toNat st.lookahead.toNat (W.toNat - 262) m) := by
    intro H0 z st d hh G hW hh6
    have I0 := sli_of_slc G.1 (SH_dstate _ _ _ _ _ _)
    obtain ⟨-, -, -, -, -, w1, w2, hlook, h65, -, -, -, -⟩ := ZlibNgF.Proof.MediumStep.sli_lay I0
    have hmd' : md.toInt = (MAX_DIST st).toNat := by
      rw [maxDist_toNat' _ (by omega), hW]; exact hmd
    refine Sat.mono (ZlibNgF.Proof.MediumStep.sli_find I0 hh md hh6 hmd' (by omega) (by omega) (by omega)) ?_
    rintro m _ ⟨ms, rfl, I1, hf⟩
    refine ⟨ms, rfl, ⟨sli_slc I1, chainAll_SH.mpr ?_⟩, ?_⟩
    · exact chain_adv (G.2 st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)) rfl rfl rfl rfl rfl (Nat.le_refl _)
        (by simp only [chainLim]; exact Nat.le_refl _)
    · rw [maxDist_toNat' _ (by omega), hW] at hf; exact hf
  have hS : ∀ (n : Match) (H0 : Heap) (z : ZStream) (st : DeflateState) (d : Array UInt8),
      MG h i b (SH H0 i z b st d) → st.w_size = W → 1 ≤ st.lookahead.toNat →
      (0 < n.match_length.toNat → 262 ≤ st.lookahead.toNat ∧ NxtOk st.strstart.toNat n) →
      (fz = false → n.match_length = 0) →
      260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + 1 ≤ μ0 →
      (262 ≤ st.lookahead.toNat → 260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + nm n + 1 ≤ μ0) →
      Sat (SH H0 i z b st d) (jS () n) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
    intro n H0 z st d G hW hla1 hN hfz hμ1 hμ2
    simp -zeta only [jS]
    have hWn : W.toNat - 262 ≤ 32768 := by omega
    refine sat_ite (fun hfz1 => ?_) (fun hfz1 => ?_)
    · refine sat_ite (fun hp => ?_) (fun hp => ?_)
      · have hp' : 0 < n.match_length.toNat := UInt32.lt_iff_toNat_lt.mp hp
        obtain ⟨h262, hn1, hn2, hn3, hn4⟩ := hN hp'
        refine hC n _ H0 z st d hfz1 G hW (u32_eq_of_toNat hn1) hp' (by omega) hn2 hn3 hn4 rfl hμ1 fun h => ?_
        have := hμ2 h; simp only [nm, hp', ↓reduceIte] at this; omega
      · have hn0 : n.match_length = 0 := by
          have := UInt32.not_lt.mp hp; exact u32_eq_of_toNat (by have := UInt32.le_iff_toNat_le.mp this; simp at this ⊢; omega)
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        extract_lets jH
        have hJ : ∀ (hh : UInt32) (d' : Array UInt8), MG h i b (SH H0 i z b st d') → hh.toNat < 65536 →
            Sat (SH H0 i z b st d') (jH () hh) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
          intro hh d' G' hh6
          simp -zeta only [jH]
          refine Sat.bind (Sat.mono (hFB H0 z st d' hh G' hW hh6) ?_)
          rintro m _ ⟨ms, rfl, G2, hf⟩
          obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := findOk_cur hf hWn hla1
          refine hC m n H0 z _ d' hfz1 G2 hW (u32_eq_of_toNat c1) c2 c3 c4 c5 c6 hn0 hμ1 fun h => ?_
          have h' : 262 ≤ st.lookahead.toNat := h
          have hnm : nm n = 259 := by simp [nm, hn0]
          have := hμ2 h'
          show 260 * (2 * z.avail_in.toNat + st.lookahead.toNat) + (258 - m.match_length.toNat) + 1 ≤ μ0
          omega
        refine sat_ite (fun h4 => ?_) (fun _ => hJ 0 d G (by decide))
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        refine Sat.bind (Sat.mono (hIF H0 z st d G hW (UInt32.le_iff_toNat_le.mp h4)) ?_)
        rintro hh _ ⟨d', rfl, G', hh6⟩
        exact hJ hh d' G' hh6
    · have hfz0 : fz = false := by simpa using hfz1
      have hn0 := hfz hfz0
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      extract_lets jH
      have hJ : ∀ (hh : UInt32) (d' : Array UInt8), MG h i b (SH H0 i z b st d') → hh.toNat < 65536 →
          Sat (SH H0 i z b st d') (jH () hh) (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
        intro hh d' G' hh6
        simp -zeta only [jH]
        refine Sat.bind (Sat.mono (hFB H0 z st d' hh G' hW hh6) ?_)
        rintro m _ ⟨ms, rfl, G2, hf⟩
        obtain ⟨c1, c2, c3, c4, c5, -, c7⟩ := findOk_cur hf hWn hla1
        have hE' : ∀ d'', MG h i b (SH H0 i z b { st with match_start := ms } d'') →
            Sat (SH H0 i z b { st with match_start := ms } d'') (jE () m n m.match_length)
              (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := fun d'' G3 =>
          hE m n H0 z _ d'' G3 hW (u32_eq_of_toNat c1) c2 c3 c7
            (fun _ hml => by rw [hn0] at hml; exact absurd hml (by decide)) (fun _ => hn0) (fun _ => hn0) hμ1
        refine sat_ite (fun h4 => ?_) (fun _ => hE' d' G2)
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        refine sat_ite (fun hgt => ?_) (fun _ => hE' d' G2)
        have h4' : 4 ≤ m.match_length.toNat := UInt32.le_iff_toNat_le.mp h4
        have hgt' : m.match_length.toNat + 4 < st.lookahead.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp hgt
          rw [UInt32.toNat_add] at this; simp [WANT_MIN_MATCH] at this; omega
        have P := pe_of_mg G2 (SH_dstate _ _ _ _ _ _)
        obtain ⟨F, -, -, -, -, -, -, -⟩ := pe_st P
        obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
        have hwin : st.window = .val (.ref (.heap b) wo) := by
          obtain ⟨st0, h0, hw⟩ := F.win
          exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
        obtain rfl : wo' = wo := by
          have := Ly.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
        have hlook' : st.strstart.toNat + st.lookahead.toNat ≤ st.window_size.toNat := hlook
        have h65' : st.window_size.toNat ≤ 65536 := h65
        refine Sat.bind (Sat.mono (slf_insert_match F hwin m mic hm2 hm3 (by omega) (by rw [c1]; exact c4)
          (by rw [c1]; omega) (by rw [c1]; show _ ≤ st.window_size.toNat; omega)) ?_)
        rintro _ _ ⟨d'', rfl, F', g⟩
        exact hE' d'' (mg_ins G2 hl F' g fun q hq _ => by rw [c1] at hq; show q < st.strstart.toNat + st.lookahead.toNat; omega)
      refine sat_ite (fun h4 => ?_) (fun _ => hJ 0 d G (by decide))
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.mono (hIF H0 z st d G hW (UInt32.le_iff_toNat_le.mp h4)) ?_)
      rintro hh _ ⟨d', rfl, G', hh6⟩
      exact hJ hh d' G' hh6
  obtain ⟨G, hWS, hNI, hfzn⟩ := I
  obtain ⟨z, st, d, eH, hst⟩ := slf_sh G.1.1
  have hWst : st.w_size = W := hWS st hst
  rw [eH] at G hμ ⊢
  simp only [OM, avIn_SH, laOf_SH] at hμ
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine sat_ite (fun hlt => ?_) (fun hlt => ?_)
  · have hlt' : st.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp hlt
    refine Sat.bind (Sat.mono (mg_fill G (SH_dstate _ _ _ _ _ _) hlt') ?_)
    rintro _ _ ⟨H1, z1, st1, d1, rfl, G1, hsum, hne, hws1, hfull⟩
    rw [avIn_SH, avIn_SH] at hsum hne
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine sat_ite (fun hnm => ?_) (fun hnm => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hnm
      obtain ⟨hlt1, rfl⟩ := hnm
      have hlt1' : st1.lookahead.toNat < 262 := by
        have := UInt32.lt_iff_toNat_lt.mp hlt1; simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
      exact Sat.pure ⟨⟨slc_postM G1.1 hl (cf_fill hfull hlt1'), G1.2⟩, by simp only [OM]; omega⟩
    · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine sat_ite (fun h0 => ?_) (fun h0 => ?_)
      · refine Sat.pure ⟨⟨G1, fun st2 h2 => ?_,
          avIn_fill hfull (by rw [show st1.lookahead = 0 by simpa using h0]; decide), fun hf => hnm ?_⟩,
          by simp only [OM]; omega⟩
        · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
          simpa using h0
        · rw [show st1.lookahead = 0 by simpa using h0, hf]; decide
      · have h1 : 1 ≤ st1.lookahead.toNat := by
          have : st1.lookahead ≠ 0 := fun e => h0 (by simp [e])
          have h2 : st1.lookahead.toNat ≠ 0 := fun e => this (UInt32.toNat_inj.mp (by rw [e]; rfl))
          omega
        have hW1' : st1.w_size = W := hws1.trans hWst
        have hA : 2 * z1.avail_in.toNat + st1.lookahead.toNat ≤ 2 * z.avail_in.toNat + st.lookahead.toNat := by
          by_cases e : st1.lookahead = st.lookahead
          · rw [e] at hsum ⊢; omega
          · have := hne e; omega
        have hA2 : 262 ≤ st1.lookahead.toNat →
            2 * z1.avail_in.toNat + st1.lookahead.toNat + 1 ≤ 2 * z.avail_in.toNat + st.lookahead.toNat := by
          intro h
          have e : st1.lookahead ≠ st.lookahead := fun e => by rw [e] at h; omega
          have := hne e; omega
        have hz : ∀ n : Match, n.match_length = 0 → Sat (SH H1 i z1 b st1 d1) (jS () n)
            (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := fun n hn =>
          hS n H1 z1 st1 d1 G1 hW1' h1 (fun hp => by rw [hn] at hp; exact absurd hp (by decide))
            (fun _ => hn) (by have := nm_le nxt; omega) (fun h => by have := hA2 h; have := nm_le n; omega)
        refine sat_ite (fun _ => hz _ rfl) (fun hf => hz _ (hfzn (by simpa using hf)))
  · have hge : 262 ≤ st.lookahead.toNat := by have := UInt32.not_lt.mp hlt; exact UInt32.le_iff_toNat_le.mp this
    refine hS nxt _ z st d G hWst (by omega) (fun hp => ⟨hge, hNI st hst hge hp⟩) hfzn
      (by have := nm_le nxt; omega) (fun _ => by omega)

end ZlibNgF.Proof.MediumLoop
