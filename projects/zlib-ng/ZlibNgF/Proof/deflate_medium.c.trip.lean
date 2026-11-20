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
  | .brk => MG h i b H ∧ ∀ st, H.dstate b = some st → st.lookahead = 0
  | .ret r => StratPost h (some i) flush r H ∧ ChainAll b H

/-- The part of the measure from the carried match. -/
def nm (m : Match) : Nat := if 0 < m.match_length.toNat then 258 - m.match_length.toNat else 259

theorem nm_le (m : Match) : nm m ≤ 259 := by unfold nm; split <;> omega

/-- The measure of the outer loop. -/
def OM (i b : Nat) (v : Ctl × Match × Match) (H : Heap) : Nat :=
  match v.1 with
  | .cont => 260 * (2 * avIn H i + laOf b H) + nm v.2.2
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
  obtain ⟨H0, z, st, d, rfl, -, -, -, -, hA, hW⟩ := P
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
      260 * (2 * z.avail_in.toNat + st.lookahead.toNat) ≤ μ0 →
      Sat (SH H0 i z b st d) (jE () c n c.match_length)
        (fun v H2 => OI h i b W flush fz v H2 ∧ OM i b v H2 < μ0) := by
    intro c n H0 z st d G hW hcs hL1 hLa hLk hN h258 hfz hμ1
    have P := pe_of_mg G (SH_dstate _ _ _ _ _ _)
    rw [hW, avIn_SH] at P
    obtain ⟨F, -, -, -, -, -, -⟩ := pe_st P
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
  sorry

end ZlibNgF.Proof.MediumLoop
