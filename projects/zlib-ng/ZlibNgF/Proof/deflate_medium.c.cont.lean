import ZlibNgF.Proof.«deflate_medium.c.emit»

/-!
# The continuation loop of `deflate_medium` (`ZlibNgF`)

After a match of length `STD_MAX_MATCH` at distance `dist`, with at least `MIN_LOOKAHEAD` bytes of lookahead,
`deflate_medium` extends it by runs of at least 8 bytes at the same distance (`deflate_medium_tpl.h:283-319`):
each trip reads at most 258 bytes (`max_match_continues`), inserts `strstart` and the match, tallies it (the first
trip may tally into a full symbol buffer, `PE true`), advances `strstart`, and flushes when `bflush`. The loop stops
when the run is shorter than 8 or the lookahead drops below `MIN_LOOKAHEAD`; its measure is the lookahead.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateMedium

/-- The lookahead of block `b`'s state. -/
def laOf (b : Nat) (H : Heap) : Nat :=
  match H.dstate b with
  | some st => st.lookahead.toNat
  | none => 0

theorem laOf_SH (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    laOf b (SH H0 i z b st d) = st.lookahead.toNat := by
  simp only [laOf, SH_dstate]

/-- The state of the continuation loop. -/
def CI (h : Heap) (i b A : Nat) (flush : Int32) (dist : UInt32) (x : Ctl × Bool) (H : Heap) : Prop :=
  match x.1 with
  | .cont => PE h i b A x.2 H ∧
      ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat ∧ dist.toNat ≤ st.strstart.toNat
  | .brk => PE h i b A x.2 H
  | .ret r => StratPost h (some i) flush r H ∧ ChainAll b H

/-- The measure of the continuation loop. -/
def CM (b : Nat) (x : Ctl × Bool) (H : Heap) : Nat :=
  match x.1 with
  | .cont => laOf b H + 1
  | _ => 0

theorem u32_add_toNat (x y : UInt32) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem u32_sub_toNat (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)

theorem pe_mono {h H : Heap} {i b A A' : Nat} {bf : Bool} (P : PE h i b A bf H) (hA : A ≤ A') : PE h i b A' bf H :=
  ⟨pf_mono P.1 hA, P.2⟩

/-- One trip of the continuation loop. -/
theorem cont_trip_ok (T : TreesFacts) {h H : Heap} {i b A wo : Nat} (flush : Int32) (mic dist : UInt32)
    (bf : Bool) (hl : MedLv h b) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (P : PE h i b A bf H)
    (hc : ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat ∧ dist.toNat ≤ st.strstart.toNat) :
    Sat H (deflate_medium_cont_trip (some b) (.ref (.heap b) wo) mic dist bf) (fun x H2 =>
      CI h i b A flush dist x H2 ∧ CM b x H2 < laOf b H + 1) := by
  have P0 := P
  obtain ⟨⟨H0, z, st, d, rfl, -⟩, -⟩ := P0
  obtain ⟨hla, hds⟩ := hc st (SH_dstate _ _ _ _ _ _)
  obtain ⟨F, hp, hle, Ch, hs, hA⟩ := pe_st P
  obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
  have hwin : st.window = .val (.ref (.heap b) wo) := by
    obtain ⟨st0, h0, hw⟩ := F.win
    exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
  obtain rfl : wo' = wo := by have := Ly.win; rw [hwin] at this; injection this with e; injection e with _ e2; exact e2.symm
  rw [laOf_SH]
  unfold deflate_medium_cont_trip
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumFizzle.max_match_continues_ok (r := .heap b) (a := d)
    (by rw [ZlibNgF.Proof.InflateAlloc.space_get_heap]; exact SH_bytes _ _ _ _ _ _) st.strstart dist hds
    (by omega)) ?_)
  rintro cl _ ⟨rfl, hcl⟩
  by_cases h8 : cl < 8
  · simp only [h8, ↓reduceIte]
    exact Sat.pure ⟨P, by simp [CM]⟩
  simp only [h8, ↓reduceIte]
  have h8' : 8 ≤ cl.toNat := by have := UInt32.not_lt.mp h8; exact UInt32.le_iff_toNat_le.mp this
  have hws : st.strstart.toNat + cl.toNat + 4 ≤ st.window_size.toNat := by omega
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumLoop.slf_insert_knuth F hwin st.strstart (by omega) (by omega)) ?_)
  rintro _ _ ⟨d1, rfl, F1, g1⟩
  have P1 := pe_ins P hl F1 g1 (fun q hq _ => by rw [hq]; omega)
  have hss : (st.strstart + cl).toNat = st.strstart.toNat + cl.toNat := u32_add_toNat _ _ (by omega)
  have ho2 : (if dist < cl then st.strstart + cl - dist else st.strstart).toNat ≤ st.strstart.toNat + cl.toNat := by
    split
    · rw [u32_sub_toNat _ _ (by omega), hss]; omega
    · omega
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumLoop.slf_insert_match F1 hwin _ mic hm2 hm3 (by simp only []; omega)
    ho2 (by simp only []; omega) (by simp only []; omega)) ?_)
  rintro _ _ ⟨d2, rfl, F2, g2⟩
  have P2 := pe_ins P1 hl F2 g2 (fun q hq _ => by simp only [] at hq; omega)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hcl3 : (cl - STD_MIN_MATCH).toNat < 256 := by
    rw [u32_sub_toNat _ _ (by simp [STD_MIN_MATCH]; omega)]; simp [STD_MIN_MATCH]; omega
  refine Sat.bind (Sat.mono (pe_tally_dist P2 hl dist (cl - STD_MIN_MATCH) cl hcl3 hd1 hd2 (by omega) hcl (by omega)) ?_)
  rintro r _ ⟨st2, d3, rfl, hla2, hss2, PF3, hsl3⟩
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  have hcl' : cl.toNat ≤ st.lookahead.toNat := by omega
  have hla3 : st2.lookahead.toNat = st.lookahead.toNat - cl.toNat := by rw [hla2, u32_sub_toNat _ _ hcl']
  have hss3 : (st2.strstart + cl).toNat = st.strstart.toNat + cl.toNat := by rw [hss2]; exact hss
  by_cases hb : (bf || r) = true
  · simp only [hb, ite_true]
    refine Sat.bind (Sat.mono (pf_flush T PF3 flush hw0 hn) ?_)
    rintro r2 H4 ⟨hnone, hsome⟩
    cases r2 with
    | some r' =>
      obtain ⟨rfl, SP, Ch4⟩ := hsome _ rfl
      exact Sat.pure ⟨⟨SP, Ch4⟩, by simp [CM]⟩
    | none =>
      obtain ⟨P4, hk4⟩ := hnone rfl
      have P4' := P4
      obtain ⟨⟨H5, z5, st5, d5, rfl, -⟩, -⟩ := P4'
      obtain ⟨st6, h6, hl6, hs6⟩ := hk4 st5 (SH_dstate _ _ _ _ _ _)
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h6)
      have hl7 : st5.lookahead.toNat = st.lookahead.toNat - cl.toNat := by rw [hl6]; exact hla3
      have hs7 : st5.strstart.toNat = st.strstart.toNat + cl.toNat := by rw [hs6]; exact hss3
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      by_cases hlt : st5.lookahead < MIN_LOOKAHEAD
      · simp only [hlt, ite_true]
        exact Sat.pure ⟨pe_mono P4 (by omega), by simp [CM]⟩
      · simp only [hlt, ite_false]
        have hlt' : 262 ≤ st5.lookahead.toNat := by
          have := UInt32.not_lt.mp hlt; exact UInt32.le_iff_toNat_le.mp this
        refine Sat.pure ⟨⟨pe_mono P4 (by omega), fun st7 h7 => ?_⟩, ?_⟩
        · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h7); exact ⟨hlt', by omega⟩
        · simp only [CM, laOf_SH]; omega
  · simp only [hb, Bool.false_eq_true, ite_false]
    have hb' : (bf || r) = false := by simpa using hb
    have hbf : bf = false := by simp only [Bool.or_eq_false_iff] at hb'; exact hb'.1
    have P4 : PE h i b A (bf || r) (SH H0 i z b { st2 with strstart := st2.strstart + cl } d3) :=
      ⟨pf_mono PF3 (by omega), hsl3 hbf⟩
    rw [hb'] at P4
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    by_cases hlt : st2.lookahead < MIN_LOOKAHEAD
    · simp only [hlt, ite_true]
      exact Sat.pure ⟨P4, by simp [CM]⟩
    · simp only [hlt, ite_false]
      have hlt' : 262 ≤ st2.lookahead.toNat := by
        have := UInt32.not_lt.mp hlt; exact UInt32.le_iff_toNat_le.mp this
      refine Sat.pure ⟨⟨P4, fun st7 h7 => ?_⟩, ?_⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h7); exact ⟨hlt', by show _ ≤ (st2.strstart + cl).toNat; omega⟩
      · simp only [CM, laOf_SH]; show st2.lookahead.toNat + 1 < _; omega

/-- The continuation loop from `PE` with at least `MIN_LOOKAHEAD` bytes of lookahead and `dist <= strstart`: it ends
with `break` (`PE`, `A` kept) or a return (`StratPost` and the chains). -/
theorem cont_loop_ok (T : TreesFacts) {h H : Heap} {i b A wo : Nat} (flush : Int32) (mic dist : UInt32)
    (bf : Bool) (hl : MedLv h b) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (P : PE h i b A bf H)
    (hc : ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat ∧ dist.toNat ≤ st.strstart.toNat) :
    Sat H (cwhile (fun (x : Ctl × Bool) => pure (x.1 matches .cont, x))
      (fun (x : Ctl × Bool) => deflate_medium_cont_trip (some b) (.ref (.heap b) wo) mic dist x.2) (Ctl.cont, bf))
      (fun x H2 => CI h i b A flush dist x H2 ∧ x.1 ≠ Ctl.cont) := by
  refine ZlibNgF.Proof.WinInv.sat_cwhileH (CI h i b A flush dist) (CM b)
    (fun x H2 => CI h i b A flush dist x H2 ∧ x.1 ≠ Ctl.cont) ?_ (s := (Ctl.cont, bf)) ⟨P, hc⟩ ?_
  · rintro ⟨c, bf1⟩ H1 hI
    refine Sat.pure ⟨fun hc1 => ?_, fun hc1 => ⟨hI, ?_⟩⟩
    · cases c with
      | cont => exact cont_trip_ok T flush mic dist bf1 hl hm2 hm3 hd1 hd2 hw0 hn hI.1 hI.2
      | brk => cases hc1
      | ret r => cases hc1
    · cases c with
      | cont => cases hc1
      | brk => exact fun e => by cases e
      | ret r => exact fun e => by cases e
  · have : laOf b H < 2 ^ 32 := by
      unfold laOf; split
      · exact UInt32.toNat_lt _
      · decide
    simp only [CM, fuel]; omega

end ZlibNgF.Proof.MediumLoop
