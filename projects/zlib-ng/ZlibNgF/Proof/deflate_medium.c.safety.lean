import ZlibNgF.Proof.«deflate_medium.c.trip»
import ZlibNgF.ZlibNg.«deflate_medium.c»

/-!
# `deflate_medium` and `deflate_medium_fizzle` (`ZlibNgF`)

`medium_ok` / `medium_fizzle_ok`: the medium strategies keep the strategy frame and the hash chains (`StratOkC`),
given the block emitters (`TreesFacts`). The loop (`trip_ok`) runs from the entry state (`mg_entry`: the frame with
no pending bytes and room for a symbol, at a level of 3..6 with any strategy) until it returns or the lookahead is
empty; then `s->insert` is set and the tail flushes (`tail_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateMedium

/-- The entry of `deflate_medium*` (as `Strategy.sli_entry`, at a level other than 1 with any strategy). -/
theorem mg_entry {h : Heap} {i b : Nat} {z : ZStream} {flush : Int32} (P : StratPre h (some i) flush)
    (hz : h.streams i = some z) (hb : z.state = some b)
    (hE : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.level ≠ 1) :
    ∃ st, h.dstate b = some st ∧ SLC h i b h := by
  obtain ⟨hv, hcrc, hio, hset, -, -, b1, st1, ⟨i1, z1, e1, hz1, hb1, hst1⟩, hp0, hs1⟩ := P
  obtain rfl : i = i1 := Option.some.inj e1
  obtain rfl : z = z1 := Option.some.inj (hz.symm.trans hz1)
  obtain rfl : b = b1 := Option.some.inj (hb.symm.trans hb1)
  have hD : DStateIs h (some i) b st1 := ⟨i, z, rfl, hz, hb, hst1⟩
  obtain ⟨hlv, hl1⟩ := hE b st1 hD
  obtain ⟨hs1, ⟨hsym, -, -, hg2, hg8⟩, -⟩ := hs1
  have hgap : GapOk st1 := ⟨hg2, Int32.not_le.mp fun e8 => hl1 (hg8 e8).1⟩
  refine ⟨st1, hst1, ⟨⟨hv, hio, hset, hcrc, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩, dframe_refl _ _ _ _ _, ?_,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; rfl⟩,
    ⟨st1, hst1, fun st h1 => by rw [hst1] at h1; cases h1; exact StratKeeps.refl _⟩, fun st h1 => ?_⟩,
    fun st h1 => ?_⟩⟩
  · have hio0 := hio
    obtain ⟨z2, b2, hp, ⟨i2, e2, hz2⟩, hb2, -, -, -, hout, hnb, -⟩ := hio0
    obtain rfl : i = i2 := Option.some.inj e2
    obtain rfl : z = z2 := Option.some.inj (hz.symm.trans hz2)
    obtain ⟨z3, ⟨i3, e3, hz3⟩, hnn, -⟩ := hset
    obtain rfl : i = i3 := Option.some.inj e3
    obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
    obtain ⟨ob, oo, ad, hno, -, -⟩ := hout.resolve_left hnn
    exact ⟨z, z, ob, oo, 0, hz, hz, hno, hno, rfl⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hlv, hs1, hgap⟩
  · obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans h1)
    exact ⟨hp0, hsym⟩

set_option maxHeartbeats 4000000 in
/-- `deflate_medium_tpl fizzle` at levels `lo..hi` within 3..6 keeps the strategy frame and the hash chains. -/
theorem medium_tpl_ok (T : TreesFacts) (fz : Bool) (lo hi : Int32) (hlo : 3 ≤ lo) (hhi : hi ≤ 6) :
    StratOkC (TableAt lo hi) (deflate_medium_tpl fz) := by
  intro h s b flush P hsb hE hCh
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hl : MedLv h b := fun st0 h0 => by
    obtain ⟨h1, h2, -, -⟩ := hE b st0 ⟨i, z, rfl, hz, hb, h0⟩
    exact ⟨Int32.le_trans hlo h1, Int32.le_trans h2 hhi⟩
  obtain ⟨st, hst, C0⟩ := mg_entry P hz hb (fun b' st hd => by
    obtain ⟨h1, -, -, -⟩ := hE b' st hd
    have h3 : (3 : Int32) ≤ st.level := Int32.le_trans hlo h1
    exact ⟨Int32.lt_of_lt_of_le (by decide) h3, fun e => absurd (e ▸ h3) (by decide)⟩)
  have Ch0 : ChainAll b h := fun st' d hst' hd => hCh st' d ⟨i, z, rfl, hz, hb, hst'⟩ hd
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨-, wo, -, -, -, -, hwin, -⟩ := c.lay
  simp only [dview] at hwin
  have hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo) := fun st0 h0 => by
    rw [hst] at h0; cases h0; exact hwin
  obtain ⟨w1, w2, -⟩ := c.sizes
  have w1' : 512 ≤ st.w_size.toNat := w1
  have w2' : st.w_size.toNat ≤ 32768 := w2
  suffices S : Sat h (deflate_medium_tpl fz (some b) flush)
      (fun bs h' => StratPost h (some i) flush bs h' ∧ ChainAll b h') by
    obtain ⟨bs, h', e, q1, q2⟩ := S
    refine ⟨bs, h', e, q1, fun st2 d2 hs2 hd2 => ?_⟩
    obtain ⟨i1, z1, e1, hz1, hb1, hst1⟩ := hs2
    exact q2 st2 d2 hst1 hd2
  unfold deflate_medium_tpl
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.of_eq (ldDState_app L.dstate) ?_)
  generalize hmic : (if (if 2 < st.max_lazy_match then st.max_lazy_match else 2) > STD_MAX_MATCH then STD_MAX_MATCH
    else if 2 < st.max_lazy_match then st.max_lazy_match else 2) = mic
  have hmic2 : 2 ≤ mic.toNat ∧ mic.toNat ≤ 258 := by
    rw [← hmic]
    by_cases h1 : 2 < st.max_lazy_match
    · simp only [h1, ite_true]
      by_cases h2 : st.max_lazy_match > STD_MAX_MATCH
      · simp only [h2, ite_true]; decide
      · simp only [h2, ite_false]
        have := UInt32.lt_iff_toNat_lt.mp h1
        have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h2)
        simp [STD_MAX_MATCH] at *; omega
    · simp only [h1, ite_false]; decide
  have hmd : (MAX_DIST st).toInt32.toInt = ((st.w_size.toNat - 262 : Nat) : Int) := by
    rw [← maxDist_toNat' st w1']
    exact ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt _ (by rw [maxDist_toNat' st w1']; omega)
  have I0 : OI h i b st.w_size flush fz (Ctl.cont, { match_start := 0, match_length := 0, strstart := 0, orgstart := 0 },
      { match_start := 0, match_length := 0, strstart := 0, orgstart := 0 }) h :=
    ⟨⟨C0, Ch0⟩, fun st2 h2 => by rw [hst] at h2; cases h2; rfl, fun _ _ _ hml => absurd hml (by decide),
      fun _ => rfl⟩
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (OI h i b st.w_size flush fz) (OM i b)
    (fun v H => OI h i b st.w_size flush fz v H ∧ v.1 ≠ Ctl.cont) ?_ I0 ?_) ?_)
  · rintro ⟨c1, cu, nx⟩ H1 hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, ?_⟩⟩
    · cases c1 with
      | cont =>
        exact trip_ok T fz flush mic _ hl hmic2.1 hmic2.2 w1' w2' hmd hw0 cu nx hI
      | brk => cases hc
      | ret r => cases hc
    · cases c1 with
      | cont => cases hc
      | brk => exact fun e => by cases e
      | ret r => exact fun e => by cases e
  · have h1 := avIn_lt h i
    have h2 : laOf b h < 2 ^ 32 := by
      unfold laOf; split
      · exact UInt32.toNat_lt _
      · decide
    have := nm_le { match_start := 0, match_length := 0, strstart := 0, orgstart := 0 }
    simp only [OM, fuel]; omega
  rintro ⟨c1, cu, nx⟩ H2 ⟨hI, hc⟩
  cases c1 with
  | cont => exact absurd rfl hc
  | ret r => exact Sat.pure hI
  | brk =>
    obtain ⟨G, hla0⟩ := hI
    obtain ⟨z2, st2, d2, eH, hst2⟩ := slf_sh G.1.1
    rw [eH] at G ⊢
    have hl0 := hla0 st2 hst2
    simp only []
    have hv : (if st2.strstart < STD_MIN_MATCH - 1 then st2.strstart else STD_MIN_MATCH - 1) ≤ st2.strstart := by
      split
      · exact UInt32.le_refl _
      · exact UInt32.not_lt.mp ‹_›
    obtain ⟨_, H3, e3, C3, rfl⟩ := slc_insert G.1 _ hv
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have Ch3 : ChainAll b (SH H2 i z2 b { st2 with
        insert := if st2.strstart < STD_MIN_MATCH - 1 then st2.strstart else STD_MIN_MATCH - 1 } d2) :=
      chainAll_SH.mpr (chain_adv (G.2 st2 d2 (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)) rfl rfl rfl rfl rfl
        (Nat.le_refl _) (by simp only [chainLim]; exact Nat.le_refl _))
    have hp : ∀ st, (SH H2 i z2 b { st2 with
        insert := if st2.strstart < STD_MIN_MATCH - 1 then st2.strstart else STD_MIN_MATCH - 1 } d2).dstate b = some st →
        st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := by
      intro st4 h4
      obtain ⟨st0, h0, hw⟩ := C3.1.win
      exact ⟨(C3.2 st4 h4).1, (hw st4 h4).trans (hw0 st0 h0)⟩
    have fl : ∀ (last : Int32) (bs : BlockState), 0 ≤ last → last ≤ 1 → (bs = .block_done ∨ bs = .finish_done) →
        Sat (SH H2 i z2 b { st2 with
          insert := if st2.strstart < STD_MIN_MATCH - 1 then st2.strstart else STD_MIN_MATCH - 1 } d2)
          (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H' =>
            ∀ k : Unit → M BlockState, k () = pure bs →
            Sat H' (match r with | some r => pure r | none => k ()) (fun bs h' =>
              StratPost h (some i) flush bs h' ∧ ChainAll b h')) := by
      intro last bs hl0' hl1 hbs
      refine Sat.mono (slf_flush_mg T last hl0' hl1 C3.1 hp Ch3) ?_
      rintro r H4 ⟨-, F4, Ch4, -, hs4, hn4, hsm⟩ k hk
      have hx : ∀ st5, H4.dstate b = some st5 → st5.sym_next = 0 ∧ st5.sym_next < st5.sym_end ∧
          st5.lookahead = 0 := fun st5 h5 => by
        obtain ⟨e1, e2, st6, h6, e3, -⟩ := hs4 st5 h5
        obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h6)
        exact ⟨e1, e2, by rw [e3]; exact hl0⟩
      cases r with
      | none =>
        rw [hk]
        exact Sat.pure ⟨slf_postM F4 _ _ hl fun st5 h5 =>
          ⟨(hx st5 h5).2.1, fun _ => hn4 rfl st5 h5, fun _ => (hx st5 h5).1,
            fun _ => ⟨(hx st5 h5).1, (hx st5 h5).2.2⟩, fun _ => (hx st5 h5).1⟩, Ch4⟩
      | some v =>
        obtain ⟨rfl⟩ := Option.some.inj (hsm (by simp))
        refine Sat.pure ⟨slf_postM F4 _ _ hl fun st5 h5 => ⟨(hx st5 h5).2.1, fun e => ?_, fun _ => (hx st5 h5).1,
          fun _ => ⟨(hx st5 h5).1, (hx st5 h5).2.2⟩, fun _ => (hx st5 h5).1⟩, Ch4⟩
        split at e <;> rcases e with e | e <;> cases e
    refine sat_ite (fun hf => ?_) (fun hf => ?_)
    · exact Sat.bind (Sat.mono (fl 1 .finish_done (by decide) (by decide) (.inr rfl)) fun r H' q =>
        q (fun _ => pure .finish_done) rfl)
    · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine sat_ite (fun hs => ?_) (fun hs => ?_)
      · exact Sat.bind (Sat.mono (fl 0 .block_done (by decide) (by decide) (.inl rfl)) fun r H' q =>
          q (fun _ => pure .block_done) rfl)
      · have h0 : st2.sym_next = 0 := by simpa using hs
        refine Sat.pure ⟨slf_postM C3.1 _ _ hl fun st5 h5 => ?_, Ch3⟩
        obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h5)
        have := C3.2 _ (SH_dstate _ _ _ _ _ _)
        exact ⟨this.2, fun _ => this.1, fun _ => h0, fun e => (by rcases e with e | e <;> cases e), fun _ => h0⟩

end ZlibNgF.Proof.MediumLoop

namespace ZlibNgF.Proof.MediumLoop
open ZlibNgF.Proof.DeflateFacts

/-- **`deflate_medium` (levels 3-4) keeps the strategy frame and the hash chains** (`StrategyFacts.medium`). -/
theorem medium_ok (T : TreesFacts) : StratOkC (TableAt 3 4) ZlibNg.DeflateMedium.deflate_medium :=
  medium_tpl_ok T false 3 4 (by decide) (by decide)

/-- **`deflate_medium_fizzle` (levels 5-6) keeps the strategy frame and the hash chains**
(`StrategyFacts.medium_fizzle`). -/
theorem medium_fizzle_ok (T : TreesFacts) : StratOkC (TableAt 5 6) ZlibNg.DeflateMedium.deflate_medium_fizzle :=
  medium_tpl_ok T true 5 6 (by decide) (by decide)

end ZlibNgF.Proof.MediumLoop
