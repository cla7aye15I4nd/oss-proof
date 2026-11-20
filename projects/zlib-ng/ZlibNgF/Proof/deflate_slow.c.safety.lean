import ZlibNgF.Proof.«deflate_slow.c.trip»

/-!
# `deflate_slow` (`ZlibNgF`)

`slow_ok`: the lazy strategy of levels 7-9 keeps the strategy frame and the hash chains (`StratOkC`), given the block
emitters (`TreesFacts`). The loop runs `SlowTrip.trip_ok` until a trip returns or breaks (`lookahead == 0` after a
refill); after the break, a pending literal is tallied (`slowTail_ok`, with no pending match: the lookahead is empty),
`insert` is set and the last block is flushed (`slowEnd_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowSafety
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.SlowFrame ZlibNgF.Proof.SlowStep ZlibNgF.Proof.SlowEmit ZlibNgF.Proof.SlowTrip
open ZlibNg.DeflateP ZlibNg.DeflateSlow

/-- `s->insert = v` with `v <= strstart` keeps `SLF`. -/
theorem slf_insert {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (F : SLF h i b (SH H0 i z b st d)) (v : UInt32) (hv : v ≤ st.strstart) :
    SLF h i b (SH H0 i z b { st with insert := v } d) :=
  slf_SH F (fun _ _ c => DCore.of_heap (by rw [SH_bytes, SH_bytes])
    (dcore_set c st.strstart st.lookahead v st.block_start c.look c.bstart hv c.bs_lo)) rfl rfl rfl rfl
    (F.st st (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _)

/-- `StratPost` at an exit with no symbols, no lookahead, no pending match or literal. -/
theorem exit_ok {h H2 : Heap} {i b wo : Nat} {level : Int32} (E : Env h b wo level) (F2 : SLF h i b H2)
    (flush : Int32) (bs : BlockState)
    (hs : ∀ s2, H2.dstate b = some s2 → s2.sym_next = 0 ∧ s2.sym_next < s2.sym_end ∧ s2.lookahead = 0 ∧
      LazyOk s2 ∧ s2.match_available = 0)
    (hp : bs = .block_done ∨ bs = .finish_done → ∀ s2, H2.dstate b = some s2 → s2.pending = 0) :
    StratPost h (some i) flush bs H2 :=
  slf_postW F2 flush bs (fun st0 h0 => (tab_lv (E.tab st0 h0).1).2.1)
    (fun _ _ _ s2 h2 => ⟨(hs s2 h2).2.2.2.1, fun _ => (hs s2 h2).2.2.2.2⟩)
    (fun s2 h2 => ⟨(hs s2 h2).2.1, fun e => hp e s2 h2, fun _ _ => (hs s2 h2).1,
      fun _ => ⟨(hs s2 h2).1, (hs s2 h2).2.2.1⟩, fun _ => (hs s2 h2).1⟩)

/-- `FLUSH_BLOCK` at the end, with no lookahead and no pending match or literal: the facts of `exit_ok` after, the
hash chains kept, no pending bytes when it does not return, and its return value. -/
theorem end_flush (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sT : DeflateState}
    {dT : Array UInt8} {level : Int32} (E : Env h b wo level) (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b (SH H0 i z b sT dT)) (hp0 : sT.pending = 0) (hla : sT.lookahead = 0)
    (hpl : sT.prev_length < 3) (hma : sT.match_available = 0) (Ch : ChainOk b dT sT) :
    Sat (SH H0 i z b sT dT) (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H2 => SLF h i b H2 ∧
      (∀ s2, H2.dstate b = some s2 → s2.sym_next = 0 ∧ s2.sym_next < s2.sym_end ∧ s2.lookahead = 0 ∧
        LazyOk s2 ∧ s2.match_available = 0) ∧
      (∀ s2 d2, H2.dstate b = some s2 → H2.bytes b = some d2 → ChainOk b d2 s2) ∧
      (r = none → ∀ s2, H2.dstate b = some s2 → s2.pending = 0) ∧
      (r ≠ none → r = some (if last != 0 then .finish_started else .need_more))) := by
  obtain ⟨hwin, hT, -, -⟩ := env_st E F
  have hp : ∀ st, (SH H0 i z b sT dT).dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) :=
    fun st hst => by obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst); exact ⟨hp0, hwin⟩
  obtain ⟨pbo, hpb⟩ : ∃ pbo, sT.pending_buf = .val (.ref (.heap b) pbo) := by
    obtain ⟨-, -, -, pbo, -, -, -, -, hpb, -⟩ := slf_lay F; exact ⟨pbo, hpb⟩
  refine Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (slf_flush T last hl0 hl1 F hp)
    (slf_flush_keep T last hl0 hl1 F hp)) ?_
  rintro r H2 ⟨⟨-, F2, hs2, hn2, hsm⟩, hk2⟩
  obtain ⟨H1, z2, s2, d2, rfl⟩ := slf_sh F2
  obtain ⟨st2, hst2, K, hpb2⟩ := hk2 _ (SH_dstate _ _ _ _ _ _)
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨k1, -, k3, k4, k5, k6, k7, k8, -, k10, k11, -⟩ := fbkeeps_fields K
  obtain ⟨d4, d5, hd4, hd5, -, hq⟩ := hpb2 pbo hpb
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd4)
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd5)
  have C2 : ChainOk b d2 s2 := chain_keep F Ch hT rfl rfl rfl rfl k7 k8 k10 k11 k6
    (by rw [k4]; exact Nat.le_refl _) fun pbo' hpb' j hj => by
      rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e; injection e
      exact hq j (Or.inl hj)
  refine ⟨F2, fun s3 hs3 => ?_, fun s3 d3 hs3 hd3 => ?_, hn2, hsm⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
    obtain ⟨e1, e2, -⟩ := hs2 s2 (SH_dstate _ _ _ _ _ _)
    exact ⟨e1, e2, by rw [k5, hla], LazyOk.of_clear (by rw [k1]; exact hpl) (by rw [k3, hma]),
      by rw [k3, hma]⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
    exact C2

/-- The post of `deflate_slow`: `StratPost` and the hash chains. -/
def SPost (h : Heap) (i b : Nat) (flush : Int32) (bs : BlockState) (H : Heap) : Prop :=
  StratPost h (some i) flush bs H ∧ ∀ st d, H.dstate b = some st → H.bytes b = some d → ChainOk b d st

/-- `slowEnd`: `insert` set, and the last block flushed for `Z_FINISH` or when symbols wait. -/
theorem slowEnd_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sT : DeflateState}
    {dT : Array UInt8} {level : Int32} (E : Env h b wo level) (flush : Int32)
    (F : SLF h i b (SH H0 i z b sT dT)) (hp0 : sT.pending = 0)
    (hla : sT.lookahead = 0) (hpl : sT.prev_length < 3) (hma : sT.match_available = 0) (Ch : ChainOk b dT sT) :
    Sat (SH H0 i z b sT dT) (slowEnd (some b) (.ref (.heap b) wo) flush) (fun bs H2 => SPost h i b flush bs H2) := by
  obtain ⟨-, -, -, -, -, -, -, hse⟩ := slf_nums F
  unfold slowEnd
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sT with
    insert := if sT.strstart < STD_MIN_MATCH - 1 then sT.strstart else STD_MIN_MATCH - 1 }) rfl) ?_)
  have F1 := slf_insert F (if sT.strstart < STD_MIN_MATCH - 1 then sT.strstart else STD_MIN_MATCH - 1) (by
    split
    · exact UInt32.le_refl _
    · rename_i hn; exact UInt32.not_lt.mp hn)
  have Ch1 : ChainOk b dT { sT with
      insert := if sT.strstart < STD_MIN_MATCH - 1 then sT.strstart else STD_MIN_MATCH - 1 } :=
    ZlibNgF.Proof.DeflateSide.ChainOk.of_state Ch rfl rfl rfl rfl rfl rfl rfl
  have fin : ∀ (last : Int32) (bs : BlockState), 0 ≤ last → last ≤ 1 → (r : Option BlockState) → ∀ H2,
      (SLF h i b H2 ∧ (∀ s2, H2.dstate b = some s2 → s2.sym_next = 0 ∧ s2.sym_next < s2.sym_end ∧
        s2.lookahead = 0 ∧ LazyOk s2 ∧ s2.match_available = 0) ∧
        (∀ s2 d2, H2.dstate b = some s2 → H2.bytes b = some d2 → ChainOk b d2 s2) ∧
        (r = none → ∀ s2, H2.dstate b = some s2 → s2.pending = 0) ∧
        (r ≠ none → r = some (if last != 0 then .finish_started else .need_more))) →
      (r = none → SPost h i b flush bs H2) ∧ ∀ v, r = some v → SPost h i b flush v H2 := by
    intro last bs _ _ r H2 ⟨F2, hs2, hc2, hn2, hsm⟩
    refine ⟨fun e => ⟨exit_ok E F2 flush bs hs2 fun _ => hn2 e, hc2⟩, fun v e => ⟨exit_ok E F2 flush v hs2 ?_, hc2⟩⟩
    have hv := hsm (by rw [e]; simp)
    rw [e] at hv
    obtain rfl := Option.some.inj hv
    intro e2
    split at e2 <;> rcases e2 with e2 | e2 <;> cases e2
  refine sat_ite (fun _ => ?_) (fun _ => ?_)
  · refine Sat.bind (Sat.mono (end_flush T E 1 (by decide) (by decide) F1 hp0 hla hpl hma Ch1) ?_)
    rintro r H2 q
    have K := fin 1 .finish_done (by decide) (by decide) r H2 q
    cases r with
    | none => exact Sat.pure (K.1 rfl)
    | some v => exact Sat.pure (K.2 v rfl)
  · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine sat_ite (fun _ => ?_) (fun hs => ?_)
    · refine Sat.bind (Sat.mono (end_flush T E 0 (by decide) (by decide) F1 hp0 hla hpl hma Ch1) ?_)
      rintro r H2 q
      have K := fin 0 .block_done (by decide) (by decide) r H2 q
      cases r with
      | none => exact Sat.pure (K.1 rfl)
      | some v => exact Sat.pure (K.2 v rfl)
    · have hs0 : sT.sym_next = 0 := by simpa using hs
      refine Sat.pure ⟨exit_ok E F1 flush _ (fun s2 h2 => ?_) (fun _ s2 h2 => ?_), fun s2 d2 h2 hd2 => ?_⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
        refine ⟨hs0, ?_, hla, LazyOk.of_clear hpl hma, hma⟩
        show sT.sym_next < sT.sym_end
        rw [hs0]; exact UInt32.lt_iff_toNat_lt.mpr (by simpa using hse)
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2); exact hp0
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
        obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd2)
        exact Ch1

/-- `slowTail`: after the loop broke on an empty lookahead, the pending literal is tallied, then `slowEnd`. -/
theorem slowTail_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sT : DeflateState}
    {dT : Array UInt8} {level : Int32} (E : Env h b wo level) (flush : Int32)
    (C : SLC h i b (SH H0 i z b sT dT)) (Ch : ChainOk b dT sT) (L : LazyOk sT) (hla : sT.lookahead = 0) :
    Sat (SH H0 i z b sT dT) (slowTail (some b) (.ref (.heap b) wo) flush) (fun bs H2 => SPost h i b flush bs H2) := by
  obtain ⟨hwin, hT, -, -⟩ := env_st E C.1
  obtain ⟨hlook, -, -, -, -, -, -, -⟩ := slf_nums C.1
  obtain ⟨hp0, hsym⟩ := C.2 sT (SH_dstate _ _ _ _ _ _)
  have hpl : sT.prev_length < 3 := by
    by_cases h3 : 3 ≤ sT.prev_length
    · obtain ⟨-, a2, a3, -⟩ := L.1 h3
      have := UInt32.le_iff_toNat_le.mp h3
      rw [hla] at a2; simp at a2 this; omega
    · exact UInt32.not_le.mp h3
  unfold slowTail
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine sat_ite (fun hm => ?_) (fun hm => ?_)
  · have hm' : sT.match_available ≠ 0 := by simpa using hm
    obtain ⟨h1s, hbs⟩ := L.2.1 hm'
    obtain ⟨wo', po, ho, pbo, Ly, -, hwp, -, hpb, hhp, hsb⟩ := slf_lay C.1
    have hwin' := Ly.win
    rw [hwin] at hwin'
    obtain rfl : wo = wo' := by injection hwin' with e; injection e
    have hLp := Ly.pw
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := sT) (d := dT)
      (off := wo) ((sT.strstart - 1).toNat : Int) (by omega) (by rw [Int.toNat_natCast, toNat_sub1 h1s]; omega)
    refine Sat.bind (Sat.of_eq ec ?_)
    refine Sat.bind (Sat.mono (slf_tally_lit0 C.1 hp0 (UInt32.le_of_lt hsym) hbs c) ?_)
    rintro r H2 ⟨lt, d', rfl, F2, ⟨sbo, hi, da, db, hda, hdb, hsb', hw⟩, -⟩
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hda)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hdb)
    have hsb2 := hsb' sT (SH_dstate _ _ _ _ _ _)
    rw [hsb] at hsb2
    obtain rfl : pbo + sT.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
    refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sT with
      sym_next := sT.sym_next + 3, dyn_ltree := lt, match_available := 0 }) rfl) ?_)
    exact slowEnd_ok T E flush (slf_view F2 rfl rfl rfl hT) hp0 hla hpl rfl
      (chain_keep C.1 Ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun pbo' hpb' j hj => by
        rw [hpb] at hpb'
        obtain rfl : pbo = pbo' := by injection hpb' with e; injection e
        exact hw.2 j (Or.inl (by omega)))
  · have hm' : sT.match_available = 0 := by simpa using hm
    exact slowEnd_ok T E flush C.1 hp0 hla hpl hm' Ch

theorem floor_le (a g : UInt32) : (if a > g then g else a) ≤ a := by
  split
  · rename_i hg; exact UInt32.le_of_lt hg
  · exact UInt32.le_refl _

/-- **`deflate_slow` keeps the strategy frame and the hash chains** (`StrategyFacts.slow`), given the block
emitters. -/
theorem slow_ok (T : TreesFacts) : StratOkC (TableAt 7 9) ZlibNg.DeflateSlow.deflate_slow := by
  intro h s b flush P hsb hE hC
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  obtain ⟨st, hst, C0, L0, hlf0, hT0⟩ := slow_entry P hz hb hE
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  have Ch0 := hC st d ⟨i, z, rfl, hz, hb, hst⟩ hd
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨-, wo, -, -, -, -, hwin, -⟩ := c.lay
  have hwin' : st.window = .val (.ref (.heap b) wo) := hwin
  obtain ⟨f, hf⟩ := c.fns.1
  have hf' : st.longest_match = .val f := hf
  have hib : st.insert_batch = .val (insertBatchOf st.level) := c.fns.2
  have E : Env h b wo st.level := ⟨fun st0 h0 => by rw [hst] at h0; cases h0; exact hwin',
    fun st0 h0 => by rw [hst] at h0; cases h0; exact ⟨hT0, hlf0⟩, fun st0 h0 => by rw [hst] at h0; cases h0; rfl⟩
  suffices S : Sat h (deflate_slow (some b) flush) (fun bs h' => SPost h i b flush bs h') by
    obtain ⟨bs, h', e, q1, q2⟩ := S
    exact ⟨bs, h', e, q1, fun st2 d2 ⟨i2, z2, e2, hz2, hb2, hst2⟩ hd2 => q2 st2 d2 hst2 hd2⟩
  rw [slow_eq]
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hf']
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hib]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin']
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (RI h i b flush) (RM i b)
    (fun c H => RI h i b flush c H ∧ c ≠ .cont) ?_ (s := Ctl.cont)
    ⟨C0, fun st2 d2 h2 hd2 => by
      rw [hst] at h2; cases h2; rw [hd] at hd2; cases hd2; exact ⟨Ch0, L0⟩⟩ ?_) ?_)
  · rintro c H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, fun e => by subst e; simp at hc⟩⟩
    cases c with
    | cont =>
      exact Sat.mono (trip_ok T flush f _ _ (floor_le _ _) E hI.1 hI.2) fun v H2 ⟨a, m⟩ => ⟨a, by simp only [RM]; exact m⟩
    | brk => simp at hc
    | ret r => simp at hc
  · have := avIn_lt h i
    have : laOf h b < 2 ^ 32 := by
      simp only [laOf]; split
      · exact UInt32.toNat_lt _
      · decide
    simp only [RM, fuel]; omega
  rintro c H ⟨hI, hc⟩
  cases c with
  | cont => exact absurd rfl hc
  | ret r => exact Sat.pure hI
  | brk =>
    obtain ⟨C1, S1, hl1⟩ := hI
    obtain ⟨H0, z1, s1, d1, rfl⟩ := slf_sh C1.1
    obtain ⟨Ch1, L1⟩ := S1 s1 d1 (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
    exact slowTail_ok T E flush C1 Ch1 L1 (hl1 s1 (SH_dstate _ _ _ _ _ _))

end ZlibNgF.Proof.SlowSafety
