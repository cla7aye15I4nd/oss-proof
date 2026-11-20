import ZlibNgF.Proof.«deflate_slow.c.emit»

/-!
# One trip of `deflate_slow` (`ZlibNgF`)

`trip_ok`: from the loop invariant (`RI` with `cont`), one trip of the `for (;;)` of `deflate_slow` ends with the loop
invariant and a smaller measure (`RM`). The trip refills the window when the lookahead is short (`slc_fill`), inserts
the hash of `strstart` (the chains grow by `strstart`, kept with `strstart + 1`), searches a longer match than the
pending one (`slowB_ok`: `longest_match` from a candidate within `MAX_DIST`, the kept length by
`SlowLazy.ml_cases`), and emits (`SlowEmit.slowC_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowTrip
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.SlowFrame ZlibNgF.Proof.SlowStep ZlibNgF.Proof.SlowEmit
open ZlibNg.DeflateP ZlibNg.DeflateSlow

/-- A `Sat` fact about `if c then A else B` from facts about both branches. -/
theorem sat_ite {α : Type} {H : Heap} {c : Prop} [Decidable c] {A B : M α} {Q : α → Heap → Prop}
    (h1 : c → Sat H A Q) (h2 : ¬ c → Sat H B Q) : Sat H (if c then A else B) Q := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact h1 hc
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact h2 hc

/-- What `slowB` needs of the state `sB` after the hash insertion: the loop frame, the hash chains with `strstart`
one past the inserted position, a non-empty lookahead, `LazyOk`, the bound `M0` of the measure. -/
structure BPre (h : Heap) (i b wo : Nat) (level : Int32) (M0 : Nat) (H0 : Heap) (z : ZStream) (sB : DeflateState)
    (dB : Array UInt8) : Prop where
  env : Env h b wo level
  slc : SLC h i b (SH H0 i z b sB dB)
  ch : ChainOk b dB { sB with strstart := sB.strstart + 1 }
  la1 : 1 ≤ sB.lookahead.toNat
  lazy : LazyOk sB
  meas : z.avail_in.toNat + sB.lookahead.toNat ≤ M0

/-- `CPre` of the state after the match search: `prev_match = match_start` of before, `match_start = ms`. -/
theorem cpre_of {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sB : DeflateState} {dB : Array UInt8}
    {level : Int32} {M0 : Nat} (P : BPre h i b wo level M0 H0 z sB dB) (ms ml : UInt32)
    (hml : 3 ≤ ml → (3 ≤ sB.prev_length ∧ ml ≤ sB.prev_length) ∨ (ml.toNat ≤ 258 ∧ ml.toNat ≤ sB.lookahead.toNat ∧
      ms.toNat < sB.strstart.toNat ∧ sB.strstart.toNat - ms.toNat ≤ (MAX_DIST sB).toNat)) :
    CPre h i b wo level ml M0 H0 z { sB with prev_match := sB.match_start, match_start := ms } dB := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 sB (SH_dstate _ _ _ _ _ _)
  obtain ⟨l1, l2, -, -⟩ := P.lazy
  exact ⟨P.env, slc_of (slf_view (st' := { sB with prev_match := sB.match_start, match_start := ms }) P.slc.1 rfl rfl
    rfl hT) hp0 hsym, chain_keep P.slc.1 P.ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _)
    fun _ _ _ _ => rfl, P.la1, l1, l2, hml, P.meas⟩

/-- `slowB`: `prev_match = match_start`, and, for a candidate `hash_head` within `MAX_DIST` behind `strstart` and a
pending match shorter than `max_lazy_match`, `longest_match` with `prev_length` raised to `match_floor`; the kept
length after the `match_discard` test and the test of patch 0019; then `slowC`. -/
theorem slowB_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sB : DeflateState}
    {dB : Array UInt8} {level : Int32} {M0 : Nat} (flush : Int32) (lm : LongestMatchFn) (md mf : UInt32)
    (hmf : mf ≤ md) (hh : UInt32) (P : BPre h i b wo level M0 H0 z sB dB) :
    Sat (SH H0 i z b sB dB) (slowB (some b) (.ref (.heap b) wo) lm (insertBatchOf level) level md mf hh)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, -, -, w1, w2, -, -⟩ := slf_nums P.slc.1
  have hmd : (MAX_DIST sB).toNat = sB.w_size.toNat - 262 := by
    unfold MAX_DIST
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show 262 ≤ _; omega))]; rfl
  unfold slowB
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with prev_match := sB.match_start }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  dsimp only
  refine sat_ite (fun hc => ?_) (fun _ => slowC_ok T flush (cpre_of P sB.match_start _ fun h3 => absurd h3 (by decide)))
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨hd1, hd2⟩, -⟩, -⟩ := hc
  have hd1' : (sB.strstart.toNat : Int) - hh.toNat ≤ (MAX_DIST sB).toNat := hd1
  have hd2' : (0 : Int) < (sB.strstart.toNat : Int) - hh.toNat := hd2
  have hcm : hh.toNat < 65536 := by omega
  let s2 : DeflateState := { sB with
    prev_match := sB.match_start, prev_length := if sB.prev_length < mf then mf else sB.prev_length }
  have hlb : (ZlibNgF.Proof.LongestMatch.limitBase s2).toNat ≤ hh.toNat := by
    show (ZlibNgF.Proof.LongestMatch.limitBase sB).toNat ≤ hh.toNat
    unfold ZlibNgF.Proof.LongestMatch.limitBase
    split
    · rename_i hg
      have hg' := UInt32.lt_iff_toNat_lt.mp hg
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt hg)]; omega
    · simp
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := s2) rfl) ?_)
  have F2 := slf_view (st' := s2) P.slc.1 rfl rfl rfl hT
  refine Sat.bind (Sat.mono (slf_match F2 lm hh hcm hlb) ?_)
  rintro r _ ⟨ms, rfl, hpr⟩
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with prev_match := sB.match_start, match_start := ms })
    rfl) ?_)
  refine sat_ite (fun _ => slowC_ok T flush (cpre_of P ms _ fun h3 => absurd h3 (by decide))) (fun h1 => ?_)
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  refine sat_ite (fun _ => slowC_ok T flush (cpre_of P ms _ fun h3 => absurd h3 (by decide))) (fun h2 => ?_)
  refine slowC_ok T flush (cpre_of P ms r fun h3 => ?_)
  have h1' : md.toNat < r.toNat := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp h1)
  have h2' : ms.toNat < sB.strstart.toNat := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp h2)
  have h3' : 3 ≤ r.toNat := by have := UInt32.le_iff_toNat_le.mp h3; simpa using this
  have hmf' := UInt32.le_iff_toNat_le.mp hmf
  have K := ZlibNgF.Proof.SlowLazy.ml_cases sB.prev_length.toNat mf.toNat md.toNat
    (if sB.prev_length < mf then mf else sB.prev_length).toNat
    (if (if sB.prev_length < mf then mf else sB.prev_length) != 0 then
      (if sB.prev_length < mf then mf else sB.prev_length) else STD_MIN_MATCH - 1).toNat
    r.toNat ms.toNat sB.strstart.toNat sB.lookahead.toNat (ZlibNgF.Proof.LongestMatch.limitBase s2).toNat r.toNat
    hmf' ⟨fun hl => by rw [ite_eq_left_of_eq_true _ _ (eq_true (UInt32.lt_iff_toNat_lt.mpr hl))], fun hl => by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hl (UInt32.lt_iff_toNat_lt.mp e)))]⟩
    ⟨fun hn => by
      have : ((if sB.prev_length < mf then mf else sB.prev_length) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro e; exact hn (by rw [e]; rfl)
      rw [ite_eq_left_of_eq_true _ _ (eq_true this)], fun hn => by
      have : ¬ ((if sB.prev_length < mf then mf else sB.prev_length) != 0) = true := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact UInt32.toNat_inj.mp (by rw [hn]; rfl)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]; rfl⟩
    (by rcases hpr with a | ⟨a1, a2, a3, -⟩
        · exact Or.inl a
        · exact Or.inr ⟨a1, a2, a3⟩)
    ⟨fun a => absurd a (by omega), fun _ a => absurd a (by omega), fun _ _ => rfl⟩ h3'
  rcases K with ⟨k1, k2⟩ | ⟨k1, k2, k3, k4⟩
  · exact Or.inl ⟨UInt32.le_iff_toNat_le.mpr (by simpa using k1), UInt32.le_iff_toNat_le.mpr k2⟩
  · refine Or.inr ⟨k1, k2, k4, ?_⟩
    have := ZlibNgF.Proof.SlowLazy.dist_le s2 ms.toNat k3 (by show 262 ≤ sB.w_size.toNat; omega)
    exact this

/-- What `slowA` needs of the state `st` after the refill: the loop frame, the hash chains, a non-empty lookahead,
`LazyOk`, the bound `M0` of the measure. -/
structure APre (h : Heap) (i b wo : Nat) (level : Int32) (M0 : Nat) (H0 : Heap) (z : ZStream) (st : DeflateState)
    (d : Array UInt8) : Prop where
  env : Env h b wo level
  slc : SLC h i b (SH H0 i z b st d)
  ch : ChainOk b d st
  la1 : 1 ≤ st.lookahead.toNat
  lazy : LazyOk st
  meas : z.avail_in.toNat + st.lookahead.toNat ≤ M0

/-- `slowA`: the hash of `strstart` inserted when 4 bytes are in the lookahead, then `slowB`. -/
theorem slowA_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState}
    {d : Array UInt8} {level : Int32} {M0 : Nat} (flush : Int32) (lm : LongestMatchFn) (md mf : UInt32)
    (hmf : mf ≤ md) (P : APre h i b wo level M0 H0 z st d) :
    Sat (SH H0 i z b st d) (slowA (some b) (.ref (.heap b) wo) lm (insertBatchOf level) level md mf)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, -, -, w1, -, -, -⟩ := slf_nums P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 st (SH_dstate _ _ _ _ _ _)
  have h7 : 7 ≤ st.level := (tab_lv hT).2.2
  have hss1 := toNat_add1 (x := st.strstart) (by omega)
  have post : ∀ (x : UInt32) (d' : Array UInt8), ZlibNgF.Proof.InsertLoop.GrowSt b st d d' (· = st.strstart.toNat) →
      SLF h i b (SH H0 i z b (FS { st with ins_h := x } st.lookahead st.strstart) d') → ∀ hh : UInt32,
      Sat (SH H0 i z b { st with ins_h := x } d')
        (slowB (some b) (.ref (.heap b) wo) lm (insertBatchOf level) level md mf hh)
        (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
    intro x d' g F' hh
    refine slowB_ok T flush lm md mf hmf hh ⟨P.env, slc_of F' hp0 hsym, ?_, P.la1, ?_, P.meas⟩
    · refine ZlibNgF.Proof.InsertGrow.ChainOk.grow P.ch g rfl rfl rfl rfl rfl
        (by show st.strstart.toNat ≤ (st.strstart + 1).toNat; omega) (chainLim_le h7 rfl
          (by show st.strstart.toNat ≤ (st.strstart + 1).toNat; omega)) fun q hq _ => chainLim_gt h7 ?_
      show q < (st.strstart + 1).toNat
      rw [hq]; omega
    · exact LazyOk.of_eq P.lazy rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  unfold slowA
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  dsimp only
  refine sat_ite (fun hl => ?_) (fun _ => ?_)
  · have hl' : 4 ≤ st.lookahead.toNat := by have := UInt32.le_iff_toNat_le.mp hl; simpa [WANT_MIN_MATCH] using this
    refine sat_ite (fun _ => ?_) (fun _ => ?_)
    · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.mono (slf_insert_roll (la := st.lookahead) (ss := st.strstart) P.slc.1 hwin st.strstart
        (by omega) (by omega)) ?_)
      rintro hh _ ⟨d', x, rfl, F', g⟩
      exact post x d' g F' hh
    · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.mono (slf_insert_knuth (la := st.lookahead) (ss := st.strstart) P.slc.1 hwin st.strstart
        (by omega) (by omega)) ?_)
      rintro hh _ ⟨d', x, rfl, F', g⟩
      exact post x d' g F' hh
  · exact slowB_ok T flush lm md mf hmf _ ⟨P.env, P.slc, chain_keep P.slc.1 P.ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by show st.strstart.toNat ≤ (st.strstart + 1).toNat; omega) fun _ _ _ _ => rfl, P.la1, P.lazy, P.meas⟩

/-- **One trip** of the loop of `deflate_slow`: from the loop invariant, the loop invariant by the way the trip ended
and a smaller measure. -/
theorem trip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {level : Int32} (flush : Int32) (lm : LongestMatchFn)
    (md mf : UInt32) (hmf : mf ≤ md) (E : Env h b wo level) (C : SLC h i b H) (S : SI b H) :
    Sat H (deflate_slow_trip (some b) flush lm (insertBatchOf level) (.ref (.heap b) wo) level md mf)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < avIn H i + laOf H b + 1) := by
  obtain ⟨H0, z, st, d, rfl⟩ := slf_sh C.1
  obtain ⟨Ch, L⟩ := S st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
  rw [avIn_SH, laOf_SH, trip_eq]
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  dsimp only
  refine sat_ite (fun hl => ?_) (fun hl => ?_)
  · have hl' : st.lookahead.toNat < 262 := by
      have := UInt32.lt_iff_toNat_lt.mp hl; simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
    refine Sat.bind (Sat.mono (slc_fill C hl' Ch L) ?_)
    rintro _ _ ⟨H1, z', st', d', rfl, C', Ch', L', hsum, -, hend⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    refine sat_ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨-, hf⟩ := hc
      obtain ⟨-, hT', -, -⟩ := env_st E C'.1
      refine Sat.pure ⟨⟨slf_postW C'.1 flush .need_more (fun st0 h0 => (tab_lv (E.tab st0 h0).1).2.1)
        (fun _ _ _ s3 hs3 => ?_) (fun s3 hs3 => ?_), fun s3 d3 hs3 hd3 => ?_⟩, by simp [RM]⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
        exact ⟨L', fun e => by cases e⟩
      · obtain ⟨hp3, hs3'⟩ := C'.2 s3 hs3
        refine ⟨hs3', ?_, fun hn => absurd hf hn, ?_, ?_⟩
        · intro e; rcases e with e | e <;> cases e
        · intro e; rcases e with e | e <;> cases e
        · intro e; cases e
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
        obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
        exact Ch'
    · refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine sat_ite (fun hz => ?_) (fun hz => ?_)
      · have hz' : st'.lookahead = 0 := by simpa using hz
        refine Sat.pure ⟨⟨C', fun s3 d3 hs3 hd3 => ?_, fun s3 hs3 => ?_⟩, by simp [RM]⟩
        · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
          obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
          exact ⟨Ch', L'⟩
        · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hs3)
          exact hz'
      · have hz' : st'.lookahead.toNat ≠ 0 := fun e => hz (by
          rw [beq_iff_eq]; exact UInt32.toNat_inj.mp (by rw [e]; rfl))
        exact slowA_ok T flush lm md mf hmf ⟨E, C', Ch', by omega, L', hsum⟩
  · have hl' : 262 ≤ st.lookahead.toNat := by
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl)
      simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
    exact slowA_ok T flush lm md mf hmf ⟨E, C, Ch, by omega, L, Nat.le_refl _⟩

end ZlibNgF.Proof.SlowTrip
