import ZlibNgF.Proof.«deflate_fast.c.trip»
import ZlibNgF.ZlibNg.«deflate_fast.c»

/-!
# `deflate_fast` (`ZlibNgF`)

`fast_ok`: the fast strategy (level 2, any strategy but `Z_HUFFMAN_ONLY` and `Z_RLE`, `Z_FIXED` included) keeps the
strategy frame and the hash chains (`StratOkC (TableAt 2 2) deflate_fast`), given the block emitters (`TreesFacts`).
The outer loop runs `trip_ok` with the measure `avail_in + lookahead`; after the loop, `s->insert` is set and the
common tail flushes the last block (`ftail_ok`, with the chains kept by `FLUSH_BLOCK`).
-/

set_option autoImplicit false
set_option pp.oneline true

namespace ZlibNgF.Proof.FastP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.FastSteps ZlibNgF.Proof.FastFrame ZlibNgF.Proof.FastCont ZlibNgF.Proof.FastTrip
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateFast

/-- `FLUSH_BLOCK(s, window, last)` from `SLF` with no pending bytes, the hash chains kept. -/
theorem flushC (T : TreesFacts) {h H : Heap} {i b wo : Nat} (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b H) (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo))
    (Ck : CK b H) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) last) (fun r H2 => (avIn H2 i = avIn H i ∧ SLF h i b H2 ∧
      (∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧
        ∃ st, H.dstate b = some st ∧ st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
          st2.window = st.window) ∧
      (r = none → ∀ st2, H2.dstate b = some st2 → st2.pending = 0) ∧
      (r ≠ none → r = some (if last != 0 then .finish_started else .need_more))) ∧ CK b H2) := by
  obtain ⟨z, st, -, -, -, hst, -, -⟩ := F.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  refine Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (slf_flush T last hl0 hl1 F hp)
    (ZlibNgF.Proof.StrategyChain.slf_flush_chain T last hl0 hl1 F hp)) ?_
  rintro r H2 ⟨q, hck⟩
  exact ⟨q, fun st2 d2 h2 hd2 => hck st d st2 d2 hst hd h2 hd2 (Ck st d hst hd)⟩

/-- The common tail (`s->insert` set before it) from `SLC` with an empty lookahead, at level 2: `StratPost` and the
hash chains. -/
theorem ftail_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} (flush : Int32) (C : SLC h i b H) (Ck : CK b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.level = 2)
    (hla : ∀ st, H.dstate b = some st → st.lookahead = 0) :
    Sat H (strat_tail (some b) (.ref (.heap b) wo) flush) (fun r H' => StratPost h (some i) flush r H' ∧ CK b H') := by
  have hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := by
    intro st hst
    obtain ⟨st0, h0, hw⟩ := C.1.win
    exact ⟨(C.2 st hst).1, (hw st hst).trans (hw0 st0 h0)⟩
  have fl : ∀ (last : Int32) (bs : BlockState), 0 ≤ last → last ≤ 1 →
      (bs = .block_done ∨ bs = .finish_done) → Sat H (do
        if let some r ← FLUSH_BLOCK (some b) (.ref (.heap b) wo) last then return r
        return bs) (fun r H' => StratPost h (some i) flush r H' ∧ CK b H') := by
    intro last bs hl0 hl1 hbs
    refine Sat.bind (Sat.mono (flushC T last hl0 hl1 C.1 hp Ck) ?_)
    rintro r H2 ⟨⟨-, F2, hs2, hn2, hsm⟩, Ck2⟩
    have hx : ∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧ st2.lookahead = 0 :=
      fun st2 h2 => by
        obtain ⟨e1, e2, st, hst, e3, -⟩ := hs2 st2 h2
        exact ⟨e1, e2, by rw [e3]; exact hla st hst⟩
    cases r with
    | none =>
      exact Sat.pure ⟨slf_post_l F2 _ _ hn fun st2 h2 =>
        ⟨(hx st2 h2).2.1, fun _ => hn2 rfl st2 h2, fun _ => (hx st2 h2).1, fun _ => ⟨(hx st2 h2).1, (hx st2 h2).2.2⟩,
          fun _ => (hx st2 h2).1⟩, Ck2⟩
    | some v =>
      obtain ⟨rfl⟩ := Option.some.inj (hsm (by simp))
      refine Sat.pure ⟨slf_post_l F2 _ _ hn fun st2 h2 => ⟨(hx st2 h2).2.1, fun e => ?_, fun _ => (hx st2 h2).1,
        fun _ => ⟨(hx st2 h2).1, (hx st2 h2).2.2⟩, fun _ => (hx st2 h2).1⟩, Ck2⟩
      split at e <;> rcases e with e | e <;> cases e
  unfold strat_tail
  by_cases hf : flush == Z_FINISH
  · simp only [hf, ↓reduceIte]
    exact fl 1 .finish_done (by decide) (by decide) (.inr rfl)
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨z, st, -, hz, hb, hst, -, -⟩ := C.1.live
    obtain ⟨i', z', b', st', al, e, L, -, -⟩ := live C.1.inv
    obtain rfl : i = i' := Option.some.inj e
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
    obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
    refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
    by_cases hs : (st.sym_next != 0) = true
    · simp only [hs, ↓reduceIte]
      exact fl 0 .block_done (by decide) (by decide) (.inl rfl)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      have h0 : st.sym_next = 0 := by simpa using hs
      refine Sat.pure ⟨slf_post_l C.1 _ _ hn fun st2 h2 => ?_, Ck⟩
      obtain rfl := Option.some.inj (hst.symm.trans h2)
      exact ⟨(C.2 st hst).2, fun _ => (C.2 st hst).1, fun _ => h0, fun e => (by rcases e with e | e <;> cases e),
        fun _ => h0⟩

/-- **`deflate_fast` keeps the strategy frame and the hash chains.** -/
theorem fast_ok (T : TreesFacts) : StratOkC (TableAt 2 2) deflate_fast := by
  intro h s b flush P hsb hE hC
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hD : ∀ st0, h.dstate b = some st0 → DStateIs h (some i) b st0 := fun st0 h0 => ⟨i, z, rfl, hz, hb, h0⟩
  have hn : ∀ st0, h.dstate b = some st0 → st0.level = 2 := fun st0 h0 => by
    obtain ⟨h1, h2, -⟩ := hE b st0 (hD st0 h0)
    exact Int32.le_antisymm h2 h1
  have hl : ∀ st0, h.dstate b = some st0 → st0.level = 2 ∧ HASHLESS st0.level st0.strategy = false :=
    fun st0 h0 => by
      obtain ⟨-, -, h3, h4⟩ := hE b st0 (hD st0 h0)
      refine ⟨hn st0 h0, ?_⟩
      simp only [HASHLESS, hn st0 h0, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      exact ⟨⟨by decide, h3⟩, h4⟩
  have hE' : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.level ≠ 1 := fun b' st hd => by
    obtain ⟨h1, h2, -⟩ := hE b' st hd
    have := Int32.le_antisymm h2 h1
    rw [this]; exact ⟨by decide, by decide⟩
  obtain ⟨st, hst, I0⟩ := sli_entry_l P hz hb hE'
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨-, wo, -, -, -, -, hwin, -⟩ := c.lay
  simp only [dview] at hwin
  have hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo) := fun st0 h0 => by
    rw [hst] at h0; cases h0; exact hwin
  have Ck0 : CK b h := fun st0 d0 h0 hd0 => hC st0 d0 (hD st0 h0) hd0
  have C0 : SLC h i b h := by
    obtain ⟨H1, z1, st1, d1, e1, C1⟩ := I0
    obtain rfl : st1 = st := by
      have := congrArg (fun H => H.dstate b) e1
      simp only [SH_dstate] at this
      exact (Option.some.inj (this.symm.trans hst)).symm
    rw [FS_self, ← e1] at C1
    exact C1
  suffices S : Sat h (deflate_fast (some b) flush) (fun bs h' => StratPost h (some i) flush bs h' ∧ CK b h') by
    obtain ⟨bs, h', e2, q1, q2⟩ := S
    refine ⟨bs, h', e2, q1, fun st2 d2 hs2 hd2 => ?_⟩
    obtain ⟨i2, z2, e3, hz2, hb2, hst2⟩ := hs2
    exact q2 st2 d2 hst2 hd2
  unfold deflate_fast
  extract_lets bf0 ml0 jpE
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  extract_lets mi
  have hmi : 2 ≤ mi.toNat := by
    simp only [mi]; split
    · rename_i hg; have := UInt32.lt_iff_toNat_lt.mp hg; simp at this; omega
    · decide
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (OI h i b flush) (OM i b)
    (fun v H => OI h i b flush v H ∧ (v.1 matches .cont) = false) ?_ (s := (Ctl.cont, bf0, ml0))
    ⟨C0, Ck0, by simp only [ml0]; decide⟩ ?_) ?_)
  · rintro ⟨cc, bfl, ml⟩ H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases cc with
    | cont =>
      obtain ⟨C1, Ck1, hml⟩ := hI
      exact Sat.mono (trip_ok T bfl hw0 hn hl hmi C1 Ck1 hml) fun v H2 ⟨a, m⟩ => ⟨a, by simpa only [OM] using m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := avIn_lt h i
    have := UInt32.toNat_lt st.lookahead
    simp only [OM, LaS, hst, fuel]; omega
  rintro ⟨cc, bfl, ml⟩ H ⟨hI, hc⟩
  cases cc with
  | cont => cases hc
  | ret r => exact Sat.pure hI
  | brk =>
    obtain ⟨C1, Ck1, hl0⟩ := hI
    obtain ⟨z1, st1, -, hz1, hb1, hst1, -, -⟩ := C1.1.live
    obtain ⟨d1, hd1⟩ := bytes_of_dstate hst1
    have eH := ZlibNgF.Proof.DeflateReset.SH_self hz1 (dstates_of_dstate hst1 hd1) hd1
    rw [← eH] at C1 Ck1 hl0 ⊢
    have hv : (if st1.strstart < STD_MIN_MATCH - 1 then st1.strstart else STD_MIN_MATCH - 1) ≤ st1.strstart := by
      split
      · exact UInt32.le_refl _
      · exact UInt32.le_of_lt (UInt32.not_lt.mp (by assumption))
    refine Sat.bind (Sat.mono (slc_insert C1 _ hv) ?_)
    rintro _ H2 ⟨C2, rfl⟩
    have Ck2 : CK b (SH H i z1 b { st1 with insert := if st1.strstart < STD_MIN_MATCH - 1 then st1.strstart
        else STD_MIN_MATCH - 1 } d1) := fun st2 d2 h2 hd2 => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd2)
      exact ZlibNgF.Proof.DeflateSide.ChainOk.of_state (Ck1 st1 d1 (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _))
        rfl rfl rfl rfl rfl rfl rfl
    exact ftail_ok T flush C2 Ck2 hw0 hn fun st2 h2 => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      exact hl0 st1 (SH_dstate _ _ _ _ _ _)

end ZlibNgF.Proof.FastP
