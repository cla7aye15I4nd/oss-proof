import ZlibNgF.Proof.«deflate_strategy.common»
import ZlibNgF.ZlibNg.«deflate_huff.c»

/-!
# `deflate_huff` (`ZlibNgF`)

`huff_ok`: the `Z_HUFFMAN_ONLY` strategy keeps the strategy frame (`StratOkP`), given the block emitters
(`TreesFacts`). A trip of the loop refills the window when the lookahead is empty (`sli_fill`), tallies one literal
`window[strstart]` (`sli_tally_lit`), and flushes a full symbol buffer (`sli_flush`); the measure
`avail_in + lookahead` drops by one per trip. The tail is `strat_tail` (`slc_tail`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateHuffP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateHuff

/-- The window and the bytes `[strstart, strstart + lookahead)` of the local copy lie in block `b`. -/
theorem sli_win {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d))
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    st.window = .val (.ref (.heap b) wo) ∧ wo + ss.toNat + la.toNat ≤ d.size := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨st0, h0, hw⟩ := C.1.win
  have hwin : st.window = .val (.ref (.heap b) wo) := (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
  obtain ⟨z2, st2, al, hz2, hb2, hst2, -, c⟩ := C.1.live
  obtain rfl : FS st la ss = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨d3, wo', po, ho, pbo, hd3, hw3, -, -, -, h1, h2, h3, h4, -⟩ := c.lay
  obtain rfl : d = d3 := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd3)
  have hlook : ss.toNat + la.toNat ≤ st.window_size.toNat := c.look
  have hw3' : st.window = .val (.ref (.heap b) wo') := hw3
  rw [hwin] at hw3'
  obtain rfl : wo = wo' := by cases hw3'; rfl
  have h1' : wo + st.window_size.toNat ≤ po := h1
  have h2' : po + 2 * st.w_size.toNat ≤ ho := h2
  have h4' : pbo + 4 * st.lit_bufsize.toNat + 64 ≤ d.size := h4
  exact ⟨hwin, by omega⟩

/-- The loop state's invariant. -/
def HI (h : Heap) (i b : Nat) (flush : Int32) (v : UInt32 × UInt32 × HuffExit) (H : Heap) : Prop :=
  match v.2.2 with
  | .ret r => StratPost h (some i) flush r H
  | .brk => SLI h i b v.1 v.2.1 H ∧ v.1 = 0
  | .cont => SLI h i b v.1 v.2.1 H

/-- The loop measure: `avail_in + lookahead + 1` while the loop goes on. -/
def HM (i : Nat) (v : UInt32 × UInt32 × HuffExit) (H : Heap) : Nat :=
  match v.2.2 with
  | .cont => avIn H i + v.1.toNat + 1
  | _ => 0

/-- One trip of the loop. -/
theorem trip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {la ss : UInt32} (flush : Int32)
    (I : SLI h i b la ss H) (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hfx : NotSlow h b) :
    Sat H (huff_trip (some b) (.ref (.heap b) wo) flush la ss) (fun v H2 =>
      HI h i b flush v H2 ∧ HM i v H2 < avIn H i + la.toNat + 1) := by
  unfold huff_trip
  extract_lets jp
  have hjp : ∀ (v : UInt32 × UInt32 × HuffExit) H1,
      (v.2.2.isCont = true → SLI h i b v.1 v.2.1 H1 ∧ 1 ≤ v.1.toNat ∧ avIn H1 i + v.1.toNat ≤ avIn H i + la.toNat) →
      (v.2.2.isCont = false → HI h i b flush v H1) →
      Sat H1 (jp v) (fun v H2 => HI h i b flush v H2 ∧ HM i v H2 < avIn H i + la.toNat + 1) := by
    rintro ⟨la1, ss1, ex⟩ H1 hc hn
    cases ex with
    | ret r => exact Sat.pure ⟨hn rfl, by simp [HM]⟩
    | brk => exact Sat.pure ⟨hn rfl, by simp [HM]⟩
    | cont =>
      obtain ⟨I1, hl1, hm⟩ := hc rfl
      simp only [] at I1 hl1 hm
      simp only [jp, HuffExit.isCont, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨H0, z, st, d, rfl, C⟩ := I1
      obtain ⟨hwin, hwd⟩ := sli_win ⟨H0, z, st, d, rfl, C⟩ hw0
      obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
        (off := wo) (ss1.toNat : Int) (by omega) (by simp; omega)
      refine Sat.bind (Sat.of_eq ec (Sat.bind (Sat.mono (sli_tally_lit ⟨H0, z, st, d, rfl, C⟩ hl1 c) ?_)))
      rintro r H2 ⟨ha2, W2, I2⟩
      have hm2 : avIn H2 i + (la1 - 1).toNat + 1 < avIn H i + la.toNat + 1 := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using hl1)), ha2]; simp; omega
      cases r with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact Sat.pure ⟨I2 rfl, hm2⟩
      | true =>
        simp only [↓reduceIte]
        refine Sat.bind (Sat.mono (sli_flush T 0 (by decide) (by decide) W2 hw0) fun _ H3 h3 =>
          Sat.bind (Sat.mono h3 ?_))
        rintro r2 H4 ⟨ha4, hnone, hsome⟩
        cases r2 with
        | none => exact Sat.pure ⟨hnone rfl, by simp only [HM]; rw [ha4]; exact hm2⟩
        | some v =>
          obtain ⟨hv, F4, hs4⟩ := hsome (by simp)
          have hv' : v = .need_more := by simpa using hv
          subst hv'
          refine Sat.pure ⟨slf_post F4 _ _ hfx fun st4 h4 => ⟨(hs4 st4 h4).2, ?_, fun _ => (hs4 st4 h4).1, ?_,
            ?_⟩, by simp [HM]⟩
          · intro e; rcases e with e | e <;> cases e
          · intro e; rcases e with e | e <;> cases e
          · intro e; cases e
  by_cases hl : la == 0
  · simp only [hl, ↓reduceIte]
    have hl0 : la = 0 := by simpa using hl
    refine Sat.bind (Sat.mono (sli_fill I (by rw [hl0]; decide)) fun _ H1 h1 => Sat.bind (Sat.mono h1 ?_))
    rintro _ H2 ⟨H0, z, st, d, rfl, I2, hm1, -, -⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (rdD_SH _) ?_)))
    by_cases hl2 : st.lookahead == 0
    · simp only [hl2, ↓reduceIte]
      by_cases hf : flush == Z_NO_FLUSH
      · simp only [hf, ↓reduceIte]
        have hf' : flush = Z_NO_FLUSH := by simpa using hf
        subst hf'
        exact hjp (_, _, .ret .need_more) _ (fun e => by cases e) (fun _ => slc_post (sli_slc I2) hfx)
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        exact hjp (_, _, .brk) _ (fun e => by cases e) (fun _ => ⟨I2, by simpa using hl2⟩)
    · simp only [hl2, Bool.false_eq_true, ↓reduceIte]
      have : st.lookahead.toNat ≠ 0 := fun e => hl2 (by
        have e' : st.lookahead = 0 := UInt32.toNat_inj.mp (by rw [e]; rfl)
        simp [e'])
      refine hjp (_, _, .cont) _ (fun _ => ⟨I2, by simp only []; omega, ?_⟩) (fun e => by cases e)
      simp only []; rw [avIn_SH]; omega
  · simp only [hl, Bool.false_eq_true, ↓reduceIte]
    have : la.toNat ≠ 0 := fun e => hl (by
      have e' : la = 0 := UInt32.toNat_inj.mp (by rw [e]; rfl)
      simp [e'])
    exact hjp (_, _, .cont) _ (fun _ => ⟨I, by simp only []; omega, Nat.le_refl _⟩) (fun e => by cases e)

/-- `deflate_huff` keeps the strategy frame. -/
theorem huff_ok (T : TreesFacts) :
    StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_HUFFMAN_ONLY) deflate_huff := by
  intro h s b flush P hsb hE
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hE' : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.strategy ≠ Z_FIXED := fun b' st hd => by
    obtain ⟨h1, h2⟩ := hE b' st hd; exact ⟨h1, by rw [h2]; decide⟩
  obtain ⟨st, hst, I0⟩ := sli_entry P hz hb hE'
  have hn : NotSlow h b := fun st0 h0 =>
    ⟨(hE' b st0 ⟨i, z, rfl, hz, hb, h0⟩).2, fun ht => ht.2.2.1 (hE b st0 ⟨i, z, rfl, hz, hb, h0⟩).2⟩
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨-, wo, -, -, -, -, hwin, -⟩ := c.lay
  simp only [dview] at hwin
  have hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo) := fun st0 h0 => by
    rw [hst] at h0; cases h0; exact hwin
  suffices S : Sat h (deflate_huff (some b) flush) (fun bs h' => StratPost h (some i) flush bs h') by
    obtain ⟨bs, h', e, q⟩ := S
    exact ⟨bs, h', e, q⟩
  unfold deflate_huff
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) (Sat.bind (Sat.of_eq (rdD_app L _) ?_)))
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (HI h i b flush) (HM i)
    (fun v H => HI h i b flush v H ∧ v.2.2.isCont = false) ?_ (s := (st.lookahead, st.strstart, .cont)) I0 ?_) ?_)
  · rintro ⟨la, ss, ex⟩ H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases ex with
    | cont =>
      exact Sat.mono (trip_ok T flush hI hw0 hn) fun v H2 ⟨a, m⟩ => ⟨a, by simp only [HM]; exact m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := avIn_lt h i
    have := UInt32.toNat_lt st.lookahead
    simp only [HM, fuel]; omega
  rintro ⟨la, ss, ex⟩ H ⟨hI, hc⟩
  cases ex with
  | cont => cases hc
  | ret r => exact Sat.pure hI
  | brk =>
    obtain ⟨hI, hl0⟩ := hI
    refine Sat.bind (Sat.mono (sli_wb hI) ?_)
    rintro _ H1 ⟨C1, -, H0, z1, st1, d1, rfl, hla, -⟩
    refine Sat.bind (Sat.mono (slc_insert C1 0 UInt32.zero_le) ?_)
    rintro _ H2 ⟨C2, rfl⟩
    refine slc_tail T flush C2 hw0 hn fun st2 h2 => ?_
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    simp only [] at hl0 ⊢; rw [hla, hl0]

end ZlibNgF.Proof.DeflateHuffP
