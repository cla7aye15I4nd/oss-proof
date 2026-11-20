import ZlibNgF.Proof.«deflate_quick.c.match»

/-!
# `deflate_quick` with tallied symbols (`ZlibNgF`)

A trip of the main loop of `deflate_quick_impl` with `static_emit == 0` (`trip_ok`): `quick_flush_pending` and
`quick_start_block` return 0 at once; the window is refilled when fewer than `MIN_LOOKAHEAD` bytes are left
(`sli_fill`); then the match part (`qmatch_ok`) or a literal (`qlit_ok`). The loop measure is `avail_in + lookahead`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.QuickP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateQuick

theorem qfp0 (st : StatePtr) : quick_flush_pending st 0 = pure false := rfl

theorem qsb0 (st : StatePtr) (ss la : UInt32) (last : Int32) : quick_start_block st ss la last 0 = pure false := rfl

/-- The end of a trip from `strstart` / `lookahead` with at least one byte: the match part or a literal. -/
theorem tail_ok (T : TreesFacts) {h H1 : Heap} {i b wo : Nat} {la1 ss1 : UInt32} {flush : Int32} {Mb : Nat}
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la1 ss1 H1)
    (hl : 1 ≤ la1.toNat) (hM : avIn H1 i + la1.toNat ≤ Mb)
    (k : UInt32 → Option (UInt32 × UInt32 × QuickExit) → M (UInt32 × UInt32 × QuickExit))
    (hk1 : ∀ sv r, k sv (some r) = pure r)
    (hk2 : ∀ sv, k sv none = (do
        let x ← quick_emit_lit (some b) sv.toUInt8 ss1 la1 0
        if x.1 = true then pure (x.2.1, x.2.2, QuickExit.ret BlockState.need_more)
        else pure (x.2.1, x.2.2, QuickExit.cont))) :
    Sat H1 ((Ptr.ref (BRef.heap b) wo).add (ss1.toNat : Int) >>= fun p => memread4 p >>= fun sv =>
      quick_try_match (some b) (.ref (.heap b) wo) 0 ss1 la1 sv >>= k sv)
      (fun v H2 => QI h i b flush v H2 ∧ QM i v H2 < Mb + 1) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  have I : SLI h i b la1 ss1 (SH H0 i z b st d) := ⟨H0, z, st, d, rfl, C⟩
  obtain ⟨-, -, hk, -⟩ := sli_facts I hw0
  refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss1.toNat (by omega)) ?_)
  obtain ⟨sv, esv⟩ := ZlibNgF.Proof.WinBase.memread4_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := wo + ss1.toNat) (by omega)
  refine Sat.bind (Sat.of_eq esv ?_)
  refine Sat.bind (Sat.mono (qmatch_ok T (flush := flush) hn hw0 I sv) ?_)
  rintro o H2 ⟨hnone, hsome⟩
  cases o with
  | some v =>
    obtain ⟨q, m⟩ := hsome v rfl
    rw [hk1]
    exact Sat.pure ⟨q, by omega⟩
  | none =>
    obtain ⟨I2, ha2⟩ := hnone rfl
    rw [hk2]
    refine Sat.bind (Sat.mono (qlit_ok T (flush := flush) hn hw0 I2 hl sv.toUInt8) ?_)
    rintro ⟨r, ss2, la2⟩ H3 ⟨⟨q1, q2⟩, e1, e2, e3⟩
    simp only [] at e1 e2 e3 q1 q2
    subst e1 e2
    have hla2 : (la1 - 1).toNat = la1.toNat - 1 :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using hl))
    cases r with
    | true => exact Sat.pure ⟨q2 rfl, by simp [QM]⟩
    | false =>
      refine Sat.pure ⟨q1 rfl, ?_⟩
      show avIn H3 i + (la1 - 1).toNat + 1 < Mb + 1
      rw [e3, ha2, hla2]; omega

/-- One trip of the main loop (`quick_trip` with `static_emit == 0`). -/
theorem trip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {la ss last : UInt32} (flush : Int32)
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H) :
    Sat H (quick_trip (some b) (.ref (.heap b) wo) flush last 0 ss la) (fun v H2 =>
      QI h i b flush v H2 ∧ QM i v H2 < avIn H i + la.toNat + 1) := by
  unfold quick_trip
  simp only [qfp0, qsb0, ZlibNgF.Proof.DeflateAlloc.pure_bind_M, Bool.false_eq_true, ↓reduceIte,
    QuickExit.isCont, Bool.not_true]
  by_cases hl : la < MIN_LOOKAHEAD
  · simp only [hl, ↓reduceIte]
    have hl' : la.toNat < 262 := by simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.lt_iff_toNat_lt.mp hl
    refine Sat.bind (Sat.mono (sli_fill I hl') fun _ H1 h1 => Sat.bind (Sat.mono h1 ?_))
    rintro _ H2 ⟨H0, z, st, d, rfl, I2, hm1, -, -⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (rdD_SH _) ?_)))
    by_cases hx : (decide (st.lookahead < MIN_LOOKAHEAD) && flush == Z_NO_FLUSH) = true
    · simp only [hx, ↓reduceIte]
      have hf' : flush = Z_NO_FLUSH := by simp at hx; exact hx.2
      subst hf'
      exact Sat.pure ⟨slc_post (sli_slc I2) hn, by simp [QM]⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      by_cases hz : (st.lookahead == 0) = true
      · simp only [hz, ↓reduceIte]
        exact Sat.pure ⟨⟨I2, by simpa using hz⟩, by simp [QM]⟩
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have := ZlibNgF.Proof.DeflateRleP.ne0 (by simpa using hz)
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        split
        · exact tail_ok T (flush := flush) hn hw0 I2 (by omega) (by rw [avIn_SH]; omega) _ (fun _ _ => rfl) (fun _ => rfl)
        · exact tail_ok T (flush := flush) hn hw0 I2 (by omega) (by rw [avIn_SH]; omega) _ (fun _ _ => rfl) (fun _ => rfl)
  · simp only [hl, ↓reduceIte]
    have hl' : 262 ≤ la.toNat := by
      simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl)
    exact tail_ok T (flush := flush) hn hw0 I (by omega) (Nat.le_refl _) _ (fun _ _ => rfl) (fun _ => rfl)

/-- `deflate_quick` on a stream whose strategy is not `Z_FIXED` (`deflate_quick_impl(s, flush, 0)`) keeps the strategy
frame. -/
theorem quick_tally_ok (T : TreesFacts) :
    StratOkP (fun st => TableAt 1 1 st ∧ st.strategy ≠ Z_FIXED) deflate_quick := by
  intro h s b flush P hsb hE
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hE' : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.strategy ≠ Z_FIXED := fun b' st hd => by
    obtain ⟨⟨h1, -, -, -⟩, h2⟩ := hE b' st hd
    exact ⟨Int32.lt_of_lt_of_le (by decide) h1, h2⟩
  obtain ⟨st, hst, I0⟩ := sli_entry P hz hb hE'
  have hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED := fun st0 h0 =>
    (hE' b st0 ⟨i, z, rfl, hz, hb, h0⟩).2
  obtain ⟨i', z', b', st', al, e, L, -, c⟩ := live P.1
  obtain rfl : i = i' := Option.some.inj e
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans L.hz)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans L.hb)
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans L.dstate)
  obtain ⟨-, wo, -, -, -, -, hwin, -⟩ := c.lay
  simp only [dview] at hwin
  have hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo) := fun st0 h0 => by
    rw [hst] at h0; cases h0; exact hwin
  suffices S : Sat h (deflate_quick (some b) flush) (fun bs h' => StratPost h (some i) flush bs h') by
    obtain ⟨bs, h', e, q⟩ := S
    exact ⟨bs, h', e, q⟩
  unfold deflate_quick
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  have hfx : (st.strategy == Z_FIXED) = false := by simpa using hn st hst
  simp only [hfx, Bool.false_eq_true, ↓reduceIte]
  unfold deflate_quick_impl
  simp only [qsb0, ZlibNgF.Proof.DeflateAlloc.pure_bind_M, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq (rdD_app L _) (Sat.bind (Sat.of_eq (rdD_app L _) ?_)))
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (QI h i b flush) (QM i)
    (fun v H => QI h i b flush v H ∧ v.2.2.isCont = false) ?_ (s := (st.strstart, st.lookahead, .cont))
    I0 ?_) ?_)
  · rintro ⟨ss, la, ex⟩ H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases ex with
    | cont => exact Sat.mono (trip_ok T flush hn hw0 hI) fun v H2 ⟨a, m⟩ => ⟨a, by simp only [QM]; exact m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := avIn_lt h i
    have := UInt32.toNat_lt st.lookahead
    simp only [QM, fuel]; omega
  rintro ⟨ss, la, ex⟩ H ⟨hI, hc⟩
  cases ex with
  | cont => cases hc
  | ret r => exact Sat.pure hI
  | brk =>
    obtain ⟨hI, hl0⟩ := hI
    simp only []
    refine Sat.bind (Sat.mono (sli_wb hI) ?_)
    rintro _ H1 ⟨C1, -, H0, z1, st1, d1, rfl, hla, hss⟩
    refine Sat.bind (Sat.mono (slc_insert C1 _ ?_) ?_)
    · rw [hss]
      by_cases hs : ss < STD_MIN_MATCH - 1
      · simp only [hs, ↓reduceIte]; exact UInt32.le_refl _
      · simp only [hs, ↓reduceIte]; exact UInt32.not_lt.mp hs
    rintro _ H2 ⟨C2, rfl⟩
    have hwin2 : st1.window = .val (.ref (.heap b) wo) := by
      obtain ⟨st0, h0, hw⟩ := C2.1.win
      exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
    have hp2 : st1.pending = 0 := (C2.2 _ (SH_dstate _ _ _ _ _ _)).1
    have fin : ∀ (lst : Int32) (b1 b2 : BlockState), 0 ≤ lst → lst ≤ 1 →
        (lst = 0 → b1 = .need_more ∧ b2 = .block_done) → (lst = 1 → b1 = .finish_started ∧ b2 = .finish_done) →
        Sat (SH H0 i z1 b { st1 with insert := if ss < STD_MIN_MATCH - 1 then ss else STD_MIN_MATCH - 1 } d1) (do
          if ← quick_end_block (some b) ss lst 0 then return b1
          return b2) (fun r H' => StratPost h (some i) flush r H') := by
      intro lst b1 b2 hl0' hl1' h0 h1
      refine Sat.bind (Sat.mono (qeb_ok T ss lst hl0' hl1' C2.1 hp2 hwin2) ?_)
      rintro r H3 ⟨-, F3, hs3⟩
      have hb12 : (b1 = .need_more ∧ b2 = .block_done) ∨ (b1 = .finish_started ∧ b2 = .finish_done) := by
        have : lst = 0 ∨ lst = 1 := by
          have a := Int32.le_iff_toInt_le.mp hl0'; have b := Int32.le_iff_toInt_le.mp hl1'
          simp at a b
          rcases (show lst.toInt = 0 ∨ lst.toInt = 1 by omega) with e | e
          · exact .inl (Int32.toInt_inj.mp e)
          · exact .inr (Int32.toInt_inj.mp e)
        rcases this with e | e
        · exact .inl (h0 e)
        · exact .inr (h1 e)
      have post : ∀ bs, (bs = b1 ∧ r = true ∨ bs = b2 ∧ r = false) → StratPost h (some i) flush bs H3 := by
        rintro bs hbs
        refine slf_post F3 _ _ hn fun st3 h3 => ?_
        obtain ⟨e1, e2, e3, e4, e5⟩ := hs3 st3 h3
        unfold ExitOk
        refine ⟨e3, fun hd => ?_, fun _ => e5, fun _ => ⟨e5, by rw [e1]; exact hla.trans hl0⟩, fun _ => e5⟩
        rcases hbs with ⟨rfl, hr⟩ | ⟨rfl, hr⟩
        · rcases hb12 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hd with e | e <;> cases e
        · exact e4 hr
      cases r with
      | true => exact Sat.pure (post b1 (.inl ⟨rfl, rfl⟩))
      | false => exact Sat.pure (post b2 (.inr ⟨rfl, rfl⟩))
    by_cases hf : flush == Z_FINISH
    · simp only [hf, ↓reduceIte, show ((1 : UInt32) != 0) = true from rfl]
      exact fin 1 .finish_started .finish_done (by decide) (by decide) (fun e => by cases e) (fun _ => ⟨rfl, rfl⟩)
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, show ((0 : UInt32) != 0) = false from rfl]
      exact fin 0 .need_more .block_done (by decide) (by decide) (fun _ => ⟨rfl, rfl⟩) (fun e => by cases e)

end ZlibNgF.Proof.QuickP
