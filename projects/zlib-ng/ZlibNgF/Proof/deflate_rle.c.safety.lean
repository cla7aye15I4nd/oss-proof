import ZlibNgF.Proof.«deflate_huff.c.safety»
import ZlibNgF.ZlibNg.«deflate_rle.c»

/-!
# `deflate_rle` (`ZlibNgF`)

`rle_ok`: the `Z_RLE` strategy keeps the strategy frame (`StratOkP`), given the block emitters (`TreesFacts`). A trip
refills the window when at most `STD_MAX_MATCH` bytes are left (`sli_fill`), looks for a run of the byte before
`strstart` (`compare256_rle_64` reads at most 259 bytes from `strstart - 1`, all in the stream's block: the window is
followed by `prev`), and tallies a match of distance 1 and length `MIN(run, lookahead)` (3..258) or a literal. The
`zng_ctz64` count of a non-zero word is at most 64 (`ctz64_le`), so the run is at most 256 + 2.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateRleP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateRle

/-! ## `zng_ctz64` -/

theorem forIn_cnt (l : List Nat) (n : UInt32) (v : UInt64) (hn : n.toNat + l.length < 2 ^ 32) :
    (Id.run (forIn (m := Id) l ((n, v) : UInt32 × UInt64) (fun _ r =>
      if r.2 &&& 1 == 0 then ForInStep.yield (r.1 + 1, r.2 >>> 1) else ForInStep.yield (r.1, r.2)))).1.toNat ≤
      n.toNat + l.length := by
  induction l generalizing n v with
  | nil => simp [Id.run, pure]
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons]
    split <;> simp only [Id.run, bind] at ih ⊢
    · have := ih (n + 1) (v >>> 1) (by rw [UInt32.toNat_add]; simp at hn ⊢; omega)
      rw [UInt32.toNat_add] at this; simp at this ⊢; omega
    · have := ih n v (by simp at hn ⊢; omega)
      omega

/-- `__builtin_ctzll` of a non-zero word counts at most 64 zeros and leaves the heap. -/
theorem ctz64_le (x : UInt64) (hx : x ≠ 0) (H : Heap) :
    ∃ r, zng_ctz64 x H = .ok (r, H) ∧ r.toNat ≤ 64 := by
  unfold zng_ctz64
  have h0 : (x == 0) = false := by simpa using hx
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_cnt (List.range' 0 64 1) 0 x (by simp)

/-- `zng_first_diff_byte64` of a non-zero word is at most 8. -/
theorem fdb_sat (x : UInt64) (hx : x ≠ 0) (H : Heap) :
    Sat H (zng_first_diff_byte64 x) (fun r H' => H' = H ∧ r.toNat ≤ 8) := by
  obtain ⟨r, e, hr⟩ := ctz64_le x hx H
  unfold zng_first_diff_byte64
  refine Sat.bind (Sat.of_eq e (Sat.pure ⟨rfl, ?_⟩))
  rw [UInt32.toNat_div]; simp; omega

/-! ## `compare256_rle_64` -/

/-- `compare256_rle(scan, scan + 3)` with 259 bytes from `scan` in block `b`: no fault, the heap kept, at most 256. -/
theorem cmp_rle_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {off : Nat}
    (hk : off + 259 ≤ d.size) :
    Sat (SH H i z b st d) (compare256_rle (.ref (.heap b) off) (.ref (.heap b) (off + 3))) (fun r H' =>
      H' = SH H i z b st d ∧ r.toNat ≤ 256) := by
  unfold compare256_rle compare256_rle_64
  obtain ⟨v2, e2⟩ := ZlibNgF.Proof.WinBase.memread2_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := off) (by omega)
  refine Sat.bind (Sat.of_eq e2 ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cdoWhileH
    (fun (s : BPtr × UInt32 × Option UInt32) H' => H' = SH H i z b st d ∧ ∃ l : Nat,
      s.1 = .ref (.heap b) (off + 3 + l) ∧ s.2.1.toNat = l ∧ l % 8 = 0 ∧ l ≤ 248 ∧ s.2.2 = none)
    (fun s _ => 256 - s.2.1.toNat)
    (fun s H' => H' = SH H i z b st d ∧ ∀ v, s.2.2 = some v → v.toNat ≤ 256) ?_
    (s := (.ref (.heap b) (off + 3), 0, none)) ⟨rfl, 0, rfl, rfl, rfl, by decide, rfl⟩ (by simp [fuel])) ?_)
  · rintro ⟨src1, len, r⟩ H' ⟨rfl, l, h1, h2, hm, hle, h3⟩
    simp only [] at h1 h2 h3
    subst h1 h3
    obtain ⟨mv, em⟩ := ZlibNgF.Proof.WinBase.memread8_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d)
      (off := off + 3 + l) (by omega)
    simp only []
    refine Sat.bind (Sat.of_eq em ?_)
    generalize (((v2.toUInt32 <<< 16 ||| v2.toUInt32).toUInt64 <<< 32 |||
      (v2.toUInt32 <<< 16 ||| v2.toUInt32).toUInt64) ^^^ mv) = df
    by_cases hd : df = 0
    · have : (df != 0) = false := by simp [hd]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 8 (by omega)) (Sat.pure (Sat.pure ?_)))
      simp only [Option.isNone_none, Bool.true_and]
      have h8 : (len + 8).toNat = l + 8 := by rw [UInt32.toNat_add]; simp; omega
      refine ⟨fun hc => ⟨⟨by simp, l + 8, by simp [Nat.add_assoc], h8, by omega, ?_, by simp⟩, by rw [h8]; omega⟩,
        fun _ => ⟨by simp, fun v e => by simp at e⟩⟩
      have : (len + 8).toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using hc
      omega
    · have : (df != 0) = true := by simp [hd]
      simp only [this, ↓reduceIte]
      refine Sat.bind (Sat.mono (fdb_sat df hd _) ?_)
      rintro f _ ⟨rfl, hf⟩
      refine Sat.pure (Sat.pure ⟨fun e => by simp at e, fun _ => ⟨rfl, fun v e => ?_⟩⟩)
      simp only [Option.some.injEq] at e
      subst e
      rw [UInt32.toNat_add]; omega
  · rintro ⟨src1, len, r⟩ H' ⟨rfl, hr⟩
    cases r with
    | none => exact Sat.pure ⟨rfl, by decide⟩
    | some v => exact Sat.pure ⟨rfl, hr v rfl⟩

/-! ## The loop -/

theorem addZ_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {off : Nat}
    (k : Int) (h0 : 0 ≤ (off : Int) + k) (hk : (off : Int) + k ≤ d.size) (hoff : off ≤ d.size) :
    Ptr.add (Ptr.ref (BRef.heap b) off) k (SH H i z b st d) =
      .ok (.ref (.heap b) ((off : Int) + k).toNat, SH H i z b st d) := by
  simp only [Ptr.add, ZlibNgF.Proof.InflateAlloc.space_get_heap, SH_bytes, hoff, h0, hk, and_self, ↓reduceIte]

/-- The window, the bytes `[strstart, strstart + lookahead)` of the local copy, and 259 bytes from `strstart` lie in
block `b` (the window is followed by `prev`, at least 1024 bytes). -/
theorem sli_win2 {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d))
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    st.window = .val (.ref (.heap b) wo) ∧ wo + ss.toNat + la.toNat ≤ d.size ∧ wo + ss.toNat + 259 ≤ d.size := by
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
  have hws : 512 ≤ st.w_size.toNat := c.sizes.1
  exact ⟨hwin, by omega, by omega⟩

/-- The loop state's invariant. -/
def RI (h : Heap) (i b : Nat) (flush : Int32) (v : UInt32 × UInt32 × UInt32 × RleExit) (H : Heap) : Prop :=
  match v.2.2.2 with
  | .ret r => StratPost h (some i) flush r H
  | .brk => SLI h i b v.1 v.2.1 H ∧ v.1 = 0
  | .cont => SLI h i b v.1 v.2.1 H ∧ v.2.2.1.toNat < 3

/-- The loop measure. -/
def RM (i : Nat) (v : UInt32 × UInt32 × UInt32 × RleExit) (H : Heap) : Nat :=
  match v.2.2.2 with
  | .cont => avIn H i + v.1.toNat + 1
  | _ => 0

theorem ne0 {x : UInt32} (hx : (x == 0) = false) : x.toNat ≠ 0 := fun e => by
  have : x = 0 := UInt32.toNat_inj.mp (by rw [e]; rfl)
  simp [this] at hx

/-- One trip of the loop. -/
theorem trip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {la ss ml : UInt32} (flush : Int32)
    (I : SLI h i b la ss H) (hml : ml.toNat < 3)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hfx : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED) :
    Sat H (rle_trip (some b) (.ref (.heap b) wo) flush la ss ml) (fun v H2 =>
      RI h i b flush v H2 ∧ RM i v H2 < avIn H i + la.toNat + 1) := by
  unfold rle_trip
  extract_lets jpE jpM
  have hE : ∀ (bf : Bool) (la' ss' ml' : UInt32) H2, SLW h i b la' ss' H2 → (bf = false → SLI h i b la' ss' H2) →
      ml'.toNat < 3 → avIn H2 i + la'.toNat + 1 < avIn H i + la.toNat + 1 →
      Sat H2 (jpE (bf, la', ss', ml')) (fun v H2 => RI h i b flush v H2 ∧ RM i v H2 < avIn H i + la.toNat + 1) := by
    intro bf la' ss' ml' H2 W2 I2 hm2 hlt
    simp only [jpE]
    cases bf with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Sat.pure ⟨⟨I2 rfl, hm2⟩, hlt⟩
    | true =>
      simp only [↓reduceIte]
      refine Sat.bind (Sat.mono (sli_flush T 0 (by decide) (by decide) W2 hw0) fun _ H3 h3 =>
        Sat.bind (Sat.mono h3 ?_))
      rintro r2 H4 ⟨ha4, hnone, hsome⟩
      cases r2 with
      | none => exact Sat.pure ⟨⟨hnone rfl, hm2⟩, by simp only [RM]; rw [ha4]; exact hlt⟩
      | some v =>
        obtain ⟨hv, F4, hs4⟩ := hsome (by simp)
        have hv' : v = .need_more := by simpa using hv
        subst hv'
        refine Sat.pure ⟨slf_post F4 _ _ hfx fun st4 h4 => ⟨(hs4 st4 h4).2, ?_, fun _ => (hs4 st4 h4).1, ?_,
          ?_⟩, by simp [RM]⟩
        · intro e; rcases e with e | e <;> cases e
        · intro e; rcases e with e | e <;> cases e
        · intro e; cases e
  have hM : ∀ (la1 ss1 : UInt32) H1, SLI h i b la1 ss1 H1 → 1 ≤ la1.toNat →
      avIn H1 i + la1.toNat ≤ avIn H i + la.toNat →
      Sat H1 (jpM (la1, ss1, .cont)) (fun v H2 => RI h i b flush v H2 ∧ RM i v H2 < avIn H i + la.toNat + 1) := by
    intro la1 ss1 H1 I1 hl1 hm
    simp -zeta only [jpM, RleExit.isCont, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    extract_lets jpL
    obtain ⟨H0, z, st, d, rfl, C⟩ := I1
    obtain ⟨hwin, hwd, hw259⟩ := sli_win2 ⟨H0, z, st, d, rfl, C⟩ hw0
    rw [avIn_SH] at hm
    have hL : ∀ m : UInt32, (3 ≤ m.toNat → m.toNat ≤ 258 ∧ m.toNat ≤ la1.toNat) →
        Sat (SH H0 i z b st d) (jpL m) (fun v H2 => RI h i b flush v H2 ∧ RM i v H2 < avIn H i + la.toNat + 1) := by
      intro m hm3
      simp only [jpL]
      by_cases h3 : m ≥ STD_MIN_MATCH
      · simp only [h3, ↓reduceIte]
        have h3' : 3 ≤ m.toNat := UInt32.le_iff_toNat_le.mp h3
        obtain ⟨hm258, hmla⟩ := hm3 h3'
        have hsub : (m - STD_MIN_MATCH).toNat = m.toNat - 3 := UInt32.toNat_sub_of_le _ _ h3
        refine Sat.bind (Sat.mono (sli_tally_dist ⟨H0, z, st, d, rfl, C⟩ 1 (m - STD_MIN_MATCH) m
          (by rw [hsub]; omega) (by decide) (by decide) (by omega) hm258 hmla) ?_)
        rintro r H2 ⟨ha2, W2, I2⟩
        refine Sat.bind (Sat.pure ?_)
        refine hE r _ _ 0 H2 W2 I2 (by decide) ?_
        rw [ha2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hmla), avIn_SH]; omega
      · simp only [h3, ↓reduceIte]
        obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
          (off := wo) (ss1.toNat : Int) (by omega) (by simp; omega)
        have h3' : m.toNat < 3 := by
          have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp h3); simpa [STD_MIN_MATCH] using this
        refine Sat.bind (Sat.of_eq ec (Sat.bind (Sat.mono (sli_tally_lit ⟨H0, z, st, d, rfl, C⟩ hl1 c) ?_)))
        rintro r H2 ⟨ha2, W2, I2⟩
        refine Sat.bind (Sat.pure ?_)
        refine hE r _ _ m H2 W2 I2 h3' ?_
        rw [ha2, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using hl1)), avIn_SH]; simp; omega
    by_cases hc : (decide (la1 ≥ STD_MIN_MATCH) && decide (ss1 > 0)) = true
    · simp only [hc, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hl3, hs0⟩ := hc
      have hl3' : 3 ≤ la1.toNat := UInt32.le_iff_toNat_le.mp hl3
      have hs0' : 0 < ss1.toNat := UInt32.lt_iff_toNat_lt.mp hs0
      refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss1.toNat (by omega)) ?_)
      refine Sat.bind (Sat.of_eq (addZ_SH (-1) (by omega) (by omega) (by omega)) ?_)
      have ho : ((↑(wo + ss1.toNat) : Int) + -1).toNat = wo + ss1.toNat - 1 := by omega
      rw [ho]
      obtain ⟨c0, e0⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
        (off := wo + ss1.toNat - 1) 0 (by decide) (by simp; omega)
      obtain ⟨c1, e1⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
        (off := wo + ss1.toNat - 1) 1 (by decide) (by simp; omega)
      obtain ⟨c2, e2⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
        (off := wo + ss1.toNat - 1) 2 (by decide) (by simp; omega)
      refine Sat.bind (Sat.of_eq e0 (Sat.bind (Sat.of_eq e1 ?_)))
      by_cases he : (c0 == c1) = true
      · simp only [he, ↓reduceIte]
        refine Sat.bind (Sat.of_eq e1 (Sat.bind (Sat.of_eq e2 (Sat.bind (Sat.pure ?_)))))
        by_cases he2 : (c1 == c2) = true
        · simp only [he2, ↓reduceIte]
          refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 3 (by omega)) ?_)
          refine Sat.bind (Sat.mono (cmp_rle_SH (off := wo + ss1.toNat - 1) (by omega)) ?_)
          rintro r _ ⟨rfl, hr⟩
          refine Sat.bind (Sat.pure ?_)
          refine hL _ fun h3 => ?_
          have hr2 : (r + 2).toNat = r.toNat + 2 := by rw [UInt32.toNat_add]; simp; omega
          by_cases hg : r + 2 > la1
          · simp only [hg, ↓reduceIte] at h3 ⊢
            have := UInt32.lt_iff_toNat_lt.mp hg
            exact ⟨by omega, Nat.le_refl _⟩
          · simp only [hg, ↓reduceIte] at h3 ⊢
            have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hg)
            omega
        · simp only [he2, Bool.false_eq_true, ↓reduceIte]
          exact Sat.bind (Sat.pure (hL ml fun h3 => by omega))
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact Sat.bind (Sat.pure (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Sat.bind (Sat.pure (hL ml fun h3 => by omega))))
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact Sat.bind (Sat.pure (hL ml fun h3 => by omega))
  by_cases hl : la ≤ STD_MAX_MATCH
  · simp only [hl, ↓reduceIte]
    have hl' : la.toNat ≤ 258 := UInt32.le_iff_toNat_le.mp hl
    refine Sat.bind (Sat.mono (sli_fill I (by omega)) fun _ H1 h1 => Sat.bind (Sat.mono h1 ?_))
    rintro _ H2 ⟨H0, z, st, d, rfl, I2, hm1, -, -⟩
    refine Sat.bind (Sat.of_eq (rdD_SH _) (Sat.bind (Sat.of_eq (rdD_SH _) ?_)))
    by_cases hx : (decide (st.lookahead ≤ STD_MAX_MATCH) && flush == Z_NO_FLUSH) = true
    · simp only [hx, ↓reduceIte]
      have hf' : flush = Z_NO_FLUSH := by simp at hx; exact hx.2
      subst hf'
      exact Sat.pure ⟨slc_post (sli_slc I2) hfx, by simp [RM]⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      by_cases hz : (st.lookahead == 0) = true
      · simp only [hz, ↓reduceIte]
        exact Sat.pure ⟨⟨I2, by simpa using hz⟩, by simp [RM]⟩
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have := ne0 (by simpa using hz)
        refine Sat.bind (Sat.pure (hM _ _ _ I2 (by omega) ?_))
        rw [avIn_SH]; omega
  · simp only [hl, ↓reduceIte]
    have hl' : 258 < la.toNat := by
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hl); simpa [STD_MAX_MATCH] using this
    exact Sat.bind (Sat.pure (hM _ _ _ I (by omega) (Nat.le_refl _)))

/-- `deflate_rle` keeps the strategy frame. -/
theorem rle_ok (T : TreesFacts) :
    StratOkP (fun st => 0 < st.level ∧ st.strategy = Z_RLE) deflate_rle := by
  intro h s b flush P hsb hE
  obtain ⟨z, ⟨i, rfl, hz⟩, hb⟩ := hsb
  have hE' : ∀ b' st, DStateIs h (some i) b' st → 0 < st.level ∧ st.strategy ≠ Z_FIXED := fun b' st hd => by
    obtain ⟨h1, h2⟩ := hE b' st hd; exact ⟨h1, by rw [h2]; decide⟩
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
  suffices S : Sat h (deflate_rle (some b) flush) (fun bs h' => StratPost h (some i) flush bs h') by
    obtain ⟨bs, h', e, q⟩ := S
    exact ⟨bs, h', e, q⟩
  unfold deflate_rle
  refine Sat.bind (Sat.of_eq (rdD_app L _) ?_)
  rw [hwin]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdD_app L _) (Sat.bind (Sat.of_eq (rdD_app L _) ?_)))
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.WinInv.sat_cwhileH (RI h i b flush) (RM i)
    (fun v H => RI h i b flush v H ∧ v.2.2.2.isCont = false) ?_ (s := (st.lookahead, st.strstart, 0, .cont))
    ⟨I0, show (0 : UInt32).toNat < 3 by decide⟩ ?_) ?_)
  · rintro ⟨la, ss, ml, ex⟩ H hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases ex with
    | cont =>
      exact Sat.mono (trip_ok T flush hI.1 hI.2 hw0 hn) fun v H2 ⟨a, m⟩ => ⟨a, by simp only [RM]; exact m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := avIn_lt h i
    have := UInt32.toNat_lt st.lookahead
    simp only [RM, fuel]; omega
  rintro ⟨la, ss, ml, ex⟩ H ⟨hI, hc⟩
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

end ZlibNgF.Proof.DeflateRleP
