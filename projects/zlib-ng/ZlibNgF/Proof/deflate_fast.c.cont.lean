import ZlibNgF.Proof.«deflate_fast.c.steps»
import ZlibNgF.Proof.«deflate_quick.c.match»

/-!
# `deflate_fast`: `FLUSH_BLOCK` and the continuation loop (`ZlibNgF`)

`deflate_fast` keeps `lookahead` and `strstart` in the state; `Held b la ss H` says the state of `H` holds them, so
the loop frames `SLW` / `SLI` with the locals `la` / `ss` are those of the state itself.

* `flush0_ok`: `FLUSH_BLOCK(s, 0)` after a tally, from `SLW` of the state: the hash chains kept, `SLC` when it does
  not return, `need_more` and `StratPost` when it does;
* `ctrip_ok`, `cloop_ok`: the continuation loop of a match of `STD_MAX_MATCH` bytes (`deflate_fast.c:92-115`):
  `max_match_continues` from `strstart` at the distance of the match (at most 258 bytes, below the lookahead of at least
  `MIN_LOOKAHEAD`), the insertions of the continued positions, the tally (after a tally that may have filled the symbol
  buffer: `slw_tally_dist`, then `FLUSH_BLOCK`). The chains: `ChainOk.grow` from the start of the trip to the tally,
  after `strstart` moved past the inserted positions.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.FastCont
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InsertGrow ZlibNgF.Proof.InsertLoop ZlibNgF.Proof.InsertLoopW
open ZlibNgF.Proof.FastSteps ZlibNgF.Proof.FastFrame
open ZlibNgF.Proof.MediumStep (Sat.and)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateFast

/-- The state of `H` holds `lookahead = la` and `strstart = ss`. -/
def Held (b : Nat) (la ss : UInt32) (H : Heap) : Prop :=
  ∀ st, H.dstate b = some st → st.lookahead = la ∧ st.strstart = ss

/-- The `lookahead` of the state of block `b` in `H` (the loop measures). -/
def LaS (b : Nat) (H : Heap) : Nat :=
  match H.dstate b with
  | some st => st.lookahead.toNat
  | none => 0

theorem LaS_SH (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    LaS b (SH H0 i z b st d) = st.lookahead.toNat := by
  simp [LaS]

theorem held_SH {H0 : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} :
    Held b st.lookahead st.strstart (SH H0 i z b st d) := fun st1 h1 => by
  obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1); exact ⟨rfl, rfl⟩

/-- The level facts of the states under `SLF`, from those of the entry state. -/
theorem slf_lev {h H : Heap} {i b : Nat} (F : SLF h i b H)
    (hl : ∀ st0, h.dstate b = some st0 → st0.level = 2 ∧ HASHLESS st0.level st0.strategy = false) :
    ∀ st, H.dstate b = some st → st.level = 2 ∧ HASHLESS st.level st.strategy = false := by
  intro st hst
  obtain ⟨st0, h0, hk⟩ := F.keeps
  have K := hk st hst
  rw [K.2.2.2.2.1, K.2.2.2.2.2.1]; exact hl st0 h0

/-- The window of the state under `SLF` is the one at entry. -/
theorem slf_win {h H : Heap} {i b wo : Nat} (F : SLF h i b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    ∀ st, H.dstate b = some st → st.window = .val (.ref (.heap b) wo) := by
  intro st hst
  obtain ⟨st0, h0, hw⟩ := F.win
  exact (hw st hst).trans (hw0 st0 h0)

/-- The layout under `SLW` with the window at the entry's offset `wo`. -/
theorem slw_layw {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (W : SLW h i b la ss (SH H0 i z b st d))
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    ∃ po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho ∧ (∃ k, st.w_size.toNat = 2 ^ k) ∧
      512 ≤ st.w_size.toNat ∧ st.w_size.toNat ≤ 32768 ∧ ss.toNat + la.toNat ≤ st.window_size.toNat ∧
      st.window_size.toNat ≤ 65536 ∧ wo + st.window_size.toNat ≤ po ∧ wo + 131400 ≤ d.size := by
  obtain ⟨wo', po, ho, L, hp, a1, a2, a3, a4, a5, a6, -⟩ := slw_lay W
  have hw : st.window = .val (.ref (.heap b) wo) := by
    obtain ⟨H1, z1, st1, d1, e, F, -⟩ := W
    obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
    exact slf_win F hw0 _ (SH_dstate _ _ _ _ _ _)
  have hw' := L.win
  rw [hw] at hw'
  obtain rfl : wo = wo' := by injection hw' with e; injection e
  exact ⟨po, ho, L, hp, a1, a2, a3, a4, a5, a6⟩

/-- `FLUSH_BLOCK(s, window, 0)` after a tally, with `lookahead` / `strstart` in the state: `avail_in` and the hash
chains kept; when it does not return, `SLC` with the same `lookahead` / `strstart`; else `need_more` with
`StratPost` for any `flush`. -/
theorem flush0_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {la ss : UInt32} (W : SLW h i b la ss H)
    (hH : Held b la ss H) (Ck : CK b H)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.level ≠ 1) :
    Sat H (FLUSH_BLOCK (some b) (.ref (.heap b) wo) 0) (fun r H2 => avIn H2 i = avIn H i ∧ CK b H2 ∧
      (r = none → SLC h i b H2 ∧ Held b la ss H2) ∧
      (r ≠ none → r = some .need_more ∧ ∀ flush, StratPost h (some i) flush .need_more H2)) := by
  obtain ⟨H0, z, st, d, rfl, F0, hp0⟩ := W
  obtain ⟨e1, e2⟩ := hH st (SH_dstate _ _ _ _ _ _)
  subst e1 e2
  rw [FS_self] at F0
  have hp : ∀ st1, (SH H0 i z b st d).dstate b = some st1 → st1.pending = 0 ∧
      st1.window = .val (.ref (.heap b) wo) := fun st1 h1 => by
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    exact ⟨hp0, slf_win F0 hw0 _ (SH_dstate _ _ _ _ _ _)⟩
  refine Sat.mono (Sat.and (slf_flush T 0 (by decide) (by decide) F0 hp)
    (ZlibNgF.Proof.StrategyChain.slf_flush_chain T 0 (by decide) (by decide) F0 hp)) ?_
  rintro r H2 ⟨⟨hav, F2, hs2, hn2, hsm⟩, hck⟩
  refine ⟨hav, fun st2 d2 h2 hd2 => hck st d st2 d2 (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _) h2 hd2
    (Ck st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)), fun e => ⟨⟨F2, fun st2 h2 =>
      ⟨hn2 e st2 h2, (hs2 st2 h2).2.1⟩⟩, fun st2 h2 => ?_⟩, fun e => ⟨?_, fun flush => ?_⟩⟩
  · obtain ⟨-, -, st1, h1, e3, e4, -⟩ := hs2 st2 h2
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    exact ⟨e3, e4⟩
  · rw [hsm e]; rfl
  · refine slf_post_l F2 _ _ hn fun st2 h2 => ⟨(hs2 st2 h2).2.1, ?_, fun _ => (hs2 st2 h2).1, ?_, ?_⟩
    · intro e; rcases e with e | e <;> cases e
    · intro e; rcases e with e | e <;> cases e
    · intro e; cases e

/-! ## The continuation loop -/

/-- The invariant of the continuation loop over `(exit, bflush)`, for a match at distance `cd` and a bound `K` on
`avail_in + lookahead + 1`. -/
def CI (h : Heap) (i b : Nat) (flush : Int32) (cd : UInt32) (K : Nat) (v : Ctl × Bool) (H : Heap) : Prop :=
  match v.1 with
  | .cont => ∃ la ss, SLW h i b la ss H ∧ Held b la ss H ∧ (v.2 = false → SLI h i b la ss H) ∧
      (v.2 = true → SymLe b H) ∧ 262 ≤ la.toNat ∧ cd.toNat ≤ ss.toNat ∧ CK b H ∧ avIn H i + la.toNat + 1 ≤ K
  | .brk => ∃ la ss, SLW h i b la ss H ∧ Held b la ss H ∧ (v.2 = false → SLI h i b la ss H) ∧ CK b H ∧
      avIn H i + la.toNat + 1 ≤ K
  | .ret r => StratPost h (some i) flush r H ∧ CK b H

/-- The measure of the continuation loop. -/
def CM (b : Nat) (v : Ctl × Bool) (H : Heap) : Nat :=
  match v.1 with
  | .cont => LaS b H + 1
  | _ => 0

/-- One trip of the continuation loop. -/
theorem ctrip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {cd mi : UInt32} {K : Nat}
    {bf : Bool} {la ss : UInt32}
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.level ≠ 1)
    (hl : ∀ st0, h.dstate b = some st0 → st0.level = 2 ∧ HASHLESS st0.level st0.strategy = false)
    (hmi : 2 ≤ mi.toNat) (hd1 : 1 ≤ cd.toNat) (hd2 : cd.toNat ≤ 32768)
    (W : SLW h i b la ss H) (hH : Held b la ss H) (I : bf = false → SLI h i b la ss H) (hle : bf = true → SymLe b H)
    (hla : 262 ≤ la.toNat) (hcd : cd.toNat ≤ ss.toNat) (Ck : CK b H) (hK : avIn H i + la.toNat + 1 ≤ K) :
    Sat H (deflate_fast_cont_trip (some b) (.ref (.heap b) wo) mi cd bf) (fun v H2 =>
      CI h i b flush cd K v H2 ∧ CM b v H2 < la.toNat + 1) := by
  obtain ⟨H0, z, st, d, rfl, F0, hp0⟩ := W
  have W : SLW h i b la ss (SH H0 i z b st d) := ⟨H0, z, st, d, rfl, F0, hp0⟩
  obtain ⟨e1, e2⟩ := hH st (SH_dstate _ _ _ _ _ _)
  subst e1 e2
  obtain ⟨po, ho, L, hpw, w1, w2, hlook, h65, hwp, hbig⟩ := slw_layw W hw0
  have C0 : ChainOk b d st := Ck st d (SH_dstate _ _ _ _ _ _) (SH_bytes _ _ _ _ _ _)
  have hlev : st.level = 2 := by
    rw [FS_self] at F0; exact (slf_lev F0 hl st (SH_dstate _ _ _ _ _ _)).1
  unfold deflate_fast_cont_trip
  extract_lets bf0 jpC bf1
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.QuickP.mmc_ok (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d)
    (wo := wo) st.strstart cd (by omega) hcd) ?_)
  rintro cl _ ⟨rfl, hcl⟩
  by_cases h8 : cl < 8
  · simp only [h8, ↓reduceIte]
    exact Sat.pure ⟨⟨st.lookahead, st.strstart, W, held_SH, I, Ck, hK⟩, by simp [CM]⟩
  simp only [h8, ↓reduceIte]
  have h8' : 8 ≤ cl.toNat := by
    have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h8); simpa using this
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (sl_insert_spread (h := h) L hpw hwp w1 st.strstart cl mi (by omega) hmi
    (by omega) (by omega)) ?_)
  rintro _ _ ⟨d1, rfl, hW1, hI1, g1⟩
  have G1 := cg_ins (cg_start (H0 := H0) (i := i) (z := z) (b := b) (st := st) (d := d) (fun _ => False)) g1
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  -- the state after `strstart += cont_len; lookahead -= cont_len`
  generalize hst2 : (fun s : DeflateState => { s with lookahead := s.lookahead - cl })
    ((fun s : DeflateState => { s with strstart := s.strstart + cl }) st) = st2
  have hf : FS st2 st.lookahead st.strstart = FS st st.lookahead st.strstart := by rw [← hst2]
  have k2 : st2.lookahead = st.lookahead - cl ∧ st2.strstart = st.strstart + cl ∧ CF st st2 ∧
      st2.sym_next = st.sym_next ∧ st2.window = st.window := by
    rw [← hst2]; exact ⟨rfl, rfl, CF.refl _, rfl, rfl⟩
  have G2 := cg_st G1 k2.2.2.1
  have W2 : SLW h i b st.lookahead st.strstart (SH H0 i z b st2 d1) := slw_wr (hW1 _ _ W) hf
  have hla2 : (st.lookahead - cl).toNat = st.lookahead.toNat - cl.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have hss2 : (st.strstart + cl).toNat = st.strstart.toNat + cl.toNat := by rw [UInt32.toNat_add]; omega
  have hsub : (cl - STD_MIN_MATCH).toNat = cl.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp [STD_MIN_MATCH]; omega))
  -- after the tally: the chains, `Held`, the measure
  have post : ∀ (bfl : Bool) (H3 : Heap), SLW h i b (st.lookahead - cl) (st.strstart + cl) H3 →
      (bfl = false → SLI h i b (st.lookahead - cl) (st.strstart + cl) H3) →
      avIn H3 i = avIn (SH H0 i z b st2 d1) i →
      (∃ st3 d3 lo hi, H3 = SH H0 i z b st3 d3 ∧ TK st2 st3 ∧ ZlibNgF.Proof.DeflateBits.WrIn d1 lo hi d3 ∧
        ∀ ho, st2.head = .val (.ref (.heap b) ho) → ho + 131072 ≤ lo) →
      Sat H3 (if bfl = true then do
          let __do_lift ← FLUSH_BLOCK (some b) (.ref (.heap b) wo) 0
          match __do_lift with
            | some r => pure (Ctl.ret r, bfl)
            | none => jpC () bf1
        else jpC () bfl) (fun v H2 => CI h i b flush cd K v H2 ∧ CM b v H2 < st.lookahead.toNat + 1) := by
    intro bfl H3 W3 I3 hav3 ⟨st3, d3, lo, hi, e3, K3, Wr3, hlo⟩
    subst e3
    have G3 := cg_tally W2 G2 K3 Wr3 hlo
    have hH3 : Held b (st.lookahead - cl) (st.strstart + cl) (SH H0 i z b st3 d3) := fun st4 h4 => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h4)
      exact ⟨K3.2.2.1.trans k2.1, K3.2.1.trans k2.2.1⟩
    have Ck3 : CK b (SH H0 i z b st3 d3) := ck_of_cg C0 G3 hlev fun st4 h4 => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h4)
      rw [K3.2.1, k2.2.1, hss2]
      exact ⟨by omega, fun q hq _ => by rcases hq with hq | hq; · exact absurd hq id; · omega⟩
    have hav3' : avIn (SH H0 i z b st3 d3) i = avIn (SH H0 i z b st d) i := by
      rw [hav3, avIn_SH, avIn_SH]
    -- the end of the trip, after `FLUSH_BLOCK` or none
    have jp : ∀ H4, SLI h i b (st.lookahead - cl) (st.strstart + cl) H4 →
        Held b (st.lookahead - cl) (st.strstart + cl) H4 → CK b H4 → avIn H4 i = avIn (SH H0 i z b st d) i →
        Sat H4 (jpC () false) (fun v H2 => CI h i b flush cd K v H2 ∧ CM b v H2 < st.lookahead.toNat + 1) := by
      intro H4 I4 hH4 Ck4 hav4
      obtain ⟨H5, z5, st5, d5, rfl, C5⟩ := I4
      obtain ⟨e5, e6⟩ := hH4 st5 (SH_dstate _ _ _ _ _ _)
      simp only [jpC]
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      rw [e5]
      have hIa : SLI h i b (st.lookahead - cl) (st.strstart + cl) (SH H5 i z5 b st5 d5) := ⟨H5, z5, st5, d5, rfl, C5⟩
      have hav5 : avIn (SH H5 i z5 b st5 d5) i + (st.lookahead - cl).toNat + 1 ≤ K := by
        rw [hav4, hla2]; omega
      by_cases hl2 : st.lookahead - cl < MIN_LOOKAHEAD
      · simp only [hl2, ↓reduceIte]
        exact Sat.pure ⟨⟨_, _, sli_slw hIa, hH4, fun _ => hIa, Ck4, hav5⟩, by simp [CM]⟩
      · simp only [hl2, ↓reduceIte]
        have hl2' : 262 ≤ (st.lookahead - cl).toNat := by
          have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl2)
          simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
        refine Sat.pure ⟨⟨_, _, sli_slw hIa, hH4, fun _ => hIa, fun e => by cases e, hl2', by omega, Ck4, hav5⟩, ?_⟩
        simp only [CM, LaS_SH]; rw [e5]; omega
    cases bfl with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact jp _ (I3 rfl) hH3 Ck3 hav3'
    | true =>
      simp only [↓reduceIte]
      refine Sat.bind (Sat.mono (flush0_ok T W3 hH3 Ck3 hw0 hn) ?_)
      rintro r H4 ⟨hav4, Ck4, hnone, hsome⟩
      cases r with
      | none =>
        obtain ⟨C4, hH4⟩ := hnone rfl
        obtain ⟨z4, st4, -, -, -, hst4, -, -⟩ := C4.1.live
        have I4 := sli_of_slc C4 hst4
        rw [(hH4 st4 hst4).1, (hH4 st4 hst4).2] at I4
        simp only []
        exact jp _ I4 hH4 Ck4 (by rw [hav4, hav3'])
      | some v =>
        obtain ⟨e, hP⟩ := hsome (by simp)
        obtain rfl := Option.some.inj e
        exact Sat.pure ⟨⟨hP flush, Ck4⟩, by simp [CM]⟩
  cases bf with
  | false =>
    have I2 : SLI h i b st.lookahead st.strstart (SH H0 i z b st2 d1) := sli_wr (hI1 _ _ (I rfl)) hf
    have hlt : st2.sym_next ≤ st2.sym_end := by
      obtain ⟨H5, z5, st5, d5, e, C⟩ := I2
      obtain ⟨rfl, rfl, rfl⟩ := SH_inj e
      exact UInt32.le_of_lt (C.2 _ (SH_dstate _ _ _ _ _ _)).2
    refine Sat.bind (Sat.mono (Sat.and (sli_tally_dist_le I2 cd (cl - STD_MIN_MATCH) cl (by omega) hd1 hd2
      (by omega) hcl (by omega)) (tally_dist_K W2 hlt cd (cl - STD_MIN_MATCH) (by omega) hd1 hd2)) ?_)
    rintro r H3 ⟨⟨hav3, W3, -, -, I3⟩, K3⟩
    exact post (false || r) H3 W3 (fun e => I3 (by simpa using e)) hav3 K3
  | true =>
    have hle2 : SymLe b (SH H0 i z b st2 d1) := fun st4 h4 => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h4)
      rw [k2.2.2.2.1]; exact hle rfl st (SH_dstate _ _ _ _ _ _)
    refine Sat.bind (Sat.mono (Sat.and (slw_tally_dist W2 hle2 cd (cl - STD_MIN_MATCH) cl (by omega) hd1 hd2
      (by omega) hcl (by omega)) (tally_dist_K W2 (hle2 _ (SH_dstate _ _ _ _ _ _)) cd (cl - STD_MIN_MATCH)
        (by omega) hd1 hd2)) ?_)
    rintro r H3 ⟨⟨hav3, W3, -⟩, K3⟩
    exact post (true || r) H3 W3 (fun e => by simp at e) hav3 K3

end ZlibNgF.Proof.FastCont
