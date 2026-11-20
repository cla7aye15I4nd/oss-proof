import ZlibNgF.Proof.«deflate_slow.c.step»

/-!
# `deflate_slow`: the emission after the match search (`ZlibNgF`)

`slowC_ok`: from the state after the match search (`CPre`: the loop frame, the hash chains with `strstart` one past
the inserted position, a non-empty lookahead, the pending match and literal of `LazyOk`, the kept match length of
`SlowLazy.ml_cases`), `slowC` ends the trip with the loop invariant (`RI`) and a smaller measure (`RM`). Its three
branches: the pending match is emitted (`slowDist_ok`: tally, insertions inside the match, `strstart` past it,
`FLUSH_BLOCK` on a full symbol buffer); the pending literal is emitted (`slowLit_ok`: tally, `FLUSH_BLOCK_ONLY` on a
full buffer, `need_more` on a full output); or the byte at `strstart` waits (`slowElse_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowEmit
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.SlowFrame ZlibNgF.Proof.SlowStep
open ZlibNg.DeflateP ZlibNg.DeflateSlow

/-- What `slowC` needs of the state `sA` after the match search (heap `SH H0 i z b sA dA`), with the kept match
length `ml` and the bound `M0` of the measure. -/
structure CPre (h : Heap) (i b wo : Nat) (level : Int32) (ml : UInt32) (M0 : Nat) (H0 : Heap) (z : ZStream)
    (sA : DeflateState) (dA : Array UInt8) : Prop where
  env : Env h b wo level
  slc : SLC h i b (SH H0 i z b sA dA)
  ch : ChainOk b dA { sA with strstart := sA.strstart + 1 }
  la1 : 1 ≤ sA.lookahead.toNat
  pend : 3 ≤ sA.prev_length → sA.prev_length.toNat ≤ 258 ∧ sA.prev_length.toNat ≤ sA.lookahead.toNat + 1 ∧
    sA.prev_match.toNat + 1 < sA.strstart.toNat ∧ sA.strstart.toNat - 1 - sA.prev_match.toNat ≤ (MAX_DIST sA).toNat
  lit : sA.match_available ≠ 0 → 1 ≤ sA.strstart.toNat ∧ sA.block_start.toInt < sA.strstart.toNat
  mlk : 3 ≤ ml → (3 ≤ sA.prev_length ∧ ml ≤ sA.prev_length) ∨ (ml.toNat ≤ 258 ∧ ml.toNat ≤ sA.lookahead.toNat ∧
    sA.match_start.toNat < sA.strstart.toNat ∧ sA.strstart.toNat - sA.match_start.toNat ≤ (MAX_DIST sA).toNat)
  meas : z.avail_in.toNat + sA.lookahead.toNat ≤ M0

/-- `ChainOk` of `X` (the tables of the `SLF` state `st`) carries to `X'` with the same tables and a larger `strstart`,
and to bytes equal before `pending_buf`. -/
theorem chain_keep {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    {X X' : DeflateState} (F : SLF h i b (SH H0 i z b st d)) (C : ChainOk b d X) (hT : TableAt 7 9 st)
    (e1 : X.level = st.level) (e3 : X.head = st.head) (e4 : X.prev = st.prev) (e5 : X.w_size = st.w_size)
    (f1 : X'.level = X.level) (f2 : X'.strategy = X.strategy) (f3 : X'.head = X.head) (f4 : X'.prev = X.prev)
    (f5 : X'.w_size = X.w_size) (hss : X.strstart.toNat ≤ X'.strstart.toNat)
    (hb : ∀ pbo, st.pending_buf = .val (.ref (.heap b) pbo) → ∀ j, j < pbo → d'[j]! = d[j]!) : ChainOk b d' X' := by
  obtain ⟨wo, po, ho, pbo, L, -, -, -, hpb, hhp, -⟩ := slf_lay F
  have w1 := (slf_nums F).2.2.2.2.1
  have hph := L.ph
  refine chain_tr C f1 f2 f3 f4 f5 hss (by rw [e1]; exact (tab_lv hT).2.2) (by rw [e5]; omega)
    fun ho' po' hh hp => ?_
  rw [e3, L.head] at hh; rw [e4, L.prev] at hp
  obtain rfl : ho = ho' := by injection hh with e; injection e
  obtain rfl : po = po' := by injection hp with e; injection e
  exact ⟨by rw [e5]; exact hph, fun j hj => hb pbo hpb j (by omega)⟩

theorem toNat_add1 {x : UInt32} (h : x.toNat ≤ 65536) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]; simp; omega

theorem toNat_sub1 {x : UInt32} (h : 1 ≤ x.toNat) : (x - 1).toNat = x.toNat - 1 :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa using h))

theorem lf_ne {st : DeflateState} (h : 0 ≤ st.last_flush) : st.last_flush ≠ -2 := fun e => by
  rw [e] at h; exact absurd h (by decide)

/-! ## No pending literal -/

/-- `slowElse`: the byte at `strstart` waits (`match_available = 1`, `prev_length = match_len`). -/
theorem slowElse_ok {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sA : DeflateState} {dA : Array UInt8}
    {level : Int32} {ml : UInt32} {M0 : Nat} (flush : Int32) (P : CPre h i b wo level ml M0 H0 z sA dA)
    (hn : ¬ (3 ≤ sA.prev_length ∧ ml ≤ sA.prev_length)) :
    Sat (SH H0 i z b sA dA) (slowElse (some b) ml) (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, hbs, hins, w1, -, -, -⟩ := slf_nums P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 sA (SH_dstate _ _ _ _ _ _)
  have hss1 := toNat_add1 (x := sA.strstart) (by omega)
  have hla1 := toNat_sub1 P.la1
  have hm := P.meas
  have hl1 := P.la1
  unfold slowElse
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sA with prev_length := ml }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sA with prev_length := ml, match_available := 1 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _
    (st' := { sA with prev_length := ml, match_available := 1, strstart := sA.strstart + 1 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sA with
    prev_length := ml, match_available := 1, strstart := sA.strstart + 1, lookahead := sA.lookahead - 1 }) rfl) ?_)
  have F1 := slf_view (st' := { sA with prev_length := ml, match_available := 1 }) P.slc.1 rfl rfl rfl hT
  have F2 := slf_move F1 (sA.strstart + 1) (sA.lookahead - 1) (by show _ ≤ sA.window_size.toNat; omega)
    (by show sA.block_start.toInt ≤ _; omega) (UInt32.le_iff_toNat_le.mpr (by
      have := UInt32.le_iff_toNat_le.mp hins; show sA.insert.toNat ≤ _; omega))
    (fun e => absurd e (by show ¬ _ = sA.block_start.toInt; omega))
  refine Sat.pure ⟨⟨slc_of F2 hp0 hsym, fun st d hst hd => ?_⟩, ?_⟩
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd)
    refine ⟨chain_keep P.slc.1 P.ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun _ _ _ _ => rfl, ?_⟩
    refine ZlibNgF.Proof.SlowLazy.lazy_step sA.strstart.toNat sA.lookahead.toNat hss1 (by
      show (sA.lookahead - 1).toNat + 1 = _; omega) hT (lf_ne hlf) (by show sA.block_start.toInt ≤ _; omega)
      fun h3 => ?_
    rcases P.mlk h3 with ⟨a1, a2⟩ | ⟨a1, a2, a3, a4⟩
    · exact absurd ⟨a1, a2⟩ hn
    · exact ⟨a1, a2, a3, a4⟩
  · simp only [RM, avIn_SH, laOf_SH]
    omega

/-! ## The pending literal -/

/-- An `SLF` heap is an `SH` heap. -/
theorem slf_sh {h H : Heap} {i b : Nat} (F : SLF h i b H) : ∃ H1 z st d, H = SH H1 i z b st d := by
  obtain ⟨z, st, al, hz, hb, hst, -, -⟩ := F.live
  obtain ⟨d, hd⟩ := bytes_of_dstate hst
  exact ⟨H, z, st, d, (ZlibNgF.Proof.DeflateReset.SH_self hz (dstates_of_dstate hst hd) hd).symm⟩

/-- `rdD` on an `SH` heap, with the value named. -/
theorem rdD_SH_eq {α : Type} {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}
    (f : DeflateState → α) {a : α} (e : f st = a) : rdD (some b) f (SH H i z b st d) = .ok (a, SH H i z b st d) := by
  rw [rdD_SH, e]

/-- `slowLit2`: after the tally of the pending literal (and `FLUSH_BLOCK_ONLY` on a full buffer), `prev_length =
match_len`, `strstart` and `lookahead` moved by one, and `need_more` on a full output. -/
theorem slowLit2_ok {h H1 : Heap} {i b wo : Nat} {z1 : ZStream} {sB : DeflateState} {dB : Array UInt8}
    {level : Int32} (flush : Int32) (ml : UInt32) (M0 ss la : Nat) (E : Env h b wo level)
    (F : SLF h i b (SH H1 i z1 b sB dB)) (hss : sB.strstart.toNat = ss) (hla : sB.lookahead.toNat = la)
    (hl1 : 1 ≤ la) (hbs : sB.block_start.toInt ≤ ss) (hpz : z1.avail_out ≠ 0 → sB.pending = 0)
    (hsym : sB.sym_next < sB.sym_end) (Ch : ChainOk b dB { sB with strstart := sB.strstart + 1 })
    (hml : 3 ≤ ml → ml.toNat ≤ 258 ∧ ml.toNat ≤ la ∧ sB.match_start.toNat < ss ∧
      ss - sB.match_start.toNat ≤ (MAX_DIST sB).toNat)
    (hm : z1.avail_in.toNat + la ≤ M0) :
    Sat (SH H1 i z1 b sB dB) (slowLit2 (some b) ml) (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st E F
  obtain ⟨hlook, h65, -, hins, w1, -, -, -⟩ := slf_nums F
  have hss1 := toNat_add1 (x := sB.strstart) (by omega)
  have hla1 := toNat_sub1 (x := sB.lookahead) (by omega)
  obtain ⟨z2, st2, al, hz2, -, hst2, -, c⟩ := F.live
  obtain rfl : z1 = z2 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz2)
  obtain rfl : sB = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  have hsm : sB.strm = .val (some i) := c.strm
  unfold slowLit2
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with prev_length := ml }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with prev_length := ml, strstart := sB.strstart + 1 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with
    prev_length := ml, strstart := sB.strstart + 1, lookahead := sB.lookahead - 1 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH_eq _ (a := .val (some i)) hsm) ?_)
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.of_eq (rdZ_SH _) ?_)
  have F1 := slf_view (st' := { sB with prev_length := ml }) F rfl rfl rfl hT
  have F2 := slf_move F1 (sB.strstart + 1) (sB.lookahead - 1) (by show _ ≤ sB.window_size.toNat; omega)
    (by show sB.block_start.toInt ≤ _; omega) (UInt32.le_iff_toNat_le.mpr (by
      have := UInt32.le_iff_toNat_le.mp hins; show sB.insert.toNat ≤ _; omega))
    (fun e => absurd e (by show ¬ _ = sB.block_start.toInt; omega))
  have Lz : LazyOk { sB with prev_length := ml, strstart := sB.strstart + 1, lookahead := sB.lookahead - 1 } :=
    ZlibNgF.Proof.SlowLazy.lazy_step ss la (by rw [← hss]; exact hss1) (by show (sB.lookahead - 1).toNat + 1 = _; omega)
      hT (lf_ne hlf) hbs hml
  have Cf : ∀ d, (SH H1 i z1 b { sB with
      prev_length := ml, strstart := sB.strstart + 1, lookahead := sB.lookahead - 1 } dB).bytes b = some d →
      ChainOk b d { sB with
        prev_length := ml, strstart := sB.strstart + 1, lookahead := sB.lookahead - 1 } := fun d hd => by
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd)
    exact chain_keep F Ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun _ _ _ _ => rfl
  by_cases ha : (z1.avail_out == 0) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)]
    have ha' : ¬ z1.avail_out ≠ 0 := by simpa using ha
    refine Sat.pure ⟨⟨slf_postW F2 flush .need_more (fun st0 h0 => (tab_lv (E.tab st0 h0).1).2.1)
      (fun _ _ _ st hst => ?_) (fun st hst => ?_), fun st d hst hd => ?_⟩, by simp [RM]⟩
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
      exact ⟨Lz, fun e => by cases e⟩
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
      refine ⟨hsym, ?_, ?_, ?_, ?_⟩
      · intro e; rcases e with e | e <;> cases e
      · intro _ hz; exact absurd (hz _ ⟨i, rfl, SH_streams _ _ _ _ _ _⟩) ha'
      · intro e; rcases e with e | e <;> cases e
      · intro e; cases e
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
      exact Cf d hd
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
    have ha' : z1.avail_out ≠ 0 := by simpa using ha
    refine Sat.pure ⟨⟨slc_of F2 (hpz ha') hsym, fun st d hst hd => ?_⟩, ?_⟩
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
      exact ⟨Cf d hd, Lz⟩
    · simp only [RM, avIn_SH, laOf_SH]
      omega

/-- `slowLit`: the pending literal `window[strstart - 1]` is tallied, `FLUSH_BLOCK_ONLY` on a full buffer, then
`slowLit2`. -/
theorem slowLit_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sA : DeflateState}
    {dA : Array UInt8} {level : Int32} {ml : UInt32} {M0 : Nat} (flush : Int32)
    (P : CPre h i b wo level ml M0 H0 z sA dA) (hn : ¬ (3 ≤ sA.prev_length ∧ ml ≤ sA.prev_length))
    (hma : sA.match_available ≠ 0) :
    Sat (SH H0 i z b sA dA) (slowLit (some b) (.ref (.heap b) wo) ml)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, -, hins, w1, -, -, -⟩ := slf_nums P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 sA (SH_dstate _ _ _ _ _ _)
  obtain ⟨h1s, hbs⟩ := P.lit hma
  obtain ⟨wo', po, ho, pbo, L, -, hwp, -, hpb, hhp, hsb⟩ := slf_lay P.slc.1
  have hwin' := L.win
  rw [hwin] at hwin'
  obtain rfl : wo = wo' := by injection hwin' with e; injection e
  have hLp := L.pw
  have hm := P.meas
  have hl1 := P.la1
  have hmlk : 3 ≤ ml → ml.toNat ≤ 258 ∧ ml.toNat ≤ sA.lookahead.toNat ∧ sA.match_start.toNat < sA.strstart.toNat ∧
      sA.strstart.toNat - sA.match_start.toNat ≤ (MAX_DIST sA).toNat := fun h3 => by
    rcases P.mlk h3 with ⟨a1, a2⟩ | a
    · exact absurd ⟨a1, a2⟩ hn
    · exact a
  unfold slowLit
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.index8_SH (H := H0) (i := i) (z := z) (b := b) (st := sA) (d := dA)
    (off := wo) ((sA.strstart - 1).toNat : Int) (by omega) (by rw [Int.toNat_natCast, toNat_sub1 h1s]; omega)
  refine Sat.bind (Sat.of_eq ec ?_)
  refine Sat.bind (Sat.mono (slf_tally_lit0 P.slc.1 hp0 (UInt32.le_of_lt hsym) hbs c) ?_)
  rintro r H2 ⟨lt, d', rfl, F2, ⟨sbo, hi, da, db, hda, hdb, hsb', hw⟩, hr⟩
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hda)
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hdb)
  have hsb2 := hsb' sA (SH_dstate _ _ _ _ _ _)
  rw [hsb] at hsb2
  obtain rfl : pbo + sA.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  have Ch2 : ChainOk b d' { sA with sym_next := sA.sym_next + 3, dyn_ltree := lt, strstart := sA.strstart + 1 } :=
    chain_keep P.slc.1 P.ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun pbo' hpb' j hj => by
      rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e; injection e
      exact hw.2 j (Or.inl (by omega))
  have h3 := slf_sym_step P.slc.1 hsym
  extract_lets jp
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, jp]
    refine slowLit2_ok flush ml M0 sA.strstart.toNat sA.lookahead.toNat P.env F2 rfl rfl hl1 (Int.le_of_lt hbs)
      (fun _ => hp0) ?_ Ch2 hmlk hm
    have hne : sA.sym_next + 3 ≠ sA.sym_end := fun e => by simp [e] at hr
    have a1 := UInt32.le_iff_toNat_le.mp h3
    have a2 : (sA.sym_next + 3).toNat ≠ sA.sym_end.toNat := fun e => hne (UInt32.toNat_inj.mp e)
    show sA.sym_next + 3 < sA.sym_end
    exact UInt32.lt_iff_toNat_lt.mpr (by omega)
  | true =>
    simp only [↓reduceIte]
    have hp : ∀ st, (SH H0 i z b { sA with sym_next := sA.sym_next + 3, dyn_ltree := lt } d').dstate b = some st →
        st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := fun st hst => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst); exact ⟨hp0, hwin⟩
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
      (slf_flush_only T (pure (.ref (.heap b) wo)) 0 (by decide) (by decide) F2 hp rfl)
      (slf_flush_only_keep T (pure (.ref (.heap b) wo)) 0 (by decide) (by decide) F2 hp rfl)) ?_)
    rintro _ H3 ⟨⟨hav3, F3, hs3, hpz3⟩, hk3⟩
    obtain ⟨H1, z3, s3, d3, rfl⟩ := slf_sh F3
    obtain ⟨st2, hst2, K, hpb3⟩ := hk3 _ (SH_dstate _ _ _ _ _ _)
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ := fbkeeps_fields K
    obtain ⟨d4, d5, hd4, hd5, -, hq⟩ := hpb3 pbo hpb
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd4)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd5)
    have hb12 : ((sA.strstart.toInt32).toInt) = (sA.strstart.toNat : Int) :=
      DeflateAlloc.u32_toInt32_toInt _ (by omega)
    have Ch3 : ChainOk b d3 { s3 with strstart := s3.strstart + 1 } :=
      chain_keep F2 Ch2 hT rfl rfl rfl rfl k7 k8 k10 k11 k6 (by rw [k4]; exact Nat.le_refl _) fun pbo' hpb' j hj => by
        rw [hpb] at hpb'
        obtain rfl : pbo = pbo' := by injection hpb' with e; injection e
        exact hq j (Or.inl hj)
    have hav : z3.avail_in = z.avail_in := by
      have := hav3; simp only [avIn, SH_streams] at this; exact UInt32.toNat_inj.mp this
    have hml3 : 3 ≤ ml → ml.toNat ≤ 258 ∧ ml.toNat ≤ sA.lookahead.toNat ∧ s3.match_start.toNat < sA.strstart.toNat ∧
        sA.strstart.toNat - s3.match_start.toNat ≤ (MAX_DIST s3).toNat := fun h3 => by
      obtain ⟨a1, a2, a3, a4⟩ := hmlk h3
      have e2 : s3.match_start = sA.match_start := k2
      have e6 : MAX_DIST s3 = MAX_DIST sA := by unfold MAX_DIST; rw [k6]
      rw [e2, e6]; exact ⟨a1, a2, a3, a4⟩
    obtain ⟨-, e1, -⟩ := hs3 s3 (SH_dstate _ _ _ _ _ _)
    exact slowLit2_ok flush ml M0 sA.strstart.toNat sA.lookahead.toNat P.env F3 (congrArg UInt32.toNat k4)
      (congrArg UInt32.toNat k5) hl1 (by rw [k12]; exact Int.le_of_eq hb12)
      (fun ha => hpz3 _ _ (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) ha) e1 Ch3 hml3 (by rw [hav]; exact hm)

end ZlibNgF.Proof.SlowEmit
