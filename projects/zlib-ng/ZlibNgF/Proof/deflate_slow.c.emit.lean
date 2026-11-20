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
theorem chain_keep {e : Nat} {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    {X X' : DeflateState} (F : SLFe e h i b (SH H0 i z b st d)) (C : ChainOk b d X) (hT : TableAt 7 9 st)
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
    (hn : ¬ (3 ≤ sA.prev_length ∧ ml ≤ sA.prev_length)) (hma0 : sA.match_available = 0) :
    Sat (SH H0 i z b sA dA) (slowElse (some b) ml) (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, hbs, hins, w1, -, -, -⟩ := slf_nums P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 sA (SH_dstate _ _ _ _ _ _)
  have hgapA := (P.slc.1.st sA (SH_dstate _ _ _ _ _ _)).2.2.2.2
  rw [hma0] at hgapA
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
    (view_set rfl rfl)
  have F2 : SLF h i b _ := slf_move F1 (sA.strstart + 1) (sA.lookahead - 1) (by show _ ≤ sA.window_size.toNat; omega)
    (by show sA.block_start.toInt ≤ _; omega) (UInt32.le_iff_toNat_le.mpr (by
      have := UInt32.le_iff_toNat_le.mp hins; show sA.insert.toNat ≤ _; omega))
    (fun e => absurd e (by show ¬ _ = sA.block_start.toInt; omega))
    (by show ((sA.strstart + 1).toNat : Int) - sA.block_start.toInt ≤ 86 * sA.sym_next.toNat + (if (1 : UInt32) ≠ 0 then 1 else 0)
        rw [hss1]; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hgapA
        rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]; omega)
    (fun f => by
      have := ZlibNgF.Proof.DeflatePsi.psiS_move (f := f) { sA with prev_length := ml, match_available := 1 } (sA.strstart + 1) (sA.lookahead - 1) 1
        (by show (sA.lookahead - 1).toNat + 1 = sA.lookahead.toNat; omega)
        (by show (sA.strstart + 1).toNat = sA.strstart.toNat + 1; omega) (by show sA.block_start.toInt ≤ _; omega)
      exact (by omega : ∀ a c : Nat, a + 2 ^ 19 * 1 ≤ c + 6 * 1 → a + 2 ^ 18 ≤ c + 0) _ _ this)
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
theorem slf_sh {e : Nat} {h H : Heap} {i b : Nat} (F : SLFe e h i b H) : ∃ H1 z st d, H = SH H1 i z b st d := by
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
    (F : SLFe (2 ^ 18) h i b (SH H1 i z1 b sB dB)) (hss : sB.strstart.toNat = ss) (hla : sB.lookahead.toNat = la)
    (hl1 : 1 ≤ la) (hbs : sB.block_start.toInt ≤ ss) (hpz : z1.avail_out ≠ 0 → sB.pending = 0)
    (hsym : sB.sym_next < sB.sym_end) (Ch : ChainOk b dB { sB with strstart := sB.strstart + 1 })
    (hml : 3 ≤ ml → ml.toNat ≤ 258 ∧ ml.toNat ≤ la ∧ sB.match_start.toNat < ss ∧
      ss - sB.match_start.toNat ≤ (MAX_DIST sB).toNat)
    (hm : z1.avail_in.toNat + la ≤ M0)
    (hgapB : (ss : Int) + 1 - sB.block_start.toInt ≤
      86 * sB.sym_next.toNat + (if sB.match_available ≠ 0 then 1 else 0)) :
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
  have F1 := slf_view (st' := { sB with prev_length := ml }) F rfl rfl rfl hT (view_le rfl rfl (.inr rfl))
  have F2 : SLF h i b _ := slf_move F1 (sB.strstart + 1) (sB.lookahead - 1) (by show _ ≤ sB.window_size.toNat; omega)
    (by show sB.block_start.toInt ≤ _; omega) (UInt32.le_iff_toNat_le.mpr (by
      have := UInt32.le_iff_toNat_le.mp hins; show sB.insert.toNat ≤ _; omega))
    (fun e => absurd e (by show ¬ _ = sB.block_start.toInt; omega))
    (by show ((sB.strstart + 1).toNat : Int) - sB.block_start.toInt ≤ _; rw [hss1, hss]; exact hgapB)
    (fun f => by
      have := ZlibNgF.Proof.DeflatePsi.psiS_move (f := f) { sB with prev_length := ml } (sB.strstart + 1) (sB.lookahead - 1) 1
        (by show (sB.lookahead - 1).toNat + 1 = sB.lookahead.toNat; omega)
        (by show (sB.strstart + 1).toNat = sB.strstart.toNat + 1; omega) (by show sB.block_start.toInt ≤ (sB.strstart.toNat : Int); omega)
      exact (by omega : ∀ a c : Nat, a + 2 ^ 19 * 1 ≤ c + 6 * 1 → a + 2 ^ 18 ≤ c + 0) _ _ this)
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
    refine Sat.pure ⟨⟨slf_postW F2 flush .need_more
      (exitIO_nm (o0_of fun z5 h5 => by
        rw [SH_streams] at h5; obtain rfl := Option.some.inj h5; simpa using ha)) (fun st0 h0 => (tab_lv (E.tab st0 h0).1).2.1)
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
      (fun _ => hp0) ?_ Ch2 hmlk hm ?_
    · have hne : sA.sym_next + 3 ≠ sA.sym_end := fun e => by simp [e] at hr
      have a1 := UInt32.le_iff_toNat_le.mp h3
      have a2 : (sA.sym_next + 3).toNat ≠ sA.sym_end.toNat := fun e => hne (UInt32.toNat_inj.mp e)
      show sA.sym_next + 3 < sA.sym_end
      exact UInt32.lt_iff_toNat_lt.mpr (by omega)
    · have hgapA := (P.slc.1.st sA (SH_dstate _ _ _ _ _ _)).2.2.2.2
      have hsn3 : (sA.sym_next + 3).toNat = sA.sym_next.toNat + 3 := by
        obtain ⟨z1, st1, al, -, -, hst1, -, c'⟩ := P.slc.1.live
        obtain rfl : sA = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
        obtain ⟨-, -, -, -, hl2, -, hse⟩ := c'.sizes
        simp only [dview] at hse hl2
        have := UInt32.lt_iff_toNat_lt.mp hsym
        rw [UInt32.toNat_add]; simp; omega
      show (sA.strstart.toNat : Int) + 1 - sA.block_start.toInt ≤ 86 * (sA.sym_next + 3).toNat + (if sA.match_available ≠ 0 then 1 else 0)
      omega
  | true =>
    simp only [↓reduceIte]
    have hp : ∀ st, (SH H0 i z b { sA with sym_next := sA.sym_next + 3, dyn_ltree := lt } d').dstate b = some st →
        st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := fun st hst => by
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst); exact ⟨hp0, hwin⟩
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
      (slf_flush_only T (pure (.ref (.heap b) wo)) 0 (by decide) (by decide) F2 hp rfl fun _ st hst => by
        obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
        exact slf_sym3 P.slc.1 (UInt32.le_of_lt hsym))
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
    exact slowLit2_ok flush ml M0 sA.strstart.toNat sA.lookahead.toNat P.env (F3.mono (Nat.le_of_eq rfl))
      (congrArg UInt32.toNat k4)
      (congrArg UInt32.toNat k5) hl1 (by rw [k12]; exact Int.le_of_eq hb12)
      (fun ha => hpz3 _ _ (SH_streams _ _ _ _ _ _) (SH_dstate _ _ _ _ _ _) ha) e1 Ch3 hml3 (by rw [hav]; exact hm)
      (by rw [k12, hb12, k3, ite_eq_left hma]; omega)

/-! ## The pending match -/

/-- `slowDist3`: `prev_length` and `match_available` cleared, `strstart` past the match (`ss'`), `FLUSH_BLOCK` on a full
symbol buffer. The frame holds of the state with `strstart = ss'` (the lookahead is already lowered). -/
theorem slowDist3_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sE : DeflateState}
    {dE : Array UInt8} {level : Int32} (flush : Int32) (M0 : Nat) (mov_fwd ss' : UInt32) (bflush : Bool)
    (E : Env h b wo level) (hss' : sE.strstart + (mov_fwd + 1) = ss')
    (F : SLF h i b (SH H0 i z b (FS sE sE.lookahead ss') dE)) (hp0 : sE.pending = 0)
    (hbf : bflush = false → sE.sym_next < sE.sym_end) (Ch : ChainOk b dE { sE with strstart := ss' })
    (hm : z.avail_in.toNat + sE.lookahead.toNat + 1 ≤ M0) (hnz : sE.sym_next ≠ 0)
    (hgap0 : (ss'.toNat : Int) - sE.block_start.toInt ≤ 86 * sE.sym_next.toNat) :
    Sat (SH H0 i z b sE dE) (slowDist3 (some b) (.ref (.heap b) wo) mov_fwd bflush)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st E F
  unfold slowDist3
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sE with prev_length := 0 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sE with prev_length := 0, match_available := 0 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sE with prev_length := 0, match_available := 0, strstart := ss' })
    (by subst hss'; rfl)) ?_)
  have F' := slf_view_gap (st' := { sE with prev_length := 0, match_available := 0, strstart := ss' }) F rfl rfl rfl hT
    (by show (ss'.toNat : Int) - sE.block_start.toInt ≤ 86 * sE.sym_next.toNat + (if (0 : UInt32) ≠ 0 then 1 else 0)
        simpa using hgap0)
    (view_le rfl rfl (.inl rfl))
  have Lf : LazyOk { sE with prev_length := 0, match_available := 0, strstart := ss' } :=
    LazyOk.of_clear (show (0 : UInt32) < 3 by decide) rfl
  have Cf : ChainOk b dE { sE with prev_length := 0, match_available := 0, strstart := ss' } :=
    chain_keep F Ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun _ _ _ _ => rfl
  have hp : ∀ st, (SH H0 i z b { sE with prev_length := 0, match_available := 0, strstart := ss' } dE).dstate b =
      some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo) := fun st hst => by
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst); exact ⟨hp0, hwin⟩
  cases bflush with
  | false =>
    refine Sat.pure ⟨⟨slc_of F' hp0 (hbf rfl), fun st d hst hd => ?_⟩, ?_⟩
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
      obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd)
      exact ⟨Cf, Lf⟩
    · simp only [RM, avIn_SH, laOf_SH]
      show z.avail_in.toNat + sE.lookahead.toNat + 1 < M0 + 1
      omega
  | true =>
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and (slf_flush T 0 (by decide) (by decide) F' hp
      fun _ => nz_SH hnz)
      (slf_flush_keep T 0 (by decide) (by decide) F' hp)) ?_)
    rintro r H2 ⟨⟨hav, F2, hs2, hn2, hsm, hcf⟩, hk2⟩
    obtain ⟨H1, z2, s2, d2, rfl⟩ := slf_sh F2
    obtain ⟨st2, hst2, K, hpb2⟩ := hk2 _ (SH_dstate _ _ _ _ _ _)
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
    obtain ⟨k1, -, k3, k4, k5, k6, k7, k8, -, k10, k11, -⟩ := fbkeeps_fields K
    obtain ⟨pbo, hpb⟩ : ∃ pbo, sE.pending_buf = .val (.ref (.heap b) pbo) := by
      obtain ⟨-, -, -, pbo, -, -, -, -, hpb, -⟩ := slf_lay F'; exact ⟨pbo, hpb⟩
    obtain ⟨d4, d5, hd4, hd5, -, hq⟩ := hpb2 pbo hpb
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd4)
    obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd5)
    have C2 : ChainOk b d2 s2 := chain_keep F' Cf hT rfl rfl rfl rfl k7 k8 k10 k11 k6
      (by rw [k4]; exact Nat.le_refl _) fun pbo' hpb' j hj => by
        have hpb'' : sE.pending_buf = _ := hpb'
        rw [hpb] at hpb''
        obtain rfl : pbo = pbo' := by injection hpb'' with e; injection e
        exact hq j (Or.inl hj)
    have L2 : LazyOk s2 := LazyOk.of_clear (by rw [k1]; exact (show (0 : UInt32) < 3 by decide)) (by rw [k3])
    have hav' : z2.avail_in.toNat = z.avail_in.toNat := by simpa [avIn] using hav
    cases r with
    | none =>
      refine Sat.pure ⟨⟨⟨F2, fun st hst => ⟨hn2 rfl st hst, (hs2 st hst).2.1⟩⟩, fun st d hst hd => ?_⟩, ?_⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
        obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd)
        exact ⟨C2, L2⟩
      · simp only [RM, avIn_SH, laOf_SH]
        rw [k5, hav']
        show z.avail_in.toNat + sE.lookahead.toNat + 1 < M0 + 1
        omega
    | some v =>
      obtain ⟨rfl⟩ := Option.some.inj (hsm (by simp))
      refine Sat.pure ⟨⟨slf_postW F2 flush _ (exitIO_nm (hcf (by simp))) (fun st0 h0 => (tab_lv (E.tab st0 h0).1).2.1)
        (fun _ _ _ st hst => ?_) (fun st hst => ?_), fun st d hst hd => ?_⟩, by simp [RM]⟩
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
        exact ⟨L2, fun e => by simp at e⟩
      · obtain ⟨e1, e2, -⟩ := hs2 st hst
        refine ⟨e2, ?_, fun _ _ => e1, ?_, ?_⟩
        · intro e; simp at e
        · intro e; simp at e
        · intro e; simp at e
      · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst)
        obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hd)
        exact C2

/-- At the levels of `deflate_slow` the chain limit is `strstart`. -/
theorem chainLim_hi {X : DeflateState} (h7 : 7 ≤ X.level) : chainLim X = X.strstart.toNat := by
  have hn : ¬ (3 ≤ X.level ∧ X.level ≤ 6) := fun ⟨_, h6⟩ => by
    have a := Int32.le_iff_toInt_le.mp h7
    have c := Int32.le_iff_toInt_le.mp h6
    have e7 : (7 : Int32).toInt = 7 := rfl
    have e6 : (6 : Int32).toInt = 6 := rfl
    omega
  unfold chainLim
  simp only [hn, ↓reduceIte, Nat.add_zero]

theorem chainLim_le {X X' : DeflateState} (h7 : 7 ≤ X.level) (e : X'.level = X.level)
    (hs : X.strstart.toNat ≤ X'.strstart.toNat) : chainLim X ≤ chainLim X' := by
  rw [chainLim_hi h7, chainLim_hi (by rw [e]; exact h7)]; exact hs

theorem chainLim_gt {X : DeflateState} {q : Nat} (h7 : 7 ≤ X.level) (hq : q < X.strstart.toNat) : q < chainLim X := by
  rw [chainLim_hi h7]; exact hq

/-- The `insert_batch` of levels 7-9 is not `insert_knuth_batch_head`. -/
theorem ib_ne {level : Int32} (h7 : 7 ≤ level) : insertBatchOf level ≠ .insert_knuth_batch_head := by
  unfold insertBatchOf
  split
  · decide
  · have hn : (level == 1) = false := by
      have a := Int32.le_iff_toInt_le.mp h7
      have e7 : (7 : Int32).toInt = 7 := rfl
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; rw [e] at a; exact absurd a (by decide)
    simp only [hn, Bool.false_eq_true, ↓reduceIte, ne_eq]
    decide

/-- `slowIns`: the positions after `strstart` inside the match are inserted (`insert_batch`, or the tail forms that
skip all but the last `tail_cnt`), then `slowDist3`. -/
theorem slowIns_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sD : DeflateState}
    {dD : Array UInt8} {level : Int32} (flush : Int32) (M0 : Nat) (max_insert mov_fwd ss' : UInt32) (bflush : Bool)
    (laA : Nat) (E : Env h b wo level) (hss' : sD.strstart + (mov_fwd + 1) = ss')
    (hss'n : ss'.toNat = sD.strstart.toNat + mov_fwd.toNat + 1) (hmv1 : 1 ≤ mov_fwd.toNat)
    (hmv : mov_fwd.toNat ≤ 257) (hmi : max_insert.toNat + 3 = sD.strstart.toNat + laA)
    (hgt : sD.strstart.toNat < max_insert.toNat) (hws : sD.strstart.toNat + laA ≤ sD.window_size.toNat)
    (F : SLF h i b (SH H0 i z b (FS sD sD.lookahead ss') dD)) (hp0 : sD.pending = 0)
    (hbf : bflush = false → sD.sym_next < sD.sym_end) (Ch : ChainOk b dD { sD with strstart := sD.strstart + 1 })
    (hm : z.avail_in.toNat + sD.lookahead.toNat + 1 ≤ M0) (hnz : sD.sym_next ≠ 0)
    (hgap0 : (ss'.toNat : Int) - sD.block_start.toInt ≤ 86 * sD.sym_next.toNat) :
    Sat (SH H0 i z b sD dD) (slowIns (some b) (.ref (.heap b) wo) (insertBatchOf level) level max_insert mov_fwd bflush)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, hlv⟩ := env_st E F
  obtain ⟨-, h65, -, -, w1, -, -, -⟩ := slf_nums F
  have h65' : sD.window_size.toNat ≤ 65536 := h65
  have w1' : 512 ≤ sD.w_size.toNat := w1
  have h7 : 7 ≤ sD.level := (tab_lv hT).2.2
  have h7' : 7 ≤ level := by rw [← hlv]; exact h7
  have hss1 := toNat_add1 (x := sD.strstart) (by omega)
  have post : ∀ (x : UInt32) (d' : Array UInt8) (S : Nat → Prop), (∀ q, S q → q < ss'.toNat) →
      ZlibNgF.Proof.InsertLoop.GrowSt b sD dD d' S →
      SLF h i b (SH H0 i z b (FS { sD with ins_h := x } sD.lookahead ss') d') →
      Sat (SH H0 i z b { sD with ins_h := x } d') (slowDist3 (some b) (.ref (.heap b) wo) mov_fwd bflush)
        (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
    intro x d' S hS g F'
    refine slowDist3_ok T flush M0 mov_fwd ss' bflush E hss' F' hp0 hbf ?_ hm hnz hgap0
    refine ZlibNgF.Proof.InsertGrow.ChainOk.grow Ch g rfl rfl rfl rfl rfl
      (by show (sD.strstart + 1).toNat ≤ ss'.toNat; omega) (chainLim_le h7 rfl ?_) fun q hq _ => chainLim_gt h7 (hS q hq)
    show (sD.strstart + 1).toNat ≤ ss'.toNat; omega
  have hJ : ∀ cnt : UInt32, 1 ≤ cnt.toNat → cnt.toNat ≤ mov_fwd.toNat →
      cnt.toNat + sD.strstart.toNat ≤ max_insert.toNat →
      Sat (SH H0 i z b sD dD) (slowIns2 (some b) (.ref (.heap b) wo) (insertBatchOf level) level mov_fwd bflush cnt)
        (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
    intro cnt hc1 hc2 hc3
    unfold slowIns2
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    extract_lets match_dist tail_cnt jp
    by_cases ht : tail_cnt ≥ cnt
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
      refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
      refine Sat.bind (Sat.mono (slf_call_insert_batch F hwin (insertBatchOf level) (ib_ne h7') (sD.strstart + 1) cnt
        (by rw [hss1]; omega) (by rw [hss1]; omega)) ?_)
      rintro _ _ ⟨d', x, rfl, F', g⟩
      exact post x d' _ (fun q hq => by rw [hss1] at hq; omega) g F'
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ht)]
      have ht' : tail_cnt.toNat ≤ cnt.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp ht); omega
      by_cases hr : level ≥ ZlibNg.Deflate.MIN_ROLL_LEVEL
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)]
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        refine Sat.bind (Sat.mono (slf_insert_roll_tail F hwin (sD.strstart + 1) cnt tail_cnt ht' (by omega)
          (by rw [hss1]; omega) (by rw [hss1]; omega)) ?_)
        rintro _ _ ⟨d', x, rfl, F', g⟩
        exact post x d' _ (fun q hq => by rw [hss1] at hq; omega) g F'
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)]
        refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
        refine Sat.bind (Sat.mono (slf_insert_knuth_tail F hwin (sD.strstart + 1) cnt tail_cnt ht' (by omega)
          (by rw [hss1]; omega) (by rw [hss1]; omega)) ?_)
        rintro _ _ ⟨d', x, rfl, F', g⟩
        exact post x d' _ (fun q hq => by rw [hss1] at hq; omega) g F'
  have hsub : (max_insert - sD.strstart).toNat = max_insert.toNat - sD.strstart.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  unfold slowIns
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  dsimp only
  by_cases hc : mov_fwd > max_insert - sD.strstart
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    have := UInt32.lt_iff_toNat_lt.mp hc
    exact hJ _ (by omega) (by omega) (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hc)
    exact hJ _ hmv1 (Nat.le_refl _) (by omega)

/-- `slowDist2`: after the tally of the pending match of length `pl` (`n = pl - 1` positions after `strstart - 1`),
`prev_length` and `lookahead` lowered, the insertions when `max_insert > strstart`, then `slowDist3`. -/
theorem slowDist2_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sB : DeflateState}
    {dB : Array UInt8} {level : Int32} (flush : Int32) (M0 : Nat) (max_insert : UInt32) (bflush : Bool)
    (E : Env h b wo level)
    (F : SLF h i b (SH H0 i z b (FS sB (sB.lookahead - (sB.prev_length - 1)) (sB.strstart + (sB.prev_length - 1))) dB))
    (hp0 : sB.pending = 0) (hbf : bflush = false → sB.sym_next < sB.sym_end)
    (Ch : ChainOk b dB { sB with strstart := sB.strstart + 1 })
    (hpl3 : 3 ≤ sB.prev_length.toNat) (hpl : sB.prev_length.toNat ≤ 258)
    (hpla : sB.prev_length.toNat ≤ sB.lookahead.toNat + 1)
    (hmi : max_insert.toNat + 3 = sB.strstart.toNat + sB.lookahead.toNat)
    (hws : sB.strstart.toNat + sB.lookahead.toNat ≤ sB.window_size.toNat)
    (hm : z.avail_in.toNat + sB.lookahead.toNat ≤ M0) (hnz : sB.sym_next ≠ 0)
    (hgap0 : ((sB.strstart + (sB.prev_length - 1)).toNat : Int) - sB.block_start.toInt ≤ 86 * sB.sym_next.toNat) :
    Sat (SH H0 i z b sB dB) (slowDist2 (some b) (.ref (.heap b) wo) (insertBatchOf level) level max_insert bflush)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, hlv⟩ := env_st E F
  have h7 : 7 ≤ sB.level := (tab_lv hT).2.2
  have hp1 : (sB.prev_length - 1).toNat = sB.prev_length.toNat - 1 := toNat_sub1 (by omega)
  have hp2 : (sB.prev_length - 1 - 1).toNat = sB.prev_length.toNat - 2 := by
    rw [toNat_sub1 (by omega), hp1]; omega
  have hla' : (sB.lookahead - (sB.prev_length - 1)).toNat = sB.lookahead.toNat - (sB.prev_length.toNat - 1) := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), hp1]
  have h65 : sB.window_size.toNat ≤ 65536 := (slf_nums F).2.1
  have hss' : (sB.strstart + (sB.prev_length - 1)).toNat = sB.strstart.toNat + (sB.prev_length.toNat - 1) := by
    rw [UInt32.toNat_add, hp1]; omega
  unfold slowDist2
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with prev_length := sB.prev_length - 1 }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (wrD_SH' _ (st' := { sB with
    prev_length := sB.prev_length - 1, lookahead := sB.lookahead - (sB.prev_length - 1) }) rfl) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  dsimp only
  have F' := slf_view (st' := FS { sB with
    prev_length := sB.prev_length - 1, lookahead := sB.lookahead - (sB.prev_length - 1) }
    (sB.lookahead - (sB.prev_length - 1))
    (sB.strstart + (sB.prev_length - 1))) F rfl rfl rfl hT (view_le rfl rfl (.inr rfl))
  have e1 : sB.strstart + (sB.prev_length - 1 - 1 + 1) = sB.strstart + (sB.prev_length - 1) := by
    rw [UInt32.sub_add_cancel]
  by_cases hc : max_insert > sB.strstart
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have hc' := UInt32.lt_iff_toNat_lt.mp hc
    exact slowIns_ok T flush M0 max_insert _ _ bflush sB.lookahead.toNat E e1 (by
        show (sB.strstart + (sB.prev_length - 1)).toNat = sB.strstart.toNat + (sB.prev_length - 1 - 1).toNat + 1
        rw [hss', hp2]; omega)
      (by show 1 ≤ (sB.prev_length - 1 - 1).toNat; rw [hp2]; omega)
      (by show (sB.prev_length - 1 - 1).toNat ≤ 257; rw [hp2]; omega) hmi hc' hws F' hp0 hbf
      (chain_keep F Ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun _ _ _ _ => rfl)
      (by show _ + (sB.lookahead - (sB.prev_length - 1)).toNat + 1 ≤ M0; rw [hla']; omega) hnz hgap0
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact slowDist3_ok T flush M0 _ _ bflush E e1 F' hp0 hbf
      (chain_keep F Ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (by
        show (sB.strstart + 1).toNat ≤ (sB.strstart + (sB.prev_length - 1)).toNat
        rw [hss', toNat_add1 (by omega)]; omega) fun _ _ _ _ => rfl)
      (by show _ + (sB.lookahead - (sB.prev_length - 1)).toNat + 1 ≤ M0; rw [hla']; omega) hnz hgap0

open ZlibNgF.Proof.Tally (tally_dist_SH incF) in
/-- `slowDist`: the pending match (`prev_length = pl >= 3`, at `strstart - 1`, distance `strstart - 1 - prev_match`)
is tallied, then `slowDist2`. -/
theorem slowDist_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sA : DeflateState}
    {dA : Array UInt8} {level : Int32} {ml : UInt32} {M0 : Nat} (flush : Int32)
    (P : CPre h i b wo level ml M0 H0 z sA dA) (hc : 3 ≤ sA.prev_length) :
    Sat (SH H0 i z b sA dA) (slowDist (some b) (.ref (.heap b) wo) (insertBatchOf level) level sA)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  obtain ⟨hwin, hT, hlf, -⟩ := env_st P.env P.slc.1
  obtain ⟨hlook, h65, -, -, w1, w2, -, -⟩ := slf_nums P.slc.1
  obtain ⟨hp0, hsym⟩ := P.slc.2 sA (SH_dstate _ _ _ _ _ _)
  obtain ⟨a1, a2, a3, a4⟩ := P.pend hc
  have hc' : 3 ≤ sA.prev_length.toNat := by have := UInt32.le_iff_toNat_le.mp hc; simpa using this
  have hm := P.meas
  have hmd : (MAX_DIST sA).toNat = sA.w_size.toNat - 262 := by
    unfold MAX_DIST
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show 262 ≤ _; omega))]; rfl
  have hs1 : (sA.strstart - 1).toNat = sA.strstart.toNat - 1 := toNat_sub1 (by omega)
  have hdist : (sA.strstart - 1 - sA.prev_match).toNat = sA.strstart.toNat - 1 - sA.prev_match.toNat := by
    have hle : sA.prev_match ≤ sA.strstart - 1 := UInt32.le_iff_toNat_le.mpr (by rw [hs1]; omega)
    rw [UInt32.toNat_sub_of_le _ _ hle, hs1]
  have hlen : (sA.prev_length - STD_MIN_MATCH).toNat = sA.prev_length.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ hc
  have hn : (sA.prev_length - 1).toNat = sA.prev_length.toNat - 1 := toNat_sub1 (by omega)
  obtain ⟨sbo, hsb, hk, hlt, hdt⟩ := slf_sym P.slc.1 (UInt32.le_of_lt hsym)
  obtain ⟨wo', po, ho, pbo, L, -, -, -, hpb, hhp, hsb2⟩ := slf_lay P.slc.1
  rw [hsb] at hsb2
  obtain rfl : sbo = pbo + sA.lit_bufsize.toNat + 8 := by injection hsb2 with e; injection e
  unfold slowDist
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumStep.Sat.and
    (tally_dist_SH (H := H0) (i := i) (z := z) (b := b) (st := sA) (d := dA) _ _ (by rw [hlen]; omega)
      (by rw [hdist]; omega) (by rw [hdist]; omega) hsb hk hlt hdt)
    (slf_tally_dist (st := sA) (la := sA.lookahead) (ss := sA.strstart) P.slc.1 hp0 (UInt32.le_of_lt hsym)
      (sA.strstart - 1 - sA.prev_match) (sA.prev_length - STD_MIN_MATCH) (sA.prev_length - 1)
      (by rw [hlen]; omega) (by rw [hdist]; omega) (by rw [hdist]; omega) (by rw [hn]; omega) (by rw [hn]; omega)
      (by rw [hn]; omega))) ?_)
  rintro r H' ⟨⟨rfl, hr⟩, -, W, ⟨sbo', hi, da, db, hda, hdb, hsb', hw⟩, -, hle', -⟩
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hda)
  obtain rfl := Option.some.inj ((SH_bytes _ _ _ _ _ _).symm.trans hdb)
  have hsb3 := hsb' sA (SH_dstate _ _ _ _ _ _)
  rw [hsb] at hsb3
  obtain rfl : pbo + sA.lit_bufsize.toNat + 8 = sbo' := by injection hsb3 with e; injection e
  obtain ⟨F2, hp2⟩ := slw_norm W
  have h3 := slf_sym_step P.slc.1 hsym
  refine slowDist2_ok T flush M0 _ r P.env F2 hp0 (fun e => ?_) ?_ (by exact hc') (by exact a1) (by exact a2) ?_
    (by exact hlook) (by exact hm) (slf_sym3 P.slc.1 (UInt32.le_of_lt hsym)) ?_
  · subst e
    have hne : sA.sym_next + 3 ≠ sA.sym_end := fun e => by simp [e] at hr
    have b1 := UInt32.le_iff_toNat_le.mp h3
    have b2 : (sA.sym_next + 3).toNat ≠ sA.sym_end.toNat := fun e => hne (UInt32.toNat_inj.mp e)
    show sA.sym_next + 3 < sA.sym_end
    exact UInt32.lt_iff_toNat_lt.mpr (by omega)
  · exact chain_keep P.slc.1 P.ch hT rfl rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) fun pbo' hpb' j hj => by
      rw [hpb] at hpb'
      obtain rfl : pbo = pbo' := by injection hpb' with e; injection e
      exact hw.2 j (Or.inl (by omega))
  · show (sA.strstart + sA.lookahead - STD_MIN_MATCH).toNat + 3 = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by
      rw [UInt32.toNat_add]; show 3 ≤ _; rw [Nat.mod_eq_of_lt (by omega)]; omega)), UInt32.toNat_add,
      Nat.mod_eq_of_lt (by omega)]
    show sA.strstart.toNat + sA.lookahead.toNat - 3 + 3 = sA.strstart.toNat + sA.lookahead.toNat; omega
  · have hgapA := (P.slc.1.st sA (SH_dstate _ _ _ _ _ _)).2.2.2.2
    have hsn3 : (sA.sym_next + 3).toNat = sA.sym_next.toNat + 3 := by
      obtain ⟨z1, st1, al, -, -, hst1, -, c'⟩ := P.slc.1.live
      obtain rfl : sA = st1 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst1)
      obtain ⟨-, -, -, -, hl2, -, hse⟩ := c'.sizes
      simp only [dview] at hse hl2
      have := UInt32.lt_iff_toNat_lt.mp hsym
      rw [UInt32.toNat_add]; simp; omega
    have hss' : (sA.strstart + (sA.prev_length - 1)).toNat = sA.strstart.toNat + (sA.prev_length.toNat - 1) := by
      rw [UInt32.toNat_add, hn]; omega
    show ((sA.strstart + (sA.prev_length - 1)).toNat : Int) - sA.block_start.toInt ≤ 86 * (sA.sym_next + 3).toNat
    rw [hss', hsn3]; split at hgapA <;> omega

/-- `slowC`: the emission after the match search, by the three branches. -/
theorem slowC_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {sA : DeflateState}
    {dA : Array UInt8} {level : Int32} {ml : UInt32} {M0 : Nat} (flush : Int32)
    (P : CPre h i b wo level ml M0 H0 z sA dA) :
    Sat (SH H0 i z b sA dA) (slowC (some b) (.ref (.heap b) wo) (insertBatchOf level) level ml)
      (fun c H2 => RI h i b flush c H2 ∧ RM i b c H2 < M0 + 1) := by
  unfold slowC
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  by_cases hc : (decide (sA.prev_length ≥ STD_MIN_MATCH) && decide (ml ≤ sA.prev_length)) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact slowDist_ok T flush P hc.1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have hn : ¬ (3 ≤ sA.prev_length ∧ ml ≤ sA.prev_length) := fun ⟨a, c⟩ => hc (by simp [STD_MIN_MATCH]; exact ⟨a, c⟩)
    by_cases hm : (sA.match_available != 0) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
      exact slowLit_ok T flush P hn (by simpa using hm)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
      exact slowElse_ok flush P hn (by simpa using hm)

end ZlibNgF.Proof.SlowEmit
