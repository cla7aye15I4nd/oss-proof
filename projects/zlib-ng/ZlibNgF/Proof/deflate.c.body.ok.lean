import ZlibNgF.Proof.«deflate.c.body.after»
import ZlibNgF.Proof.«trees.c.facts»
import ZlibNgF.Proof.«deflate.c.reach»

/-!
# `deflate`: the strategy call and the whole call (`ZlibNgF`)

`bodyC_ok`: the dispatch of `deflate` to a strategy (`StrategyFacts`) and what follows it (`after_ok`), or the trailer.
`bodyB_ok`, `bodyA_ok`: the parts before it (the pending output, the repeated flush, the header). `deflate_ok`: the
whole call, from the argument checks on (`DeflateParams.DeflateOk`); `dpending`: the obligations of
`DeflateReach.DPending` from `StrategyFacts`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateBody
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk HdrState HdrMove)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.DeflateParams (config_eq lvl_nat)
open ZlibNgF.Proof.FlushBlock (dframe_nil)

/-- The state of a strategy's result heap is the stream's state. -/
theorem post_state {H H' : Heap} {i b : Nat} {flush : Int32} {bs : BlockState} (P : StratPost H (some i) flush bs H')
    (hsb : StateBlock H (some i) b) {st' : DeflateState} (h' : H'.dstate b = some st') : DStateIs H' (some i) b st' := by
  obtain ⟨z', ⟨i', e', hz'⟩, hb'⟩ := P.2.2.2.2.2.1 b hsb
  obtain rfl := Option.some.inj e'
  exact ⟨i, z', rfl, hz', hb', h'⟩

/-- The stream facts of a strategy's `StratPost` as `after_ok` takes them. -/
theorem strat_io {h H H' : Heap} {i b : Nat} {flush : Int32} {bs : BlockState} (R : Run h i b H)
    (P : StratPost H (some i) flush bs H') {z' : ZStream} (hz' : H'.streams i = some z') :
    (bs = .need_more ∨ bs = .block_done → aIn H' i = 0 ∨ aOut H' i = 0) ∧
    (bs = .finish_started ∨ bs = .finish_done → flush = Z_FINISH) ∧
    (flush = Z_FINISH → bs = .need_more ∨ bs = .finish_started → aOut h i ≠ 0 →
      aIn H' i < aIn h i ∨ aOut H' i < aOut h i) := by
  obtain ⟨-, -, -, -, Pout, -, -, Pcf, Pfin, Pprog, -, -⟩ := P
  obtain ⟨z, -, -, -, hz, -⟩ := R.live
  have m := R.mono
  refine ⟨fun e => ?_, Pfin, fun hf e hne => ?_⟩
  · rcases Pcf e z' ⟨i, rfl, hz'⟩ with x | x
    · left; rw [aIn_of hz', x]; rfl
    · right; rw [aOut_of hz', x]; rfl
  · obtain ⟨z0, z1, ob, oo, k, h0, h1, -, -, ek⟩ := Pout i rfl
    obtain rfl := Option.some.inj (hz.symm.trans h0)
    obtain rfl := Option.some.inj (hz'.symm.trans h1)
    rw [aIn_of hz', aOut_of hz']
    rw [aIn_of hz, aOut_of hz] at m
    by_cases h0 : z.avail_out = 0
    · right; rw [h0] at ek; simp at ek; omega
    · rcases Pprog hf e z z' ⟨i, rfl, hz⟩ ⟨i, rfl, hz'⟩ h0 with x | x
      · left; have := UInt32.lt_iff_toNat_lt.mp x; omega
      · right; have := UInt32.lt_iff_toNat_lt.mp x; omega

/-- **The strategy part** (`bodyC`). -/
theorem bodyC_ok (SF : StrategyFacts) (T : TreesFacts) {h H : Heap} {i b : Nat} {flush : Int32}
    {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE) (hlf : st.last_flush = flush) (hf0 : 0 ≤ flush)
    (hf5 : flush ≤ 5) (hp0 : st.pending = 0)
    (hfa : st.status = FINISH_STATE → ∀ z, H.streams i = some z → z.avail_in = 0) :
    Sat H (bodyC (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
  obtain ⟨z, st1, al, d, hz, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain ⟨S1, S2, -, -, S5, S6⟩ := R.side st hst
  have uniq : ∀ b' st', DStateIs H (some i) b' st' → st' = st := fun b' st' ⟨i', z', e', hz', hb', hst'⟩ => by
    obtain rfl := Option.some.inj e'
    obtain rfl := Option.some.inj (hz.symm.trans hz')
    obtain rfl := Option.some.inj (hb.symm.trans hb')
    exact Option.some.inj (hst'.symm.trans hst)
  have hD : DStateIs H (some i) b st := ⟨i, z, rfl, hz, hb, hst⟩
  have SB : StateBlock H (some i) b := ⟨z, ⟨i, rfl, hz⟩, hb⟩
  have fin : ∀ (bs : BlockState) H', StratPost H (some i) flush bs H' →
      (∀ st' d, H'.dstate b = some st' → H'.bytes b = some d → ChainOk b d st') → st.status = BUSY_STATE →
      Sat H' (afterStrat bs (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
    intro bs H' P hC hbusy
    obtain ⟨R', K⟩ := run_post R hst hbusy (by rw [hlf]; exact hf0) P hC
    obtain ⟨z', -, -, -, hz', -⟩ := R'.live
    obtain ⟨A1, A2, A3⟩ := strat_io R P hz'
    exact after_ok T R' (fun st' h' => by
      obtain ⟨k1, k2, k3, k4, k5⟩ := K st' h'
      obtain ⟨s1, -, -, -, -, -, s7, -⟩ := k1
      exact ⟨s1.trans hbusy, s7.trans hlf, k2, k3, k4, k5⟩) A1 A2 A3
  have keeps : ∀ (bs : BlockState) H', StratPost H (some i) flush bs H' → ∀ st', H'.dstate b = some st' →
      StratKeeps st st' := fun bs H' P st' h' => (P.2.2.2.2.2.2.2.2.2.2.2 b st st' hD (post_state P SB h')).2.1
  unfold bodyC
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
  by_cases hc : (z.avail_in != 0 || st.lookahead != 0 || (flush != Z_NO_FLUSH && st.status != FINISH_STATE)) = true
  · rw [ite_t hc]
    have hbusy : st.status = BUSY_STATE := by
      rcases hs with x | x
      · exact x
      · exfalso; simp [hfa x z hz, (S2 x).2, x] at hc
    have SP : StratPre H (some i) flush := ⟨R.inv, R.crc, R.io, R.set, hf0, hf5, b, st, hD, hp0, .inl hbusy, S1, S6,
      by rw [hlf]; exact hf0⟩
    have runP : ∀ (D : DeflateState → Prop) (f : StatePtr → Int32 → M BlockState), StratOkP D f → D st →
        (st.level = 1 ∨ HASHLESS st.level st.strategy = true) →
        Sat H (f (some b) flush >>= fun bs => afterStrat bs (some b) (some i) flush)
          (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
      intro D f O hD' hv
      obtain ⟨bs, H', e', P⟩ := O H (some i) b flush SP SB fun b' st' x => by rw [uniq b' st' x]; exact hD'
      refine Sat.bind ⟨bs, H', e', fin bs H' P (fun st' d' h' _ => chainOk_vac ?_) hbusy⟩
      obtain ⟨-, -, -, -, k5, k6, -, -⟩ := keeps bs H' P st' h'
      rw [k5, k6]; exact hv
    have runC : ∀ (D : DeflateState → Prop) (f : StatePtr → Int32 → M BlockState), StratOkC D f → D st →
        Sat H (f (some b) flush >>= fun bs => afterStrat bs (some b) (some i) flush)
          (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
      intro D f O hD'
      obtain ⟨bs, H', e', P, hC⟩ := O H (some i) b flush SP SB (fun b' st' x => by rw [uniq b' st' x]; exact hD')
        (fun st' d' x hd' => by rw [uniq b st' x]; exact S5 d' hd')
      exact Sat.bind ⟨bs, H', e', fin bs H' P (fun st' d' h' hd' => hC st' d' (post_state P SB h') hd') hbusy⟩
    refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
    by_cases h0 : (st.level == 0) = true
    · rw [ite_t h0]
      have hl0 : st.level = 0 := by simpa using h0
      exact runP _ _ SF.stored hl0 (.inr (by simp [HASHLESS, hl0]))
    rw [ite_f h0]
    have hl0 : st.level ≠ 0 := by simpa using h0
    have o := c.level
    simp only [dview] at o
    have hpos : 0 < st.level := by
      rcases Int32.lt_or_eq_of_le o.1 with x | x
      · exact x
      · exact absurd x.symm hl0
    by_cases hh : (st.strategy == Z_HUFFMAN_ONLY) = true
    · rw [ite_t hh]
      have hh' : st.strategy = Z_HUFFMAN_ONLY := by simpa using hh
      exact runP _ _ SF.huff ⟨hpos, hh'⟩ (.inr (by simp [HASHLESS, hh']))
    rw [ite_f hh]
    by_cases hr : (st.strategy == Z_RLE) = true
    · rw [ite_t hr]
      have hr' : st.strategy = Z_RLE := by simpa using hr
      exact runP _ _ SF.rle ⟨hpos, hr'⟩ (.inr (by simp [HASHLESS, hr']))
    rw [ite_f hr]
    have hh' : st.strategy ≠ Z_HUFFMAN_ONLY := by simpa using hh
    have hr' : st.strategy ≠ Z_RLE := by simpa using hr
    rw [config_eq _ o.1 o.2]
    refine Sat.bind (Sat.pure ?_)
    obtain ⟨k, hk⟩ := lvl_nat st.level o.1 o.2
    have go : ∀ f : StatePtr → Int32 → M BlockState,
        call_compress configuration_table[st.level.toNatClampNeg]!.func = f →
        Sat H (f (some b) flush >>= fun bs => afterStrat bs (some b) (some i) flush)
          (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) →
        Sat H (call_compress configuration_table[st.level.toNatClampNeg]!.func (some b) flush >>= fun bs =>
          afterStrat bs (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := fun f ef q => by
      rw [ef]; exact q
    have tbl : ∀ lo hi : Int32, lo ≤ st.level → st.level ≤ hi → TableAt lo hi st := fun _ _ x y => ⟨x, y, hh', hr'⟩
    match k, hk with
    | ⟨0, _⟩, hk => exact absurd hk hl0
    | ⟨1, _⟩, hk =>
      refine go ZlibNg.DeflateQuick.deflate_quick (by rw [hk]; rfl) ?_
      exact runP _ _ SF.quick (tbl 1 1 (by rw [hk]; show (1 : Int32) ≤ Int32.ofInt 1; decide)
        (by rw [hk]; show Int32.ofInt 1 ≤ (1 : Int32); decide)) (.inl (by rw [hk]; show Int32.ofInt 1 = 1; decide))
    | ⟨2, _⟩, hk =>
      refine go ZlibNg.DeflateFast.deflate_fast (by rw [hk]; rfl) ?_
      exact runC _ _ SF.fast (tbl 2 2 (by rw [hk]; show (2 : Int32) ≤ Int32.ofInt 2; decide)
        (by rw [hk]; show Int32.ofInt 2 ≤ (2 : Int32); decide))
    | ⟨3, _⟩, hk =>
      refine go ZlibNg.DeflateMedium.deflate_medium (by rw [hk]; rfl) ?_
      exact runC _ _ SF.medium (tbl 3 4 (by rw [hk]; show (3 : Int32) ≤ Int32.ofInt 3; decide)
        (by rw [hk]; show Int32.ofInt 3 ≤ (4 : Int32); decide))
    | ⟨4, _⟩, hk =>
      refine go ZlibNg.DeflateMedium.deflate_medium (by rw [hk]; rfl) ?_
      exact runC _ _ SF.medium (tbl 3 4 (by rw [hk]; show (3 : Int32) ≤ Int32.ofInt 4; decide)
        (by rw [hk]; show Int32.ofInt 4 ≤ (4 : Int32); decide))
    | ⟨5, _⟩, hk =>
      refine go ZlibNg.DeflateMedium.deflate_medium_fizzle (by rw [hk]; rfl) ?_
      exact runC _ _ SF.medium_fizzle (tbl 5 6 (by rw [hk]; show (5 : Int32) ≤ Int32.ofInt 5; decide)
        (by rw [hk]; show Int32.ofInt 5 ≤ (6 : Int32); decide))
    | ⟨6, _⟩, hk =>
      refine go ZlibNg.DeflateMedium.deflate_medium_fizzle (by rw [hk]; rfl) ?_
      exact runC _ _ SF.medium_fizzle (tbl 5 6 (by rw [hk]; show (5 : Int32) ≤ Int32.ofInt 6; decide)
        (by rw [hk]; show Int32.ofInt 6 ≤ (6 : Int32); decide))
    | ⟨7, _⟩, hk =>
      refine go ZlibNg.DeflateSlow.deflate_slow (by rw [hk]; rfl) ?_
      exact runC _ _ SF.slow (tbl 7 9 (by rw [hk]; show (7 : Int32) ≤ Int32.ofInt 7; decide)
        (by rw [hk]; show Int32.ofInt 7 ≤ (9 : Int32); decide))
    | ⟨8, _⟩, hk =>
      refine go ZlibNg.DeflateSlow.deflate_slow (by rw [hk]; rfl) ?_
      exact runC _ _ SF.slow (tbl 7 9 (by rw [hk]; show (7 : Int32) ≤ Int32.ofInt 8; decide)
        (by rw [hk]; show Int32.ofInt 8 ≤ (9 : Int32); decide))
    | ⟨9, _⟩, hk =>
      refine go ZlibNg.DeflateSlow.deflate_slow (by rw [hk]; rfl) ?_
      exact runC _ _ SF.slow (tbl 7 9 (by rw [hk]; show (7 : Int32) ≤ Int32.ofInt 9; decide)
        (by rw [hk]; show Int32.ofInt 9 ≤ (9 : Int32); decide))
    | ⟨n + 10, hn⟩, _ => exact absurd hn (by omega)
  · rw [ite_f hc]
    have hF : 0 < flush → st.status = FINISH_STATE := fun hf => Classical.byContradiction fun hn => hc (by
      have : flush ≠ Z_NO_FLUSH := fun e => by rw [e] at hf; exact absurd hf (by decide)
      simp [this, hn])
    have hai : z.avail_in = 0 := by
      apply Classical.byContradiction; intro hn; exact hc (by simp [hn])
    exact trailer_ok R hst hs hlf (fun hf => (S2 (hF hf)).1) (fun _ => hp0) fun _ => .inl (by rw [aIn_of hz, hai]; rfl)

/-! ## The error returns, the entry, `RANK` -/

theorem strLit_ok' (s : String) (hs : s ∈ strTable) (h : Heap) : ∃ p, strLitRef s h = .ok (p, h) := by
  cases hx : strTable.findIdx? (· == s) with
  | none => exfalso; rw [Array.findIdx?_eq_none_iff] at hx; simpa using hx s hs
  | some j => exact ⟨.ref (.str j) 0, by simp [strLitRef, hx]⟩

theorem zErr_ok (err : Int32) (herr : err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) (H : Heap) :
    ∃ p, ZlibNg.Zutil.zError err H = .ok (p, H) := by
  rcases herr with rfl | rfl
  · have e : ZlibNg.Zutil.zError Z_STREAM_ERROR = strLitRef "stream error" := by
      unfold ZlibNg.Zutil.zError; rfl
    rw [e]; exact strLit_ok' _ (Array.getElem_mem (xs := strTable) (i := 6) (by decide)) H
  · have e : ZlibNg.Zutil.zError Z_BUF_ERROR = strLitRef "buffer error" := by
      unfold ZlibNg.Zutil.zError; rfl
    rw [e]; exact strLit_ok' _ (Array.getElem_mem (xs := strTable) (i := 9) (by decide)) H

/-- `ERR_RETURN` on a `Run` stream: `Run` after, the state kept. -/
theorem err_run {h H : Heap} {i b : Nat} (R : Run h i b H) (err : Int32)
    (herr : err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) :
    Sat H (ERR_RETURN (some i) err) (fun r H' => r = err ∧ Run h i b H' ∧
      (∀ st, H.dstate b = some st → H'.dstate b = some st) ∧ aIn H' i = aIn H i ∧ aOut H' i = aOut H i) := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  obtain ⟨p, ep⟩ := zErr_ok err herr H
  unfold ERR_RETURN
  refine Sat.bind (Sat.of_eq ep ?_)
  rw [← e]
  refine Sat.bind (Sat.of_eq (wrZ_SH _) (Sat.pure ⟨rfl, ?_, fun st' hst' => by
    rw [SH_dstate] at hst' ⊢; exact hst', by rw [aIn_of (SH_streams _ _ _ _ _ _), aIn_of (SH_streams _ _ _ _ _ _)],
    by rw [aOut_of (SH_streams _ _ _ _ _ _), aOut_of (SH_streams _ _ _ _ _ _)]⟩))
  have c' : DCore (SH H i { z with msg := p } b st d) (some i) { z with msg := p } b (dview st) al :=
    DCore.of_heap (by simp [hd]) { c with zalloc := c.zalloc, zfree := c.zfree }
  refine run_SH R hz hst hal c' rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, S2, S3, S4, S5, S6⟩ := R.side st hst
  refine ⟨S1, S2, S3.move (DeflateSide.hdrMove_out rfl fun r hr => DeflateSetDict.space_SH_ne hr), S4,
    fun d' hd' => ?_, S6⟩
  rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'
  exact S5 d hd

/-- The post of `DeflateOk`. -/
def DPost (h h' : Heap) (i : Nat) : Prop :=
  DFrame h h' (streamIds (some i)) (stateIds h (some i)) [] (dOutputRanges h (some i)) ∧
    stateIds h' (some i) = stateIds h (some i) ∧ DInv h' (some i) ∧ DSide h' (some i)

/-- The buffer fields and the `state` field of stream `i` the same in `h'` as in `h`. -/
def SameBuf (h h' : Heap) (i : Nat) : Prop :=
  ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧ z'.next_in = z.next_in ∧ z'.avail_in = z.avail_in ∧
    z'.next_out = z.next_out ∧ z'.avail_out = z.avail_out ∧ z'.state = z.state

/-- `ERR_RETURN` on an invariant stream with `DSide`. -/
theorem err_pre {h : Heap} {i : Nat} (hv : DInv h (some i)) (hs : DSide h (some i)) (err : Int32)
    (herr : err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) :
    Sat h (ERR_RETURN (some i) err) (fun r h' => r = err ∧ DPost h h' i ∧ SameBuf h h' i) := by
  obtain ⟨i', z, b, st, al, e', L, hal, c⟩ := live hv
  obtain rfl := Option.some.inj e'
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of L.hz L.dstate
  obtain ⟨p, ep⟩ := zErr_ok err herr h
  have key : Sat (SH h i z b st d) (ERR_RETURN (some i) err)
      (fun r h' => r = err ∧ DPost (SH h i z b st d) h' i ∧ SameBuf (SH h i z b st d) h' i) := by
    unfold ERR_RETURN
    rw [e]
    refine Sat.bind (Sat.of_eq ep ?_)
    rw [← e]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) (Sat.pure ?_))
    rw [e]
    have hsi : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
    have c' : DCore (SH h i { z with msg := p } b st d) (some i) { z with msg := p } b (dview st) al :=
      DCore.of_heap (by simp [hd]) { c with zalloc := c.zalloc, zfree := c.zfree }
    refine ⟨rfl, ⟨by rw [hsi]; exact dframe_nil _ (DeflateReset.dframe_SH _ _ _ _ _ _), by
      rw [hsi]; simp [stateIds, SH_streams, L.hb], ⟨i, _, b, st, al, rfl, SH_streams _ _ _ _ _ _, L.hb,
      SH_dstate _ _ _ _ _ _, by simpa [Heap.dallocsOf, SH, hd] using hal, c'⟩, ?_⟩, ?_⟩
    · obtain ⟨-, -, -, -, -, S, -⟩ := hs b st ⟨i, z, rfl, L.hz, L.hb, L.dstate⟩
      exact DeflateSide.side_SH hs L.hz L.hb L.dstate L.hb (SideEq.refl _) (S d hd)
    · intro z0 hz0
      rw [← e] at hz0; rw [SH_streams] at hz0; obtain rfl := Option.some.inj hz0
      exact ⟨_, SH_streams _ _ _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩
  rw [e] at key; exact key

/-- `Run` at the entry of `deflate`. -/
theorem run_init {h : Heap} {i b : Nat} {z : ZStream} (hv : DInv h (some i)) (hs : DSide h (some i))
    (hcg : CrcGlobals h) (hio : DStreamIO h (some i)) (hz : h.streams i = some z) (hb : z.state = some b)
    (hno : z.next_out ≠ .null) (hni : z.avail_in ≠ 0 → z.next_in ≠ .null) : Run h i b h := by
  have hio0 := hio
  obtain ⟨z3, b3, hp, ⟨i3, e3, hz3⟩, hb3, -, -, -, hout, -, -⟩ := hio0
  obtain rfl : i = i3 := Option.some.inj e3
  obtain rfl : z = z3 := Option.some.inj (hz.symm.trans hz3)
  obtain ⟨ob, oo, ad, hno', -, -⟩ := hout.resolve_left hno
  refine ⟨hv, hio, ⟨z, ⟨i, rfl, hz⟩, hno, hni⟩, hcg, ⟨z, hz, hb⟩, ⟨z, hz, hb⟩,
    by have := Strategy.dframe_refl h [i] [b] [] (dOutputRanges h (some i)); exact this,
    ⟨z, z, ob, oo, 0, hz, hz, hno', by rw [hno']; rfl, by omega⟩, InTail.refl hz hz rfl rfl, fun st hst => ?_⟩
  obtain ⟨S1, -, S2, S3, S4, S5, S6⟩ := hs b st ⟨i, z, rfl, hz, hb, hst⟩
  exact ⟨S1, S2, S3, S4, S5, S6⟩

/-- `last_flush = flush` (a flush value) keeps `Run`. -/
theorem run_setlf {h H : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} (R : Run h i b H)
    (hz : H.streams i = some z) (hst : H.dstate b = some st) {flush : Int32} (hf0 : 0 ≤ flush) (hf5 : flush ≤ 5) :
    Sat H (wrD (some b) fun s => { s with last_flush := flush }) (fun _ H' => Run h i b H' ∧
      H'.dstate b = some { st with last_flush := flush } ∧ H'.streams i = some z) := by
  obtain ⟨z1, st1, al, d, hz1, hb, hst1, hal, hd, e, c⟩ := R.live
  obtain rfl := Option.some.inj (hst.symm.trans hst1)
  obtain rfl := Option.some.inj (hz.symm.trans hz1)
  rw [← e]
  refine Sat.of_eq (wrD_SH _) ⟨?_, SH_dstate _ _ _ _ _ _, SH_streams _ _ _ _ _ _⟩
  refine run_SH (z' := z) (st' := { st with last_flush := flush }) (d' := d) R hz hst hal
    (DCore.of_heap (by simp [hd]) c) rfl rfl rfl rfl rfl rfl ?_
  obtain ⟨S1, S2, S3, -, S5, S6⟩ := R.side st hst
  refine ⟨S1, S2, S3.move (DeflateSide.hdrMove_out rfl fun r hr => DeflateSetDict.space_SH_ne hr),
    flushOk_of hf0 hf5, fun d' hd' => ?_, ⟨S6.1, S6.2.1, S6.2.2.1, fun e2 => ?_⟩⟩
  · rw [SH_bytes] at hd'; obtain rfl := Option.some.inj hd'
    exact S5 d hd
  · have : flush = -2 := e2
    rw [this] at hf0; exact absurd hf0 (by decide)

theorem rank_eq (f : Int32) (h0 : -2 ≤ f.toInt) (h5 : f.toInt ≤ 5) (H : Heap) :
    RANK f H = .ok (Int32.ofInt (f.toInt * 2 - (if f > 4 then 9 else 0)), H) := by
  have e1 := DeflatePrime.chk_ok (f.toInt * 2) (by omega) (by omega)
  have e2 := DeflatePrime.ofInt_toInt (f.toInt * 2) (by omega) (by omega)
  have e3 := DeflatePrime.chk_ok (f.toInt * 2 - (if f > 4 then 9 else 0)) (by split <;> omega) (by split <;> omega)
  simp only [RANK, bind_app, e1, pure_app, e2, e3]

theorem rank_pos {f o : Int32} (hf : 0 < f.toInt) (hf5 : f.toInt ≤ 5) (ho : -2 ≤ o.toInt)
    (ho5 : o.toInt ≤ 5)
    (hr : Int32.ofInt (f.toInt * 2 - (if f > 4 then 9 else 0)) ≤ Int32.ofInt (o.toInt * 2 - (if o > 4 then 9 else 0))) :
    0 < o.toInt := by
  have t : ∀ x : Int32, -2 ≤ x.toInt → x.toInt ≤ 5 →
      (Int32.ofInt (x.toInt * 2 - (if x > 4 then 9 else 0))).toInt = x.toInt * 2 - (if 4 < x.toInt then 9 else 0) := by
    intro x a1 a2
    have hiff : (x > 4) ↔ 4 < x.toInt := Int32.lt_iff_toInt_lt
    split <;> split <;> rename_i p q
    · exact DeflatePrime.ofInt_toInt _ (by omega) (by omega)
    · exact absurd (hiff.mp p) q
    · exact absurd (hiff.mpr q) p
    · exact DeflatePrime.ofInt_toInt _ (by omega) (by omega)
  have := Int32.le_iff_toInt_le.mp hr
  rw [t f (by omega) hf5, t o ho ho5] at this
  split at this <;> split at this <;> omega

/-! ## `bodyB`, `bodyA` -/

/-- The header and the strategy part of `bodyB` (`deflate.c:1052-1058`). -/
def bodyBt (st : StatePtr) (strm : StreamPtr) (flush : Int32) : M Int32 := do
  let s ← ldDState st
  if s.status != BUSY_STATE && s.status != FINISH_STATE && s.wrap != 0 then
    if (← deflateHeaders st strm) == Z_OK then return Z_OK
  bodyC st strm flush

theorem bodyBt_ok (SF : StrategyFacts) (T : TreesFacts) {h H : Heap} {i b : Nat} {flush : Int32}
    {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st) (hlf : st.last_flush = flush)
    (hf0 : 0 ≤ flush) (hf5 : flush ≤ 5) (hp0 : st.pending = 0) (hni : ¬ (st.status = INIT_STATE ∧ st.wrap = 0))
    (hfa : st.status = FINISH_STATE → ∀ z, H.streams i = some z → z.avail_in = 0) :
    Sat H (bodyBt (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
  unfold bodyBt
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  by_cases hc : (st.status != BUSY_STATE && st.status != FINISH_STATE && st.wrap != 0) = true
  · rw [ite_t hc]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨hs1, hs2⟩, -⟩ := hc
    refine Sat.bind (Sat.mono (headers_ok R hst hs1 hs2 hp0) ?_)
    rintro r H2 ⟨R2, q1, q2⟩
    by_cases hr : (r == Z_OK) = true
    · rw [ite_t hr]
      have q := q1 (by simpa using hr)
      obtain ⟨z2, -, -, -, hz2, -⟩ := R2.live
      exact Sat.pure ⟨R2, lfok_m1 q, DIO.o0 (by rw [aOut_of hz2, q.2 z2 hz2]; rfl)⟩
    · rw [ite_f hr]
      obtain ⟨z2, st2, -, -, -, -, hst2, -, -, -, -⟩ := R2.live
      obtain ⟨a1, a2, -, a4⟩ := q2 (by simpa using hr) st2 hst2
      exact bodyC_ok SF T R2 hst2 (.inl a1) (a4.trans hlf) hf0 hf5 a2 (fun x => absurd (a1.symm.trans x) (by decide))
  · rw [ite_f hc]
    have hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE := by
      obtain ⟨z, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
      obtain rfl := Option.some.inj (hst.symm.trans hst1)
      obtain ⟨hw, -⟩ := (R.side st hst).2.2.1
      have hlo := Int32.le_iff_toInt_le.mp c.status_lo
      have hhi := Int32.le_iff_toInt_le.mp c.status_hi
      simp only [dview] at hlo hhi
      have t : ∀ x : Int32, st.status = x ∨ st.status.toInt ≠ x.toInt := fun x => by
        by_cases e : st.status = x
        · exact .inl e
        · exact .inr fun e' => e (Int32.toInt_inj.mp e')
      rcases t BUSY_STATE with e2 | e2
      · exact .inl e2
      rcases t FINISH_STATE with e3 | e3
      · exact .inr e3
      exfalso
      have n2 : st.status ≠ BUSY_STATE := fun x => e2 (by rw [x])
      have n3 : st.status ≠ FINISH_STATE := fun x => e3 (by rw [x])
      have hw0 : st.wrap = 0 := Classical.byContradiction fun hw => hc (by simp [n2, n3, hw])
      rcases t INIT_STATE with e1 | e1
      · exact hni ⟨e1, hw0⟩
      have hw2 : st.wrap = 2 := by
        apply hw
        have a2 : BUSY_STATE.toInt = 2 := rfl
        have a3 : FINISH_STATE.toInt = 3 := rfl
        have a1 : INIT_STATE.toInt = 1 := rfl
        have a4 : GZIP_STATE.toInt = 4 := rfl
        have a8 : MAX_STATE.toInt = 8 := rfl
        rw [a2] at e2; rw [a3] at e3; rw [a1] at e1; rw [a8] at hhi
        have l1 : INIT_STATE.toInt = 1 := rfl
        rw [l1] at hlo
        rcases (by omega : st.status.toInt = 4 ∨ st.status.toInt = 5 ∨ st.status.toInt = 6 ∨ st.status.toInt = 7 ∨
            st.status.toInt = 8) with x | x | x | x | x
        · exact .inl (Int32.toInt_inj.mp (x.trans a4.symm))
        · exact .inr (.inl (Int32.toInt_inj.mp (x.trans rfl)))
        · exact .inr (.inr (.inl (Int32.toInt_inj.mp (x.trans rfl))))
        · exact .inr (.inr (.inr (.inl (Int32.toInt_inj.mp (x.trans rfl)))))
        · exact .inr (.inr (.inr (.inr (Int32.toInt_inj.mp (x.trans rfl)))))
      rw [hw0] at hw2; exact absurd hw2 (by decide)
    exact bodyC_ok SF T R hst hs hlf hf0 hf5 hp0 hfa

/-- **`bodyB`**. -/
theorem bodyB_ok (SF : StrategyFacts) (T : TreesFacts) {h H : Heap} {i b : Nat} {flush : Int32} {z : ZStream}
    {st : DeflateState} (R : Run h i b H) (hz : H.streams i = some z) (hst : H.dstate b = some st)
    (hlf : st.last_flush = flush) (hf0 : 0 ≤ flush) (hf5 : flush ≤ 5) (hp0 : st.pending = 0)
    (hfs : st.status = FINISH_STATE → flush = Z_FINISH) :
    Sat H (bodyB (some b) (some i) flush) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
  obtain ⟨S1, S2, -, -, -, -⟩ := R.side st hst
  unfold bodyB
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
  by_cases hc : (st.status == FINISH_STATE && z.avail_in != 0) = true
  · rw [ite_t hc]
    have hF : st.status = FINISH_STATE := by simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1
    exact Sat.mono (err_run R Z_BUF_ERROR (.inr rfl)) fun _ H' ⟨hr, R', k, _, _⟩ => ⟨R', (fun st' h' _ => by
      obtain rfl := Option.some.inj ((k st hst).symm.trans h'); exact (S2 hF).1),
      DIO.err (by rw [hr]; decide) fun hf => absurd (hfs hF) hf⟩
  rw [ite_f hc]
  have hfa : st.status = FINISH_STATE → ∀ z', H.streams i = some z' → z'.avail_in = 0 := fun x z' hz' => by
    obtain rfl := Option.some.inj (hz.symm.trans hz')
    simpa [x] using hc
  refine Sat.bind (Sat.of_eq (ldDState_app hst) ?_)
  by_cases hI : (st.status == INIT_STATE && st.wrap == 0) = true
  · rw [ite_t hI]
    simp only [Bool.and_eq_true, beq_iff_eq] at hI
    obtain ⟨z1, st1, al, d, -, -, hst1, -, -, -, c⟩ := R.live
    obtain rfl := Option.some.inj (hst.symm.trans hst1)
    have h0 : st.sym_next = 0 := c.hdr (show st.status ≠ BUSY_STATE by rw [hI.1]; decide)
      (show st.status ≠ FINISH_STATE by rw [hI.1]; decide)
    obtain ⟨z', d', pbo, e', SS⟩ := segS_of R hst h0 (c.pout hp0)
    rw [← e']
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    have R' := seg_run SS.run SS.pb SS.sym SS.pout z'.adler st.pending BUSY_STATE st.gzindex rfl (fun _ _ => rfl)
      (by rw [hp0]; simp) (by decide) (by decide) (by decide) (hdrOk_busy (.inl rfl))
    exact bodyBt_ok SF T R' (SH_dstate _ _ _ _ _ _) hlf hf0 hf5 hp0 (fun x => absurd x.1 (by show ¬ (BUSY_STATE = INIT_STATE); decide))
      (fun x => absurd x (by show ¬ (BUSY_STATE = FINISH_STATE); decide))
  · rw [ite_f hI]
    exact bodyBt_ok SF T R hst hlf hf0 hf5 hp0 (fun x => hI (by simp [x.1, x.2])) hfa

/-- **`bodyA`**. -/
theorem bodyA_ok (SF : StrategyFacts) (T : TreesFacts) {h H : Heap} {i b : Nat} {flush old : Int32} {z : ZStream}
    {st : DeflateState} (R : Run h i b H) (hz : H.streams i = some z) (hst : H.dstate b = some st)
    (hlf : st.last_flush = flush) (hf0 : 0 ≤ flush) (hf5 : flush ≤ 5) (ho : -2 ≤ old) (ho5 : old ≤ 5)
    (hold : 0 < old → st.sym_next = 0) (hfs : st.status = FINISH_STATE → flush = Z_FINISH) :
    Sat H (bodyA (some b) (some i) flush old) (fun r H' => Run h i b H' ∧ LFok H' b ∧ DIO h H' i flush r) := by
  unfold bodyA
  refine Sat.bind (Sat.of_eq (rdD_dst hst _) ?_)
  by_cases hp : (st.pending != 0) = true
  · rw [ite_t hp]
    obtain ⟨H2, e2, R2, k⟩ := run_flush R.w
    obtain ⟨z2, st2, hz2, hst2, hse, -, hpz, -⟩ := k z st hz hst
    refine Sat.bind ⟨(), H2, e2, ?_⟩
    refine Sat.bind (Sat.of_eq (rdZ_app hz2 _) ?_)
    by_cases ha : (z2.avail_out == 0) = true
    · rw [ite_t ha]
      have ha0 : z2.avail_out = 0 := by simpa using ha
      exact Sat.bind (Sat.mono (run_lf R2 fun z' hz' => by
        obtain rfl := Option.some.inj (hz2.symm.trans hz'); exact ha0) fun _ H3 q => Sat.pure ⟨q.1, lfok_m1 q.2,
          DIO.o0 (by obtain ⟨z3, -, -, -, hz3, -⟩ := q.1.live; rw [aOut_of hz3, q.2.2 z3 hz3]; rfl)⟩)
    · rw [ite_f ha]
      exact bodyB_ok SF T R2 hz2 hst2 (by rw [hse]; exact hlf) hf0 hf5 (hpz (by simpa using ha))
        fun x => hfs (by rw [hse] at x; exact x)
  · rw [ite_f hp]
    have hp0 : st.pending = 0 := by simpa using hp
    refine Sat.bind (Sat.of_eq (rdZ_app hz _) ?_)
    have i0 := Int32.le_iff_toInt_le.mp hf0
    have i5 := Int32.le_iff_toInt_le.mp hf5
    have j0 := Int32.le_iff_toInt_le.mp ho
    have j5 := Int32.le_iff_toInt_le.mp ho5
    have c5 : (5 : Int32).toInt = 5 := rfl
    have c0 : (0 : Int32).toInt = 0 := rfl
    have c2 : (-2 : Int32).toInt = -2 := rfl
    rw [c0] at i0; rw [c5] at i5; rw [c2] at j0; rw [c5] at j5
    refine Sat.bind (Sat.of_eq (rank_eq flush (by omega) (by omega) _) ?_)
    refine Sat.bind (Sat.of_eq (rank_eq old j0 j5 _) ?_)
    by_cases hc : (z.avail_in == 0 && decide (Int32.ofInt (flush.toInt * 2 - (if flush > 4 then 9 else 0)) ≤
        Int32.ofInt (old.toInt * 2 - (if old > 4 then 9 else 0))) && flush != Z_FINISH) = true
    · rw [ite_t hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hc0, hr⟩, -⟩ := hc
      have hz0 : aIn H i = 0 := by
        rw [aIn_of hz]; simp only [beq_iff_eq] at hc0; rw [hc0]; rfl
      exact Sat.mono (err_run R Z_BUF_ERROR (.inr rfl)) fun _ H' ⟨hre, R', k, ka, _⟩ => ⟨R', (fun st' h' hl => by
        obtain rfl := Option.some.inj ((k st hst).symm.trans h')
        rw [hlf] at hl
        have := Int32.lt_iff_toInt_lt.mp hl
        rw [c0] at this
        exact hold (Int32.lt_iff_toInt_lt.mpr (by rw [c0]; exact rank_pos this i5 j0 j5 hr))),
        DIO.err (by rw [hre]; decide) fun _ _ => .inl (ka.trans hz0)⟩
    · rw [ite_f hc]
      exact bodyB_ok SF T R hz hst hlf hf0 hf5 hp0 hfs

/-! ## `deflate` -/

/-- **`deflate`**, given the strategies: the post of `DeflateOk`, and either the call ran (`Run`, `DIO`, from an
output with room) or it returned at an argument check (`Z_STREAM_ERROR`, or `Z_BUF_ERROR` with a full output) with
the buffer fields and the `state` field unchanged. -/
theorem deflate_okX (SF : StrategyFacts) {h : Heap} {i : Nat} {flush : Int32} (hv : DInv h (some i))
    (hs : DSide h (some i)) (hcg : CrcGlobals h) (hio : DStreamIO h (some i)) :
    Sat h (ZlibNg.Deflate.deflate (some i) flush) (fun r h' => DPost h h' i ∧
      ((∃ b, Run h i b h' ∧ DIO h h' i flush r ∧ aOut h i ≠ 0) ∨
        (SameBuf h h' i ∧ (r = Z_STREAM_ERROR ∨ (r = Z_BUF_ERROR ∧ aOut h i = 0))))) := by
  obtain ⟨i', z, b, st, al, e', L, hal, c⟩ := live hv
  obtain rfl := Option.some.inj e'
  have T := ZlibNgF.Proof.TreesFactsP.treesFacts
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
  have same : SameBuf h h i := fun z0 hz0 => ⟨z0, hz0, rfl, rfl, rfl, rfl, rfl⟩
  rw [deflate_eq]
  refine Sat.bind (Sat.of_eq L.check ?_)
  split
  · exact Sat.pure ⟨⟨by rw [hsi]; exact Strategy.dframe_refl _ _ _ _ _, rfl, hv, hs⟩, .inr ⟨same, .inl rfl⟩⟩
  rename_i hfl
  have hf5 : flush ≤ Z_BLOCK := Classical.byContradiction fun x => hfl (by simp [Int32.not_le.mp x])
  have hf0 : 0 ≤ flush := Classical.byContradiction fun x => hfl (by simp [Int32.not_le.mp x])
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.InflateInv.ldStream_app L.hz) ?_)
  refine Sat.bind (Sat.of_eq (ldDState_app L.dstate) ?_)
  split
  · exact Sat.mono (err_pre hv hs _ (.inl rfl)) fun _ _ ⟨rfl, q1, q2⟩ => ⟨q1, .inr ⟨q2, .inl rfl⟩⟩
  rename_i hc
  split
  · rename_i ha
    have ha0 : aOut h i = 0 := by rw [aOut_of L.hz]; simp only [beq_iff_eq] at ha; rw [ha]; rfl
    exact Sat.mono (err_pre hv hs _ (.inr rfl)) fun _ _ ⟨rfl, q1, q2⟩ => ⟨q1, .inr ⟨q2, .inr ⟨rfl, ha0⟩⟩⟩
  rename_i ha
  have ha0 : aOut h i ≠ 0 := by
    rw [aOut_of L.hz]; intro e0; apply ha; simp only [beq_iff_eq]; exact UInt32.toNat_inj.mp (by rw [e0]; rfl)
  have hno : z.next_out ≠ .null := fun x => hc (by simp [x])
  have hni : z.avail_in ≠ 0 → z.next_in ≠ .null := fun x y => hc (by simp [x, y])
  have hfs : st.status = FINISH_STATE → flush = Z_FINISH := fun x => Classical.byContradiction fun y => hc (by simp [x, y])
  obtain ⟨S1, Slf, S2, S3, ⟨f1, f2, -⟩, S5, S6⟩ := hs b st ⟨i, z, rfl, L.hz, L.hb, L.dstate⟩
  have R0 := run_init hv hs hcg hio L.hz L.hb hno hni
  refine Sat.bind (Sat.mono (run_setlf R0 L.hz L.dstate hf0 hf5) ?_)
  rintro _ H1 ⟨R1, hst1, hz1⟩
  exact Sat.mono (bodyA_ok SF T R1 hz1 hst1 rfl hf0 hf5 f1 f2 Slf hfs) fun _ H' ⟨R', l, d⟩ =>
    ⟨Run.done R' l, .inl ⟨b, R', d, ha0⟩⟩

/-- **`deflate`** satisfies `DeflateOk`, given the strategies (`StrategyFacts`). -/
theorem deflate_ok (SF : StrategyFacts) : DeflateParams.DeflateOk := by
  intro h s flush hv hs hcg hio
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  obtain ⟨r, h', e, q, -⟩ := deflate_okX SF (flush := flush) hv hs hcg hio
  exact ⟨r, h', e, q⟩

/-- The obligations of the reachability induction, given the strategies. -/
theorem dpending (SF : StrategyFacts) : DeflateReach.DPending := ⟨deflate_ok SF⟩

end ZlibNgF.Proof.DeflateBody
