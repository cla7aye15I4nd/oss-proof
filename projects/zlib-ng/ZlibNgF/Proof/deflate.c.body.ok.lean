import ZlibNgF.Proof.«deflate.c.body.after»

/-!
# `deflate`: the strategy call and the whole call (`ZlibNgF`)

`bodyC_ok`: the dispatch of `deflate` to a strategy (`StrategyFacts`) and what follows it (`after_ok`), or the trailer.
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

/-- **The strategy part** (`bodyC`). -/
theorem bodyC_ok (SF : StrategyFacts) (T : TreesFacts) {h H : Heap} {i b : Nat} {flush : Int32}
    {st : DeflateState} (R : Run h i b H) (hst : H.dstate b = some st)
    (hs : st.status = BUSY_STATE ∨ st.status = FINISH_STATE) (hlf : st.last_flush = flush) (hf0 : 0 ≤ flush)
    (hf5 : flush ≤ 5) (hp0 : st.pending = 0)
    (hfa : st.status = FINISH_STATE → ∀ z, H.streams i = some z → z.avail_in = 0) :
    Sat H (bodyC (some b) (some i) flush) (fun _ H' => Run h i b H' ∧ LFok H' b) := by
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
      Sat H' (afterStrat bs (some b) (some i) flush) (fun _ H' => Run h i b H' ∧ LFok H' b) := by
    intro bs H' P hC hbusy
    obtain ⟨R', K⟩ := run_post R hst hbusy (by rw [hlf]; exact hf0) P hC
    exact after_ok T R' fun st' h' => by
      obtain ⟨k1, k2, k3, k4, k5⟩ := K st' h'
      obtain ⟨s1, -, -, -, -, -, s7, -⟩ := k1
      exact ⟨s1.trans hbusy, s7.trans hlf, k2, k3, k4, k5⟩
  have keeps : ∀ (bs : BlockState) H', StratPost H (some i) flush bs H' → ∀ st', H'.dstate b = some st' →
      StratKeeps st st' := fun bs H' P st' h' => (P.2.2.2.2.2.2.2 b st st' hD (post_state P SB h')).2.1
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
          (fun _ H' => Run h i b H' ∧ LFok H' b) := by
      intro D f O hD' hv
      obtain ⟨bs, H', e', P⟩ := O H (some i) b flush SP SB fun b' st' x => by rw [uniq b' st' x]; exact hD'
      refine Sat.bind ⟨bs, H', e', fin bs H' P (fun st' d' h' _ => chainOk_vac ?_) hbusy⟩
      obtain ⟨-, -, -, -, k5, k6, -, -⟩ := keeps bs H' P st' h'
      rw [k5, k6]; exact hv
    have runC : ∀ (D : DeflateState → Prop) (f : StatePtr → Int32 → M BlockState), StratOkC D f → D st →
        Sat H (f (some b) flush >>= fun bs => afterStrat bs (some b) (some i) flush)
          (fun _ H' => Run h i b H' ∧ LFok H' b) := by
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
          (fun _ H' => Run h i b H' ∧ LFok H' b) →
        Sat H (call_compress configuration_table[st.level.toNatClampNeg]!.func (some b) flush >>= fun bs =>
          afterStrat bs (some b) (some i) flush) (fun _ H' => Run h i b H' ∧ LFok H' b) := fun f ef q => by
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
    exact trailer_ok R hst hs hlf (fun hf => (S2 (hF hf)).1) (fun _ => hp0)

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
    Sat H (ERR_RETURN (some i) err) (fun _ H' => Run h i b H' ∧ ∀ st, H.dstate b = some st → H'.dstate b = some st) := by
  obtain ⟨z, st, al, d, hz, hb, hst, hal, hd, e, c⟩ := R.live
  obtain ⟨p, ep⟩ := zErr_ok err herr H
  unfold ERR_RETURN
  refine Sat.bind (Sat.of_eq ep ?_)
  rw [← e]
  refine Sat.bind (Sat.of_eq (wrZ_SH _) (Sat.pure ⟨?_, fun st' hst' => by
    rw [SH_dstate] at hst' ⊢; exact hst'⟩))
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

/-- `ERR_RETURN` on an invariant stream with `DSide`. -/
theorem err_pre {h : Heap} {i : Nat} (hv : DInv h (some i)) (hs : DSide h (some i)) (err : Int32)
    (herr : err = Z_STREAM_ERROR ∨ err = Z_BUF_ERROR) :
    Sat h (ERR_RETURN (some i) err) (fun _ h' => DPost h h' i) := by
  obtain ⟨i', z, b, st, al, e', L, hal, c⟩ := live hv
  obtain rfl := Option.some.inj e'
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of L.hz L.dstate
  obtain ⟨p, ep⟩ := zErr_ok err herr h
  have key : Sat (SH h i z b st d) (ERR_RETURN (some i) err) (fun _ h' => DPost (SH h i z b st d) h' i) := by
    unfold ERR_RETURN
    rw [e]
    refine Sat.bind (Sat.of_eq ep ?_)
    rw [← e]
    refine Sat.bind (Sat.of_eq (wrZ_SH _) (Sat.pure ?_))
    rw [e]
    have hsi : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
    have c' : DCore (SH h i { z with msg := p } b st d) (some i) { z with msg := p } b (dview st) al :=
      DCore.of_heap (by simp [hd]) { c with zalloc := c.zalloc, zfree := c.zfree }
    refine ⟨by rw [hsi]; exact dframe_nil _ (DeflateReset.dframe_SH _ _ _ _ _ _), by
      rw [hsi]; simp [stateIds, SH_streams, L.hb], ⟨i, _, b, st, al, rfl, SH_streams _ _ _ _ _ _, L.hb,
      SH_dstate _ _ _ _ _ _, by simpa [Heap.dallocsOf, SH, hd] using hal, c'⟩, ?_⟩
    obtain ⟨-, -, -, -, -, S, -⟩ := hs b st ⟨i, z, rfl, L.hz, L.hb, L.dstate⟩
    exact DeflateSide.side_SH hs L.hz L.hb L.dstate L.hb (SideEq.refl _) (S d hd)
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
    ⟨z, z, ob, oo, 0, hz, hz, hno', by rw [hno']; rfl, by omega⟩, fun st hst => ?_⟩
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

end ZlibNgF.Proof.DeflateBody
