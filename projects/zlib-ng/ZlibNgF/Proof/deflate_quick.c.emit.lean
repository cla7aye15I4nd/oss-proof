import ZlibNgF.Proof.«deflate_quick.c.tally»
import ZlibNgF.Proof.«deflate_rle.c.safety»

/-!
# `deflate_quick` with tallied symbols: the block end and the emitters (`ZlibNgF`)

On the tallying path (`static_emit == 0`): `quick_end_block` (`qeb_ok`: `FLUSH_BLOCK_ONLY` when symbols wait or for
the last block, then the output test), `quick_emit_lit` (`qlit_ok`) and `quick_emit_dist` (`qdist_ok`): a tally, and
the block end when the symbol buffer is full. A result `true` of an emitter is the return `need_more` of
`deflate_quick_impl` (`QE`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.QuickP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateQuick

/-- `s->strm` of a stream under `SLF`. -/
theorem strmOf_slf {h H : Heap} {i b : Nat} (F : SLF h i b H) : strmOf (some b) H = .ok (some i, H) := by
  obtain ⟨z, st, al, hz, hb, hst, -, c⟩ := F.live
  have hs : st.strm = .val (some i) := c.strm
  simp [strmOf, ldDState_app hst, bind_app, hs, Ival.get]

/-- `sym_end` is not 0. -/
theorem symend_pos {h H : Heap} {i b : Nat} (F : SLF h i b H) {st : DeflateState} (hst : H.dstate b = some st) :
    0 < st.sym_end.toNat := by
  obtain ⟨z, st1, al, hz, hb, hst1, -, c⟩ := F.live
  obtain rfl : st1 = st := Option.some.inj (hst1.symm.trans hst)
  obtain ⟨-, -, -, hl, -, -, hse⟩ := c.sizes
  simp only [dview] at hl hse
  omega

/-- `quick_end_block(s, strstart, last, 0)` from `SLF` with no pending bytes (`deflate_quick.c:32-50`): `SLF` after,
`lookahead` and `strstart` kept, room for a symbol, no pending bytes when it returns `false`, and no symbols. -/
theorem qeb_ok (T : TreesFacts) {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8}
    (ss : UInt32) (last : Int32) (hl0 : 0 ≤ last) (hl1 : last ≤ 1)
    (F : SLF h i b (SH H0 i z b st d)) (hp : st.pending = 0) (hw : st.window = .val (.ref (.heap b) wo)) :
    Sat (SH H0 i z b st d) (quick_end_block (some b) ss last 0) (fun r H2 => avIn H2 i = z.avail_in.toNat ∧
      SLF h i b H2 ∧ ∀ st2, H2.dstate b = some st2 → st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
        st2.sym_next < st2.sym_end ∧ (r = false → st2.pending = 0) ∧ st2.sym_next = 0) := by
  have fl : Sat (SH H0 i z b st d) (do
      FLUSH_BLOCK_ONLY (some b) (do (← rdD (some b) (·.window)).get) last
      return (← rdZ (← strmOf (some b)) (·.avail_out)) == 0) (fun r H2 => avIn H2 i = z.avail_in.toNat ∧
      SLF h i b H2 ∧ ∀ st2, H2.dstate b = some st2 → st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
        st2.sym_next < st2.sym_end ∧ (r = false → st2.pending = 0) ∧ st2.sym_next = 0) := by
    refine Sat.bind (Sat.mono (slf_flush_only T (wo := wo) _ last hl0 hl1 F (fun st1 h1 => ?_) ?_) ?_)
    · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
      exact ⟨hp, hw⟩
    · simp [rdD_SH, hw, Ival.get, bind_app]
    rintro _ H2 ⟨hav, F2, hs2, hpz⟩
    obtain ⟨z2, st2, -, hz2, -, hst2, -, -⟩ := F2.live
    refine Sat.bind (Sat.of_eq (strmOf_slf F2) (Sat.bind (Sat.of_eq (rdZ_app hz2 _) (Sat.pure ?_))))
    refine ⟨by rw [hav, avIn_SH], F2, fun st3 h3 => ?_⟩
    obtain rfl := Option.some.inj (hst2.symm.trans h3)
    obtain ⟨e0, e1, st1, h1, e2, e3, -⟩ := hs2 st2 hst2
    obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h1)
    refine ⟨e2, e3, e1, fun hr => hpz z2 st2 hz2 hst2 ?_, e0⟩
    intro e; simp [e] at hr
  unfold quick_end_block
  simp only [show ((0 : Int32) == 0) = true from rfl, ↓reduceIte]
  by_cases hl : (last != 0) = true
  · simp only [hl, ↓reduceIte, ZlibNgF.Proof.DeflateAlloc.pure_bind_M]
    exact fl
  · simp only [hl, Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.bind (Sat.of_eq ldDState_SH (Sat.pure ?_)))
    by_cases hs : (st.sym_next != 0) = true
    · simp only [hs]
      exact fl
    · simp only [hs]
      have h0 : st.sym_next = 0 := by simpa using hs
      have hl' : last = 0 := by simpa using hl
      refine Sat.pure ⟨avIn_SH _ _ _ _ _ _, F, fun st2 h2 => ?_⟩
      obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
      have := symend_pos F (SH_dstate _ _ _ _ _ _)
      refine ⟨rfl, rfl, ?_, fun _ => hp, h0⟩
      rw [h0]; exact UInt32.lt_iff_toNat_lt.mpr (by simpa using this)

/-- The result of an emitter `(r, strstart, lookahead)` on the tallying path: the loop invariant when `r` is `false`,
`StratPost` for the return `need_more` when it is `true`. -/
def QE (h : Heap) (i b : Nat) (flush : Int32) (v : Bool × UInt32 × UInt32) (H : Heap) : Prop :=
  (v.1 = false → SLI h i b v.2.2 v.2.1 H) ∧ (v.1 = true → StratPost h (some i) flush .need_more H)

/-- `QE` from the facts after `quick_end_block(s, strstart, 0, 0)`. -/
theorem qe_of {h H2 : Heap} {i b : Nat} {flush : Int32} {r : Bool} {la ss : UInt32}
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED) (F2 : SLF h i b H2)
    (hs : ∀ st2, H2.dstate b = some st2 → st2.lookahead = la ∧ st2.strstart = ss ∧ st2.sym_next < st2.sym_end ∧
      (r = false → st2.pending = 0) ∧ (r = true → st2.sym_next = 0)) : QE h i b flush (r, ss, la) H2 := by
  obtain ⟨z2, st2, -, hz2, -, hst2, -, -⟩ := F2.live
  obtain ⟨e1, e2, e3, e4, e5⟩ := hs st2 hst2
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · have C : SLC h i b H2 := ⟨F2, fun st4 h4 => by
      obtain rfl := Option.some.inj (hst2.symm.trans h4)
      exact ⟨e4 hr, e3⟩⟩
    have := sli_of_slc C hst2
    rw [e1, e2] at this
    exact this
  · refine slf_post F2 _ _ hn fun st4 h4 => ?_
    obtain rfl := Option.some.inj (hst2.symm.trans h4)
    unfold ExitOk
    exact ⟨e3, fun e => (by rcases e with e | e <;> cases e), fun _ => e5 hr,
      fun e => (by rcases e with e | e <;> cases e)⟩

/-- After a tally that filled the symbol buffer: write the locals back and `quick_end_block(s, strstart, 0, 0)`. -/
theorem slw_end (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss : UInt32}
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (W : SLW h i b la ss H) :
    Sat H (do
      wrD (some b) fun s => { s with strstart := ss, lookahead := la }
      return (← quick_end_block (some b) ss 0 0, ss, la)) (fun v H2 => QE h i b flush v H2 ∧ v.2.1 = ss ∧
        v.2.2 = la ∧ avIn H2 i = avIn H i) := by
  obtain ⟨H0, z, st, d, rfl, F, hp0⟩ := W
  refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
  obtain ⟨st0, hst0, hw⟩ := F.win
  have hwin : (FS st la ss).window = .val (.ref (.heap b) wo) := by
    rw [hw _ (SH_dstate _ _ _ _ _ _)]; exact hw0 st0 hst0
  refine Sat.bind (Sat.mono (qeb_ok T ss 0 (by decide) (by decide) F hp0 hwin) ?_)
  rintro r H2 ⟨hav, F2, hs2⟩
  refine Sat.pure ⟨qe_of hn F2 fun st2 h2 => ?_, rfl, rfl, by rw [hav, avIn_SH]⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := hs2 st2 h2
  exact ⟨e1, e2, e3, e4, fun _ => e5⟩

/-- `quick_emit_lit(s, lit, &strstart, &lookahead, 0)` (`deflate_quick.c:87-104`) in the loop. -/
theorem qlit_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss : UInt32}
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H)
    (hl : 1 ≤ la.toNat) (lit : UInt8) :
    Sat H (quick_emit_lit (some b) lit ss la 0) (fun v H2 => QE h i b flush v H2 ∧ v.2.1 = ss + 1 ∧
      v.2.2 = la - 1 ∧ avIn H2 i = avIn H i) := by
  unfold quick_emit_lit
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.mono (sli_tally_lit I hl lit) ?_)
  rintro r H1 ⟨ha, W, I1⟩
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨⟨fun _ => I1 rfl, fun e => by cases e⟩, rfl, rfl, ha⟩
  | true =>
    simp only [↓reduceIte]
    refine Sat.mono (slw_end T hn hw0 W) fun v H2 ⟨q, e1, e2, e3⟩ => ⟨q, e1, e2, e3.trans ha⟩

/-- `quick_emit_dist(s, match_len, dist, &strstart, &lookahead, 0)` (`deflate_quick.c:107-124`) in the loop, with
`match_len` 3..258 and at most `lookahead`, and `dist` 1..32768. -/
theorem qdist_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss : UInt32}
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H)
    (ml dist : UInt32) (hm3 : 3 ≤ ml.toNat) (hm : ml.toNat ≤ 258) (hml : ml.toNat ≤ la.toNat)
    (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768) :
    Sat H (quick_emit_dist (some b) ml dist ss la 0) (fun v H2 => QE h i b flush v H2 ∧ v.2.1 = ss + ml ∧
      v.2.2 = la - ml ∧ avIn H2 i = avIn H i) := by
  unfold quick_emit_dist
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hsub : (ml - STD_MIN_MATCH).toNat = ml.toNat - 3 :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simpa [STD_MIN_MATCH] using hm3))
  refine Sat.bind (Sat.mono (sli_tally_dist I dist (ml - STD_MIN_MATCH) ml (by rw [hsub]; omega) hd1 hd2
    (by omega) hm hml) ?_)
  rintro r H1 ⟨ha, W, I1⟩
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Sat.pure ⟨⟨fun _ => I1 rfl, fun e => by cases e⟩, rfl, rfl, ha⟩
  | true =>
    simp only [↓reduceIte]
    refine Sat.mono (slw_end T hn hw0 W) fun v H2 ⟨q, e1, e2, e3⟩ => ⟨q, e1, e2, e3.trans ha⟩

end ZlibNgF.Proof.QuickP
