import ZlibNgF.Proof.«deflate.c.side»
import ZlibNgF.Proof.«public-deflate-init»
import ZlibNgF.Proof.«deflate_p.h.tally.flush»

/-!
# `deflateParams` (`ZlibNgF`)

`params_ok (D : DeflateOk)`: `deflateParams` on an invariant stream with `DSide`, the CRC tables and valid buffers
does not fault, writes only the output buffer, the stream record and the stream's block, and keeps the invariant
and `DSide`, given `DeflateOk` (the same of `deflate`, which `deflateParams` calls with `Z_BLOCK` before a switch of
strategy or of compression function).

The tail of `deflateParams` (`paramsTail`) runs on a state that may switch (`SwitchOk`): the strategy and the
compression function stay, or there is no lookahead and no unfinished block (after the `Z_BLOCK` flush and the
check `strstart - block_start + lookahead == 0`, or because `last_flush == -2`). The tail clears `head` on a stale
chain (`stale_chain && !hashless`: `CLEAR_HASH`, `ins_h = 0`, `insert = MIN(strstart, w_size)`), calls
`lm_set_level` on a new level, and stores the strategy.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateParams
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateFacts (ChainOk chainLim posAt SymsOk DStateIs)
open ZlibNgF.Proof.DeflateSide (DSide SideAt FlushOk HdrOk)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.ChunkMem (fillFold fillFold_size fillFold_get)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)
open ZlibNgF.Proof.DeflateSetDict (clear_hash_SH)
open ZlibNgF.Proof.DeflateReset (dframe_SH)
open ZlibNgF.Proof.FlushBlock (dframe_nil)
open ZlibNgF.Proof.DeflateSetDict (DFrame.trans)

/-- What `deflate` is to satisfy for `deflateParams`: on an invariant stream with `DSide`, the CRC tables and valid
buffers, no fault, a write of the output buffer, the stream record and the stream's block only, the same state
block, the invariant and `DSide`. -/
def DeflateOk : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (flush : Int32), DInv h s → DSide h s → CrcGlobals h → DStreamIO h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧ stateIds h' s = stateIds h s ∧
      DInv h' s ∧ DSide h' s

/-- The tail of `deflateParams` (`deflate.c:656-673`). -/
def paramsTail (st : StatePtr) (level strategy : Int32) : M Int32 := do
  let s ← ldDState st
  let hashless := HASHLESS level strategy
  let was_hashless := HASHLESS s.level s.strategy
  let stale_chain := (hashless != was_hashless) || ((level ≥ MIN_ROLL_LEVEL) != (s.level ≥ MIN_ROLL_LEVEL)) ||
    (s.level == 1 && level != 1)
  if stale_chain && !hashless then
    CLEAR_HASH st
    wrD st fun s => { s with ins_h := 0 }
    wrD st fun s => { s with insert := if s.strstart > s.w_size then s.w_size else s.strstart }
  if (← rdD st (·.level)) != level then
    lm_set_level st level
  wrD st fun s => { s with strategy := strategy }
  return Z_OK

theorem params_eq (f : StreamPtr → Int32 → M Int32) (strm : StreamPtr) (level strategy : Int32) :
    deflateParamsWith f strm level strategy = (do
      let hook_flush : Int32 := Z_NO_FLUSH
      if ← deflateStateCheck strm then return Z_STREAM_ERROR
      let st ← dstateOf strm
      let level := if level == Z_DEFAULT_COMPRESSION then 6 else level
      if level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED then return Z_STREAM_ERROR
      let s ← ldDState st
      let func := (← config s.level).func
      if ((strategy != s.strategy || func != (← config level).func) && s.last_flush != -2) ||
          hook_flush != Z_NO_FLUSH then
        let flush := if (← RANK hook_flush) > (← RANK Z_BLOCK) then hook_flush else Z_BLOCK
        let err ← f strm flush
        if err == Z_STREAM_ERROR then return err
        let z ← ldStream strm
        let s ← ldDState st
        if z.avail_in != 0 then return Z_BUF_ERROR
        let d ← chkI32 (s.strstart.toInt32.toInt - s.block_start.toInt)
        if d.toUInt32 + s.lookahead != 0 then return Z_BUF_ERROR
      paramsTail st level strategy : M Int32) := by
  rfl

/-! ## The compression functions of the levels -/

/-- The compression function of level `l` (0..9) in `configuration_table`. -/
def funcOf (l : Int32) : CompressFn := (configuration_table[l.toNatClampNeg]!).func

theorem config_eq (l : Int32) (h0 : 0 ≤ l) (h9 : l ≤ 9) :
    config l = pure configuration_table[l.toNatClampNeg]! := by
  unfold config tblGet
  have : ¬ l < 0 := fun h => absurd h0 (Int32.not_le.mpr h)
  have hl : l.toNatClampNeg < configuration_table.size := by
    have := Int32.le_iff_toInt_le.mp h9
    have e : configuration_table.size = 10 := rfl
    rw [e]; show l.toInt.toNat < 10
    have : (9 : Int32).toInt = 9 := rfl
    omega
  rw [ite_f this, dif_t hl]
  simp [hl]

/-- A level as a number below 10. -/
theorem lvl_nat (l : Int32) (h0 : 0 ≤ l) (h9 : l ≤ 9) : ∃ k : Fin 10, l = Int32.ofInt (k.val : Int) := by
  have a := Int32.le_iff_toInt_le.mp h0
  have c := Int32.le_iff_toInt_le.mp h9
  have e0 : (0 : Int32).toInt = 0 := rfl
  have e9 : (9 : Int32).toInt = 9 := rfl
  refine ⟨⟨l.toInt.toNat, by omega⟩, ?_⟩
  show l = Int32.ofInt ((l.toInt.toNat : Nat) : Int)
  rw [show ((l.toInt.toNat : Nat) : Int) = l.toInt by omega, Int32.ofInt_toInt]

/-- Two levels with one compression function are both 0, both 1, or both in 3..6, or none. -/
theorem groups {a c : Int32} (a0 : 0 ≤ a) (a9 : a ≤ 9) (c0 : 0 ≤ c) (c9 : c ≤ 9) (e : funcOf a = funcOf c) :
    (a = 0 ↔ c = 0) ∧ (a = 1 ↔ c = 1) ∧ ((3 ≤ a ∧ a ≤ 6) ↔ (3 ≤ c ∧ c ≤ 6)) := by
  obtain ⟨ka, rfl⟩ := lvl_nat a a0 a9
  obtain ⟨kc, rfl⟩ := lvl_nat c c0 c9
  revert e
  revert ka kc
  decide

/-- Two levels with one compression function are both in 7..9 (`deflate_slow`) or both outside. -/
theorem groups_slow {a c : Int32} (a0 : 0 ≤ a) (a9 : a ≤ 9) (c0 : 0 ≤ c) (c9 : c ≤ 9) (e : funcOf a = funcOf c) :
    (7 ≤ a ∧ a ≤ 9) ↔ (7 ≤ c ∧ c ≤ 9) := by
  obtain ⟨ka, rfl⟩ := lvl_nat a a0 a9
  obtain ⟨kc, rfl⟩ := lvl_nat c c0 c9
  revert e
  revert ka kc
  decide

/-! ## The tail -/

/-- `stale_chain` of `deflateParams`, from the state before and the new level and strategy. -/
def staleOf (st : DeflateState) (level strategy : Int32) : Bool :=
  (HASHLESS level strategy != HASHLESS st.level st.strategy) ||
    ((level ≥ MIN_ROLL_LEVEL) != (st.level ≥ MIN_ROLL_LEVEL)) || (st.level == 1 && level != 1)

/-- The state that the tail leaves. -/
def tailS (st : DeflateState) (x1 x2 a1 a2 a4 : UInt32) (a3 : Int32) (lm : Ival LongestMatchFn)
    (ib : Ival InsertBatchFn) (level strategy : Int32) : DeflateState :=
  { st with
    ins_h := x1
    insert := x2
    max_lazy_match := a1
    good_match := a2
    nice_match := a3
    max_chain_length := a4
    longest_match := lm
    insert_batch := ib
    level := level
    strategy := strategy }

/-- What the tail leaves, from state `st` and bytes `d` (`head` at `ho`): the new level and strategy, `ins_h`,
`insert` (at most `strstart`), the parameters and function pointers of `lm_set_level` changed; `head` cleared on a
stale chain of a configuration that is not `HASHLESS`, else the bytes kept. -/
def TailPost (st : DeflateState) (d : Array UInt8) (ho : Nat) (level strategy : Int32) (st' : DeflateState)
    (d' : Array UInt8) : Prop :=
  ∃ (x1 x2 a1 a2 a4 : UInt32) (a3 : Int32) (lm : Ival LongestMatchFn) (ib : Ival InsertBatchFn),
    st' = tailS st x1 x2 a1 a2 a4 a3 lm ib level strategy ∧
    (lm = st.longest_match ∨ ∃ f, lm = .val f) ∧
    (ib = st.insert_batch ∧ level = st.level ∨ ib = .val (ZlibNgF.Proof.DeflateInv.insertBatchOf level)) ∧
    (((staleOf st level strategy && !HASHLESS level strategy) = true ∧
        d' = fillFold 0 ho (List.range' 0 (HASH_SIZE.toNat * 2)) d ∧ x2 ≤ st.strstart) ∨
      ((staleOf st level strategy && !HASHLESS level strategy) = false ∧ d' = d ∧ x2 = st.insert))

theorem tail_SH {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {ho : Nat}
    (level strategy : Int32) (hh : st.head = .val (.ref (.heap b) ho)) (hho : ho + 131072 ≤ d.size)
    (l0 : 0 ≤ level) (l9 : level ≤ 9) :
    Sat (SH H i z b st d) (paramsTail (some b) level strategy)
      (fun r H' => r = Z_OK ∧ ∃ st' d', H' = SH H i z b st' d' ∧ TailPost st d ho level strategy st' d') := by
  -- the level part and the strategy store, from a state `s1` with the level of `st`
  have rest : ∀ (s1 : DeflateState) (d1 : Array UInt8), s1.level = st.level →
      Sat (SH H i z b s1 d1) (do
        if (← rdD (some b) (·.level)) != level then
          lm_set_level (some b) level
        wrD (some b) fun s => { s with strategy := strategy }
        return Z_OK)
        (fun r H' => r = Z_OK ∧ ∃ (a1 a2 a4 : UInt32) (a3 : Int32) (lm : Ival LongestMatchFn)
          (ib : Ival InsertBatchFn),
            H' = SH H i z b (tailS s1 s1.ins_h s1.insert a1 a2 a4 a3 lm ib level strategy) d1 ∧
          (lm = s1.longest_match ∨ ∃ f, lm = .val f) ∧
            (ib = s1.insert_batch ∧ level = s1.level ∨ ib = .val (ZlibNgF.Proof.DeflateInv.insertBatchOf level))) := by
    intro s1 d1 hl1
    refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
    by_cases hc : (s1.level != level) = true
    · rw [ite_t hc]
      obtain ⟨c, lm, ib, hib, e⟩ := lm_set_level_SH (H := H) (i := i) (z := z) (b := b) (st := s1) (d := d1) level l0 l9
      refine Sat.bind (Sat.of_eq e ?_)
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      exact Sat.pure ⟨rfl, _, _, _, _, _, _, rfl, Or.inr ⟨_, rfl⟩, Or.inr (by rw [hib])⟩
    · rw [ite_f hc]
      have e : s1.level = level := by simpa using hc
      refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
      refine Sat.pure ⟨rfl, s1.max_lazy_match, s1.good_match, s1.max_chain_length, s1.nice_match,
        s1.longest_match, s1.insert_batch, ?_, Or.inl rfl, Or.inl ⟨rfl, e.symm⟩⟩
      rw [← e]; rfl
  unfold paramsTail
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  by_cases hc : (staleOf st level strategy && !HASHLESS level strategy) = true
  · have hc' := hc
    simp only [staleOf] at hc'
    rw [ite_t hc']
    refine Sat.bind (Sat.of_eq (clear_hash_SH hh hho) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.bind (Sat.of_eq (wrD_SH _) ?_)
    refine Sat.mono (rest _ _ rfl) ?_
    rintro r H' ⟨rfl, a1, a2, a4, a3, lm, ib, rfl, hlm, hib⟩
    refine ⟨rfl, _, _, rfl, _, _, a1, a2, a4, a3, lm, ib, rfl, hlm, hib, Or.inl ⟨hc, rfl, ?_⟩⟩
    show (if st.strstart > st.w_size then st.w_size else st.strstart) ≤ st.strstart
    split
    · exact UInt32.le_of_lt (by assumption)
    · exact UInt32.le_refl _
  · have hc' : ¬ ((HASHLESS level strategy != HASHLESS st.level st.strategy ||
        (decide (level ≥ MIN_ROLL_LEVEL) != decide (st.level ≥ MIN_ROLL_LEVEL)) ||
        (st.level == 1 && level != 1)) && !HASHLESS level strategy) = true := hc
    rw [ite_f hc']
    refine Sat.mono (rest _ _ rfl) ?_
    rintro r H' ⟨rfl, a1, a2, a4, a3, lm, ib, rfl, hlm, hib⟩
    exact ⟨rfl, _, _, rfl, st.ins_h, st.insert, a1, a2, a4, a3, lm, ib, rfl, hlm, hib,
      Or.inr ⟨by simpa using hc, rfl, rfl⟩⟩

/-- The bytes that the tail leaves differ from `d` in `head` only. -/
theorem tail_bytes {st st' : DeflateState} {d d' : Array UInt8} {ho : Nat} {level strategy : Int32}
    (T : TailPost st d ho level strategy st' d') :
    d'.size = d.size ∧ ∀ j, (j < ho ∨ ho + 131072 ≤ j) → d'[j]! = d[j]! := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb⟩ := T
  rcases hb with ⟨_, e, _⟩ | ⟨_, e, _⟩
  · generalize hn : HASH_SIZE.toNat * 2 = n at e
    have : n = 131072 := by rw [← hn]; rfl
    subst this
    refine ⟨by rw [e]; exact fillFold_size .., fun j hj => by
      rw [e]; exact fillFold_get _ _ _ _ _ fun x hx => by simp only [List.mem_range'_1] at hx; omega⟩
  · exact ⟨by rw [e], fun _ _ => by rw [e]⟩

/-- The invariant after the tail (a level 0..9, a strategy 0..4). -/
theorem tail_dcore {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8}
    {ho : Nat} {al : DeflateAllocs} {level strategy : Int32} (c : DCore H (some i) z b (dview st) al)
    (hd : H.bytes b = some d) (hh : st.head = .val (.ref (.heap b) ho)) (l0 : 0 ≤ level) (l9 : level ≤ 9)
    (s0 : 0 ≤ strategy) (s4 : strategy ≤ 4) (T : TailPost st d ho level strategy st' d') :
    DCore (SH H i z b st' d') (some i) z b (dview st') al := by
  obtain ⟨ho1, d1, hd1, hh1, hho⟩ := c.head
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  have hh2 : ho1 = ho := by
    simp only [dview] at hh1; rw [hh] at hh1; injection hh1 with e; injection e with _ e; exact e.symm
  subst hh2
  obtain ⟨sz, keep⟩ := tail_bytes T
  obtain ⟨x1, x2, a1, a2, a4, a3, lm, ib, rfl, hlm, hib, hbs⟩ := T
  have hx2 : x2 ≤ st.strstart := by
    rcases hbs with ⟨-, -, e⟩ | ⟨-, -, e⟩
    · exact e
    · rw [e]; exact c.ins
  obtain ⟨d0, wo, po, ho', pbo, hd0, hw, hp, hh', hpb, l1, l2, l3, l4, hsb, poo, hpo, hpoo, hpe⟩ := c.lay
  obtain rfl := Option.some.inj (hd.symm.trans hd0)
  obtain ⟨d2, sbo, hd2, hsb2, hsym⟩ := c.symv
  obtain rfl := Option.some.inj (hd.symm.trans hd2)
  simp only [dview] at hh' hsb hsb2 hpb l3 l4
  rw [hh] at hh'
  obtain rfl : ho1 = ho' := by injection hh' with e; injection e
  rw [hsb] at hsb2
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  exact { c with
    head := ⟨ho1, d', SH_bytes _ _ _ _ _ _, hh, by omega⟩
    level := ⟨l0, l9⟩
    strategy := ⟨s0, s4⟩
    fns := ⟨by
        rcases hlm with e | ⟨f, e⟩
        · rw [e]; exact c.fns.1
        · exact ⟨f, e⟩, by
        show ib = .val (ZlibNgF.Proof.DeflateInv.insertBatchOf level)
        rcases hib with ⟨e, el⟩ | e
        · rw [e, el]; exact c.fns.2
        · exact e⟩
    ins := hx2
    lay := ⟨d', wo, po, ho1, pbo, SH_bytes _ _ _ _ _ _, hw, hp, hh, hpb, l1, l2, l3, by rw [sz]; exact l4, hsb, poo,
      hpo, hpoo, hpe⟩
    symv := ⟨d', _, SH_bytes _ _ _ _ _ _, hsb, SymOk.of_eq hsym fun k hk => keep _ (Or.inr (by omega))⟩ }

/-- The switch that the tail may make: the strategy and the compression function stay, or there is no lookahead and
no unfinished block. -/
def SwitchOk (st : DeflateState) (level strategy : Int32) : Prop :=
  (st.strategy = strategy ∧ funcOf st.level = funcOf level) ∨
    (st.lookahead = 0 ∧ (st.strstart.toNat : Int) = st.block_start.toInt)

theorem tail_syms {st : DeflateState} {level strategy : Int32} (S : SymsOk st) (o0 : 0 ≤ st.level)
    (o9 : st.level ≤ 9) (l0 : 0 ≤ level) (l9 : level ≤ 9) (sw : SwitchOk st level strategy)
    (x1 x2 a1 a2 a4 : UInt32) (a3 : Int32) (lm : Ival LongestMatchFn) (ib : Ival InsertBatchFn) :
    SymsOk (tailS st x1 x2 a1 a2 a4 a3 lm ib level strategy) := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := S
  simp only [SymsOk, tailS]
  rcases sw with ⟨es, ef⟩ | ⟨el, eb⟩
  · obtain ⟨g0, g1, -⟩ := groups o0 o9 l0 l9 ef
    refine ⟨q1, fun e => q2 (g0.2 e), fun e1 e2 => q3 (g1.2 e1) (by rw [es]; exact e2), q4, fun e => ?_⟩
    obtain ⟨r1, r2, r3⟩ := q5 e
    exact ⟨g1.1 r1, by rw [← es]; exact r2, r3⟩
  · have hs0 := q4 eb
    refine ⟨q1, fun _ => ⟨by rw [Int32.le_iff_toInt_le, show (0 : Int32).toInt = 0 from rfl, ← eb]; omega, hs0, el⟩, fun _ _ => hs0, q4, fun e => ?_⟩
    exact absurd el (q5 e).2.2

/-- With no lookahead and `block_start` at `strstart`, `LazyOk` leaves no pending match and no pending literal. -/
theorem LazyOk.clear0 {st : DeflateState} (L : LazyOk st) (el : st.lookahead = 0)
    (eb : (st.strstart.toNat : Int) = st.block_start.toInt) : st.prev_length < 3 ∧ st.match_available = 0 := by
  refine ⟨UInt32.lt_iff_toNat_lt.mpr (Nat.lt_of_not_le fun h3 => ?_), Classical.byContradiction fun hm => ?_⟩
  · have := (L.1 (UInt32.le_iff_toNat_le.mpr (by simpa using h3))).2.1
    have e3 : (3 : UInt32).toNat = 3 := rfl
    rw [el] at this; simp at this; omega
  · have := (L.2.1 hm).2; omega

/-- The tail keeps `LazyOk`: a change into or out of the levels of `deflate_slow` happens only with the same strategy
and compression function (so no change of `TableAt 7 9`), or with no lookahead and `block_start` at `strstart`. -/
theorem tail_lazy {st : DeflateState} {level strategy : Int32} (L : LazyOk st) (o0 : 0 ≤ st.level)
    (o9 : st.level ≤ 9) (l0 : 0 ≤ level) (l9 : level ≤ 9) (sw : SwitchOk st level strategy)
    (x1 x2 a1 a2 a4 : UInt32) (a3 : Int32) (lm : Ival LongestMatchFn) (ib : Ival InsertBatchFn) :
    LazyOk (tailS st x1 x2 a1 a2 a4 a3 lm ib level strategy) := by
  refine ⟨L.1, L.2.1, fun ht => ?_, L.2.2.2⟩
  rcases sw with ⟨es, ef⟩ | ⟨el, eb⟩
  · refine L.clear fun h7 => ht ?_
    obtain ⟨b1, b2, b3, b4⟩ := h7
    obtain ⟨g1, g2⟩ := (groups_slow o0 o9 l0 l9 ef).mp ⟨b1, b2⟩
    exact ⟨g1, g2, by simp only [tailS]; rw [← es]; exact b3, by simp only [tailS]; rw [← es]; exact b4⟩
  · exact L.clear0 el eb

/-- `DSide`'s facts after the tail. -/
theorem tail_side {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st st' : DeflateState} {d d' : Array UInt8}
    {ho : Nat} {al : DeflateAllocs} {level strategy : Int32} (c : DCore H (some i) z b (dview st) al)
    (hd : H.bytes b = some d) (hh : st.head = .val (.ref (.heap b) ho)) (S : SideAt H b st) (l0 : 0 ≤ level)
    (l9 : level ≤ 9) (sw : SwitchOk st level strategy) (T : TailPost st d ho level strategy st' d') :
    SideAt (SH H i z b st' d') b st' := by
  have o := c.level
  simp only [dview] at o
  obtain ⟨S1, S2, S3, S4, S5, S6, S7⟩ := S
  obtain ⟨-, wo, po, -, -, -, -, hp, -⟩ := c.lay
  simp only [dview] at hp
  obtain ⟨hho0, -⟩ : ho + 131072 ≤ d.size ∧ True := by
    obtain ⟨ho1, d1, hd1, hh1, hho⟩ := c.head
    obtain rfl := Option.some.inj (hd.symm.trans hd1)
    simp only [dview] at hh1; rw [hh] at hh1
    obtain rfl : ho = ho1 := by injection hh1 with e; injection e
    exact ⟨hho, trivial⟩
  obtain ⟨x1, x2, a1, a2, a4, a3, lm, ib, rfl, -, -, hbs⟩ := T
  refine ⟨tail_syms S1 o.1 o.2 l0 l9 sw x1 x2 a1 a2 a4 a3 lm ib, S2, S3, ?_, S5, ?_,
    tail_lazy S7 o.1 o.2 l0 l9 sw x1 x2 a1 a2 a4 a3 lm ib⟩
  · have m : DeflateSide.HdrMove H (SH H i z b (tailS st x1 x2 a1 a2 a4 a3 lm ib level strategy) d') b b st :=
      DeflateSide.hdrMove_out rfl fun r hr => DeflateSetDict.space_SH_ne hr
    exact (S4.move m).of_state rfl rfl rfl rfl
  · intro d2 hd2
    rw [SH_bytes] at hd2; obtain rfl := Option.some.inj hd2
    rcases hbs with ⟨hc, e, -⟩ | ⟨hc, e, -⟩
    · refine DeflateSide.chainOk_clear (ho := ho) (po := po) hh hp fun _ j h1 h2 => ?_
      rw [e]
      exact ZlibNgF.Proof.DeflateAlloc.fillFold_in 0 ho _ d j ⟨j - ho, by
        simp only [List.mem_range'_1]; exact ⟨Nat.zero_le _, by show j - ho < 0 + 65536 * 2; omega⟩, by omega⟩
        (by omega)
    · subst e
      intro n1 n2
      simp only [tailS] at n1 n2
      have hl : HASHLESS level strategy = false := n2
      simp only [hl, Bool.not_false, Bool.and_true] at hc
      simp only [staleOf, Bool.or_eq_false_iff, bne_eq_false_iff_eq, Bool.and_eq_false_iff] at hc
      obtain ⟨⟨eh, -⟩, el1⟩ := hc
      have o1 : st.level ≠ 1 := fun e => by
        rcases el1 with x | x
        · exact (by simpa using x : st.level ≠ 1) e
        · exact n1 (by simpa using x)
      obtain ⟨I, ho', po', hh', hp', c1, c2, c3⟩ := S6 _ hd o1 (by rw [← eh]; exact hl)
      refine ⟨I, ho', po', hh', hp', fun p hp => ⟨(c1 p hp).1, ?_⟩, c2, c3⟩
      have := (c1 p hp).2
      rcases sw with ⟨-, ef⟩ | ⟨el, -⟩
      · obtain ⟨-, -, g⟩ := groups o.1 o.2 l0 l9 ef
        unfold chainLim at this
        show p < st.strstart.toNat + (if 3 ≤ level ∧ level ≤ 6 then st.lookahead.toNat else 0)
        split at this <;> split
        · exact this
        · rename_i a1 a2; exact absurd (g.1 a1) a2
        · rename_i a1 a2; exact absurd (g.2 a2) a1
        · exact this
      · unfold chainLim at this
        show p < st.strstart.toNat + (if 3 ≤ level ∧ level ≤ 6 then st.lookahead.toNat else 0)
        have e0 : st.lookahead.toNat = 0 := by rw [el]; rfl
        rw [e0] at this ⊢
        have : p < st.strstart.toNat := by split at this <;> omega
        split <;> omega

/-- The tail on an invariant stream with `DSide` that may switch: `Z_OK`, a change of the stream's block only, the
invariant and `DSide`. -/
theorem tail_ok {h : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {level strategy : Int32}
    (hv : DInv h (some i)) (hs : DSide h (some i)) (hz : h.streams i = some z) (hb : z.state = some b)
    (hst : h.dstate b = some st) (l0 : 0 ≤ level) (l9 : level ≤ 9) (s0 : 0 ≤ strategy) (s4 : strategy ≤ 4)
    (sw : SwitchOk st level strategy) :
    ∃ h', paramsTail (some b) level strategy h = .ok (Z_OK, h') ∧ DFrame h h' [i] [b] [] [] ∧ DInv h' (some i) ∧
      DSide h' (some i) := by
  have S := hs b st ⟨i, z, rfl, hz, hb, hst⟩
  obtain ⟨i0, z0, b0, st0, al, e0, hz0, hb0, hst0, hal, c⟩ := hv
  obtain rfl : i = i0 := Option.some.inj e0
  obtain rfl : z = z0 := Option.some.inj (hz.symm.trans hz0)
  obtain rfl : b = b0 := Option.some.inj (hb.symm.trans hb0)
  obtain rfl : st = st0 := Option.some.inj (hst.symm.trans hst0)
  obtain ⟨d, hd, e⟩ := DeflateSetDict.sh_of hz hst
  have hda : h.dallocs b = some al := by simpa [Heap.dallocsOf, hd] using hal
  obtain ⟨ho, d1, hd1, hh, hho⟩ := c.head
  obtain rfl := Option.some.inj (hd.symm.trans hd1)
  simp only [dview] at hh
  obtain ⟨r, H', run, rfl, st', d', rfl, T⟩ := tail_SH (H := h) (i := i) (z := z) (b := b) (st := st) (d := d)
    level strategy hh hho l0 l9
  rw [e] at run
  refine ⟨_, run, by rw [← e]; exact dframe_SH _ _ _ _ _ _, ⟨i, z, b, st', al, rfl, SH_streams _ _ _ _ _ _, hb,
    SH_dstate _ _ _ _ _ _, by simp [Heap.dallocsOf, SH, hda], tail_dcore c hd hh l0 l9 s0 s4 T⟩, ?_⟩
  intro b2 st2 ⟨i2, z2, e2, hz2, hzb2, hst2⟩
  obtain rfl := Option.some.inj e2
  rw [SH_streams] at hz2
  obtain rfl := Option.some.inj hz2
  obtain rfl := Option.some.inj (hb.symm.trans hzb2)
  rw [SH_dstate] at hst2
  obtain rfl := Option.some.inj hst2
  exact tail_side c hd hh S l0 l9 sw T

theorem ofInt_toUInt32 (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) : (Int32.ofInt v).toUInt32.toNat = v.toNat := by
  have : (Int32.ofInt v).toInt = v := by
    rw [Int32.toInt_ofInt]; rw [Int.bmod_eq_of_le] <;> simp [Int32.size] <;> omega
  rw [Int32.toNat_toUInt32_of_le (by rw [Int32.le_iff_toInt_le, this]; simp; omega)]
  show (Int32.ofInt v).toInt.toNat = _
  rw [this]

theorem sum_zero (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) (la : UInt32) (hl : la.toNat ≤ 65536)
    (e : (Int32.ofInt v).toUInt32 + la = 0) : v = 0 ∧ la = 0 := by
  have := congrArg UInt32.toNat e
  rw [UInt32.toNat_add, ofInt_toUInt32 v h0 h1] at this
  simp only [UInt32.toNat_zero] at this
  have : v.toNat + la.toNat = 0 := by omega
  exact ⟨by omega, UInt32.toNat_inj.mp (by simp; omega)⟩

theorem rank0 (h : Heap) : RANK Z_NO_FLUSH h = .ok (0, h) := rfl
theorem rank5 (h : Heap) : RANK Z_BLOCK h = .ok (1, h) := rfl

/-- **`deflateParams`**, given `DeflateOk`: no fault, a write of the output buffer, the stream record and the stream's
block only, the invariant and `DSide`. -/
theorem params_ok (D : DeflateOk) {h : Heap} {s : StreamPtr} {level strategy : Int32} (hv : DInv h s)
    (hs : DSide h s) (hcg : CrcGlobals h) (hio : DStreamIO h s) :
    Sat h (deflateParams s level strategy) (fun _ h' =>
      DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s) ∧ DInv h' s ∧ DSide h' s) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  have hsi : stateIds h (some i) = [b] := by simp [stateIds, L.hz, L.hb]
  have hsi' : streamIds (some i) = [i] := rfl
  unfold deflateParams
  rw [params_eq]
  refine Sat.bind (Sat.of_eq L.check ?_)
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  generalize (if (level == Z_DEFAULT_COMPRESSION) = true then 6 else level) = lv
  have fr0 : ∀ h', DFrame h h' [i] [b] [] [] →
      DFrame h h' (streamIds (some i)) (stateIds h (some i)) [] (dOutputRanges h (some i)) := fun h' f => by
    rw [hsi, hsi']; exact dframe_nil _ f
  have S := hs b st ⟨i, z, rfl, L.hz, L.hb, L.dstate⟩
  by_cases hr : (decide (lv < 0) || decide (lv > 9) || decide (strategy < 0) || decide (strategy > Z_FIXED)) = true
  · rw [ite_t hr]
    exact Sat.pure ⟨fr0 _ (DeflateInitPublic.dframe_refl _ _ _ _ _), hv, hs⟩
  rw [ite_f hr]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hr
  obtain ⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩ := hr
  have l0 : 0 ≤ lv := Int32.not_lt.mp hr1
  have l9 : lv ≤ 9 := Int32.not_lt.mp hr2
  have s0 : 0 ≤ strategy := Int32.not_lt.mp hr3
  have s4 : strategy ≤ 4 := Int32.not_lt.mp hr4
  have o := c.level
  simp only [dview] at o
  refine Sat.bind (Sat.of_eq (ldDState_app L.dstate) ?_)
  rw [config_eq _ o.1 o.2]
  refine Sat.bind (Sat.pure ?_)
  rw [config_eq _ l0 l9]
  refine Sat.bind (Sat.pure ?_)
  dsimp only
  by_cases hc : ((strategy != st.strategy ||
      configuration_table[st.level.toNatClampNeg]!.func != configuration_table[lv.toNatClampNeg]!.func) &&
      st.last_flush != -2 ||
      Z_NO_FLUSH != Z_NO_FLUSH) = true
  · rw [ite_t hc]
    refine Sat.bind (Sat.of_eq (rank0 _) ?_)
    refine Sat.bind (Sat.of_eq (rank5 _) ?_)
    rw [ite_f (by decide : ¬ ((0 : Int32) > 1))]
    obtain ⟨r1, h1, e1, f1, si1, hv1, hs1⟩ := D h (some i) Z_BLOCK hv hs hcg hio
    refine Sat.bind (Sat.of_eq e1 ?_)
    by_cases he : (r1 == Z_STREAM_ERROR) = true
    · rw [ite_t he]; exact Sat.pure ⟨f1, hv1, hs1⟩
    rw [ite_f he]
    obtain ⟨i1, z1, b1, st1, al1, e', L1, hal1, c1⟩ := live hv1
    obtain rfl : i = i1 := Option.some.inj e'
    obtain rfl : b = b1 := by
      have : stateIds h1 (some i) = [b1] := by simp [stateIds, L1.hz, L1.hb]
      rw [si1, hsi] at this; exact List.cons.inj this |>.1
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.InflateInv.ldStream_app L1.hz) ?_)
    refine Sat.bind (Sat.of_eq (ldDState_app L1.dstate) ?_)
    by_cases ha : (z1.avail_in != 0) = true
    · rw [ite_t ha]; exact Sat.pure ⟨f1, hv1, hs1⟩
    rw [ite_f ha]
    have ss := DeflateFacts.strstart_toInt32 c1
    have hb1 := c1.bstart
    have hb2 := c1.bs_lo
    have hl1 := c1.look
    obtain ⟨-, w2, wsz, -⟩ := c1.sizes
    simp only [dview] at ss hb1 hb2 hl1 w2 wsz
    have hws : st1.window_size.toNat ≤ 65536 := by
      rw [wsz, DeflateInit.wbuf_toNat _ w2]; unfold DeflateAlloc.dWS; split <;> omega
    rw [ss.1, DeflatePrime.chk_ok _ (by omega) (by omega)]
    refine Sat.bind (Sat.pure ?_)
    by_cases hz : ((Int32.ofInt ((st1.strstart.toNat : Int) - st1.block_start.toInt)).toUInt32 + st1.lookahead
        != 0) = true
    · rw [ite_t hz]; exact Sat.pure ⟨f1, hv1, hs1⟩
    rw [ite_f hz]
    have hz' : (Int32.ofInt ((st1.strstart.toNat : Int) - st1.block_start.toInt)).toUInt32 + st1.lookahead = 0 := by
      simpa using hz
    obtain ⟨q1, q2⟩ := sum_zero _ (by omega) (by omega) _ (by omega) hz'
    obtain ⟨h', e2, f2, hv2, hs2⟩ := tail_ok hv1 hs1 L1.hz L1.hb L1.dstate l0 l9 s0 s4 (Or.inr ⟨q2, by omega⟩)
    refine Sat.of_eq e2 ⟨?_, hv2, hs2⟩
    have f1' := f1
    rw [hsi, hsi'] at f1'
    have := DFrame.trans f1' (dframe_nil _ f2)
    rw [hsi, hsi']; exact this
  · rw [ite_f hc]
    have sw : SwitchOk st lv strategy := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, not_or, not_and, Classical.not_not] at hc
      obtain ⟨hc1, -⟩ := hc
      by_cases hl : st.last_flush = -2
      · obtain ⟨-, -, hf⟩ := S.2.2.2.2.1
        obtain ⟨e1, e2⟩ := hf hl
        exact Or.inr ⟨e2, e1⟩
      · have := fun x => hl (hc1 x)
        refine Or.inl ⟨?_, ?_⟩
        · exact Classical.byContradiction fun hn => this (Or.inl (Ne.symm hn))
        · exact Classical.byContradiction fun hn => this (Or.inr hn)
    obtain ⟨h', e2, f2, hv2, hs2⟩ := tail_ok hv hs L.hz L.hb L.dstate l0 l9 s0 s4 sw
    exact Sat.of_eq e2 ⟨fr0 _ f2, hv2, hs2⟩

end ZlibNgF.Proof.DeflateParams
