import ZlibNgF.Proof.«deflate_quick.c.emit»
import ZlibNgF.Proof.«compare256_c.c.safety»
import ZlibNgF.Proof.«insert_string_p.h.safety»

/-!
# `deflate_quick` with tallied symbols: the match search (`ZlibNgF`)

The reads of the match part of a trip of `deflate_quick_impl` (`deflate_quick.c:168-220`) on the loop invariant:
`insert_knuth_val_head` writes `head` only (the loop invariant stays, `sli_hw`); `dist = strstart - hash_head` is
used only when `0 < dist <= MAX_DIST` (`dist_ok`), so the candidate lies before `strstart`; `compare256` reads at most
256 bytes from `strstart + 2` and from the candidate `+ 2`, and `max_match_continues` 8 bytes and then 256 bytes from
`strstart + 2` and `strstart - dist + 2` (`mmc_ok`): all inside the stream's block, as the window is followed by
`prev`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.QuickP
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateQuick
open ZlibNgF.Proof.DeflateBits (WrIn)

/-! ## Numbers -/

theorem u32_i64 (a : UInt32) : (a.toUInt64.toInt64).toInt = a.toNat := by
  have := a.toNat_lt
  simp only [UInt64.toInt64, Int64.toInt]
  rw [BitVec.toInt_eq_toNat_of_lt (by show 2 * a.toUInt64.toNat < 2^64; simp; omega)]; rfl

/-- `int64_t dist = (int64_t)strstart - hash_head;` with `dist <= MAX_DIST(s) && dist > 0`: the candidate lies
before `strstart`, at most `MAX_DIST` before, and `(uint32_t)dist` is the difference. -/
theorem dist_ok (a b m : UInt32) (h : (decide (a.toUInt64.toInt64 - b.toUInt64.toInt64 ≤ m.toUInt64.toInt64) &&
    decide (a.toUInt64.toInt64 - b.toUInt64.toInt64 > 0)) = true) :
    b.toNat < a.toNat ∧ a.toNat - b.toNat ≤ m.toNat ∧
      (a.toUInt64.toInt64 - b.toUInt64.toInt64).toUInt64.toUInt32.toNat = a.toNat - b.toNat := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, Int64.toInt_sub,
    u32_i64] at h
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hm := m.toNat_lt
  obtain ⟨h1, h2⟩ := h
  rw [Int.bmod_eq_of_le (by omega) (by omega)] at h1 h2
  simp at h2
  refine ⟨by omega, by omega, ?_⟩
  have e : (a.toUInt64.toInt64 - b.toUInt64.toInt64).toInt = a.toNat - b.toNat := by
    rw [Int64.toInt_sub, u32_i64, u32_i64, Int.bmod_eq_of_le (by omega) (by omega)]
  rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le (by rw [Int64.le_iff_toInt_le, e]; simp; omega)]
  rw [Int64.toNatClampNeg, e]; omega

/-! ## The loop invariant under `head` stores -/

/-- The loop invariant after a change of the block's bytes below the end of `head`. -/
theorem sli_hw {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d))
    (hw : ∀ ho, st.head = .val (.ref (.heap b) ho) → WrIn d 0 (ho + 131072) d') :
    SLI h i b la ss (SH H0 i z b st d') := by
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨z2, hz2, hb⟩ := C.1.blk
  obtain rfl : z1 = z2 := Option.some.inj ((SH_streams _ _ _ _ _ _).symm.trans hz2)
  have e3 := congrArg (fun H => H.streams i) e
  simp only [SH_streams] at e3
  obtain rfl := Option.some.inj e3
  refine ⟨H1, z, st, d', ?_, ?_⟩
  · rw [← SH_SH H0 i z z b st st d d', e, SH_SH]
  obtain ⟨F, hC⟩ := C
  refine ⟨slf_SH F (fun al _ c => ?_) rfl rfl rfl rfl (F.st _ (SH_dstate _ _ _ _ _ _)).2.2 (StratKeeps.refl _)
    (fun _ => Nat.le_refl _), fun st2 h2 => ?_⟩
  · exact ZlibNgF.Proof.FillFacts.dcore_fw (H := H1) c (SH_bytes _ _ _ _ _ _) rfl rfl
      ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ (ZlibNgF.Proof.FillFacts.wcore_of c) c.look hw
  · obtain rfl := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans h2)
    exact hC _ (SH_dstate _ _ _ _ _ _)

/-- The window, the hash-table layout and `w_size` of a state under the loop invariant. -/
theorem sli_facts {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {la ss : UInt32}
    (I : SLI h i b la ss (SH H0 i z b st d))
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) :
    st.window = .val (.ref (.heap b) wo) ∧ wo + ss.toNat + la.toNat ≤ d.size ∧ wo + ss.toNat + 259 ≤ d.size ∧
      (∃ po ho, ZlibNgF.Proof.InsertSafe.HLay b d.size st wo po ho) ∧ 512 ≤ st.w_size.toNat ∧
      st.w_size.toNat ≤ 32768 ∧ ss.toNat + la.toNat ≤ 65536 := by
  obtain ⟨hwin, h1, h2⟩ := ZlibNgF.Proof.DeflateRleP.sli_win2 I hw0
  obtain ⟨H1, z1, st1, d1, e, C⟩ := I
  have e1 := congrArg (fun H => H.dstate b) e
  have e2 := congrArg (fun H => H.bytes b) e
  simp only [SH_dstate, SH_bytes] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain rfl := Option.some.inj e2
  obtain ⟨z2, st2, al, hz2, hb2, hst2, -, c⟩ := C.1.live
  obtain rfl : FS st la ss = st2 := Option.some.inj ((SH_dstate _ _ _ _ _ _).symm.trans hst2)
  obtain ⟨wo', po, ho, pbo, L, -⟩ := ZlibNgF.Proof.FillFacts.hlay_of c (SH_bytes _ _ _ _ _ _)
  have hw' : st.window = .val (.ref (.heap b) wo') := L.win
  rw [hwin] at hw'
  obtain rfl : wo = wo' := by cases hw'; rfl
  obtain ⟨w1, w2, hws, -⟩ := c.sizes
  have hlook : ss.toNat + la.toNat ≤ st.window_size.toNat := c.look
  have hws' : st.window_size = W_BUF_SIZE st.w_size := hws
  have w2' : st.w_size.toNat ≤ 32768 := w2
  have h65 : st.window_size.toNat ≤ 65536 := by
    rw [hws', DeflateInit.wbuf_toNat _ w2']; unfold DeflateAlloc.dWS; split <;> omega
  exact ⟨hwin, h1, h2, ⟨po, ho, ⟨L.win, L.prev, L.head, L.w1, L.pw, L.hd, L.ph⟩⟩, w1, w2, by omega⟩

/-! ## `max_match_continues` -/

/-- `max_match_continues(window, strstart, dist)` with 259 bytes from `strstart` in block `b` and `dist <= strstart`:
no fault, the heap kept, at most 258. -/
theorem mmc_ok {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8} {wo : Nat}
    (ss dist : UInt32) (hk : wo + ss.toNat + 259 ≤ d.size) (hd : dist.toNat ≤ ss.toNat) :
    Sat (SH H i z b st d) (max_match_continues (.ref (.heap b) wo) ss dist) (fun r H' =>
      H' = SH H i z b st d ∧ r.toNat ≤ 258) := by
  unfold max_match_continues
  refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss.toNat (by omega)) ?_)
  obtain ⟨a, ea⟩ := ZlibNgF.Proof.WinBase.memread8_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := wo + ss.toNat) (by omega)
  refine Sat.bind (Sat.of_eq ea ?_)
  have eq : ((↑(wo + ss.toNat) : Int) + -(dist.toNat : Int)).toNat = wo + ss.toNat - dist.toNat := by omega
  have ez := ZlibNgF.Proof.DeflateRleP.addZ_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := wo + ss.toNat) (-(dist.toNat : Int)) (by omega) (by omega) (by omega)
  rw [eq] at ez
  refine Sat.bind (Sat.of_eq ez ?_)
  obtain ⟨c, ec⟩ := ZlibNgF.Proof.WinBase.memread8_SH (H := H) (i := i) (z := z) (b := b) (st := st) (d := d)
    (off := wo + ss.toNat - dist.toNat) (by omega)
  refine Sat.bind (Sat.of_eq ec ?_)
  by_cases hne : (a != c) = true
  · simp only [hne, ↓reduceIte]
    exact Sat.pure ⟨rfl, by decide⟩
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
    refine Sat.bind (Sat.of_eq ez ?_)
    refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.Compare256.compare256_ok (SH_bytes H i z b st d) (by omega)
      (by omega)) ?_)
    rintro r _ ⟨rfl, hr⟩
    refine Sat.pure ⟨rfl, ?_⟩
    rw [UInt32.toNat_add]; simp; omega

/-! ## The continuation loop -/

/-- The invariant of the continuation loop `for (;;)` (`deflate_quick.c:195-213`) over `(strstart, lookahead, exit)`,
for a match at distance `dist` and a bound `K` on `avail_in + lookahead`. -/
def CI (h : Heap) (i b : Nat) (flush : Int32) (dist : UInt32) (K : Nat) (v : UInt32 × UInt32 × QuickExit)
    (H : Heap) : Prop :=
  match v.2.2 with
  | .cont => SLI h i b v.2.1 v.1 H ∧ 262 ≤ v.2.1.toNat ∧ dist.toNat ≤ v.1.toNat ∧ avIn H i + v.2.1.toNat ≤ K
  | .brk => SLI h i b v.2.1 v.1 H ∧ avIn H i + v.2.1.toNat ≤ K
  | .ret r => StratPost h (some i) flush r H

/-- The measure of the continuation loop. -/
def CM (v : UInt32 × UInt32 × QuickExit) : Nat :=
  match v.2.2 with
  | .cont => v.2.1.toNat + 1
  | _ => 0

/-- One trip of the continuation loop (`quick_cont_trip` with `static_emit == 0`). -/
theorem ctrip_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss dist : UInt32} {K : Nat}
    (hn : NotSlow h b)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H)
    (hla : 262 ≤ la.toNat) (hd : dist.toNat ≤ ss.toNat) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hK : avIn H i + la.toNat ≤ K) :
    Sat H (quick_cont_trip (some b) (.ref (.heap b) wo) 0 dist ss la) (fun v H2 =>
      CI h i b flush dist K v H2 ∧ CM v < la.toNat + 1) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  have I : SLI h i b la ss (SH H0 i z b st d) := ⟨H0, z, st, d, rfl, C⟩
  obtain ⟨-, -, hk, -, -, -, h65⟩ := sli_facts I hw0
  unfold quick_cont_trip
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.mono (mmc_ok ss dist hk hd) ?_)
  rintro ml _ ⟨rfl, hml⟩
  by_cases h8 : ml < 8
  · simp only [h8, ↓reduceIte]
    exact Sat.pure ⟨⟨I, hK⟩, by simp [CM]⟩
  · simp only [h8, ↓reduceIte]
    have h8' : 8 ≤ ml.toNat := by
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp h8); simpa using this
    refine Sat.bind (Sat.mono (qdist_ok T (flush := flush) hn hw0 I ml dist (by omega) hml (by omega) hd1 hd2) ?_)
    rintro ⟨r, ss2, la2⟩ H2 ⟨⟨q1, q2⟩, e1, e2, e3⟩
    simp only [] at e1 e2 e3 q1 q2
    subst e1 e2
    have hla2 : (la - ml).toNat = la.toNat - ml.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
    have hss2 : (ss + ml).toNat = ss.toNat + ml.toNat := by rw [UInt32.toNat_add]; omega
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact Sat.pure ⟨q2 rfl, by simp [CM]⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hl : la - ml < MIN_LOOKAHEAD
      · simp only [hl, ↓reduceIte]
        refine Sat.pure ⟨⟨q1 rfl, ?_⟩, by simp [CM]⟩
        show avIn H2 i + (la - ml).toNat ≤ K
        rw [e3, avIn_SH, hla2]; rw [avIn_SH] at hK; omega
      · simp only [hl, ↓reduceIte]
        have hl' : 262 ≤ (la - ml).toNat := by
          have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hl)
          simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using this
        refine Sat.pure ⟨⟨q1 rfl, hl', show dist.toNat ≤ (ss + ml).toNat by omega, ?_⟩,
          show (la - ml).toNat + 1 < la.toNat + 1 by omega⟩
        show avIn H2 i + (la - ml).toNat ≤ K
        rw [e3, avIn_SH, hla2]; rw [avIn_SH] at hK; omega

/-- The continuation loop, entered after a match of `STD_MAX_MATCH` bytes with `lookahead >= MIN_LOOKAHEAD`: it ends
in `CI` with `brk` or `ret`. -/
theorem cloop_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss dist : UInt32} {K : Nat}
    (hn : NotSlow h b)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H)
    (hla : 262 ≤ la.toNat) (hd : dist.toNat ≤ ss.toNat) (hd1 : 1 ≤ dist.toNat) (hd2 : dist.toNat ≤ 32768)
    (hK : avIn H i + la.toNat ≤ K) (body : UInt32 × UInt32 × QuickExit → M (UInt32 × UInt32 × QuickExit))
    (hbody : ∀ ss la ex, body (ss, la, ex) = quick_cont_trip (some b) (.ref (.heap b) wo) 0 dist ss la) :
    Sat H (cwhile (fun (v : UInt32 × UInt32 × QuickExit) => pure (v.2.2.isCont, v)) body (ss, la, QuickExit.cont))
      (fun v H2 => CI h i b flush dist K v H2 ∧ v.2.2.isCont = false) := by
  refine ZlibNgF.Proof.WinInv.sat_cwhileH (CI h i b flush dist K) (fun v _ => CM v)
    (fun v H => CI h i b flush dist K v H ∧ v.2.2.isCont = false) ?_ (s := (ss, la, .cont))
    ⟨I, hla, hd, hK⟩ ?_
  · rintro ⟨ss1, la1, ex⟩ H1 hI
    refine Sat.pure ⟨fun hc => ?_, fun hc => ⟨hI, hc⟩⟩
    cases ex with
    | cont =>
      obtain ⟨I1, h1, h2, h3⟩ := hI
      rw [hbody]
      exact Sat.mono (ctrip_ok T hn hw0 I1 h1 h2 hd1 hd2 h3) fun v H2 ⟨a, m⟩ => ⟨a, by simpa [CM] using m⟩
    | brk => cases hc
    | ret r => cases hc
  · have := UInt32.toNat_lt la
    simp only [CM, fuel]; omega

/-! ## The match part of a trip -/

/-- The invariant of the main loop `for (;;)` of `deflate_quick_impl` over `(strstart, lookahead, exit)`. -/
def QI (h : Heap) (i b : Nat) (flush : Int32) (v : UInt32 × UInt32 × QuickExit) (H : Heap) : Prop :=
  match v.2.2 with
  | .cont => SLI h i b v.2.1 v.1 H
  | .brk => SLI h i b v.2.1 v.1 H ∧ v.2.1 = 0 ∧ avIn H i = 0 ∧ flush ≠ Z_NO_FLUSH
  | .ret r => StratPost h (some i) flush r H

/-- The measure of the main loop. -/
def QM (i : Nat) (v : UInt32 × UInt32 × QuickExit) (H : Heap) : Nat :=
  match v.2.2 with
  | .cont => avIn H i + v.2.1.toNat + 1
  | _ => 0

/-- `quick_try_match` with `static_emit == 0` (`deflate_quick.c:168-220`) on the loop invariant: `none` keeps it (the
`head` store aside), `some` ends the trip in `QI` with a smaller measure. -/
theorem qmatch_ok (T : TreesFacts) {h H : Heap} {i b wo : Nat} {flush : Int32} {la ss : UInt32}
    (hn : NotSlow h b)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)) (I : SLI h i b la ss H)
    (str_val : UInt32) :
    Sat H (quick_try_match (some b) (.ref (.heap b) wo) 0 ss la str_val) (fun o H2 =>
      (o = none → SLI h i b la ss H2 ∧ avIn H2 i = avIn H i) ∧
      (∀ v, o = some v → QI h i b flush v H2 ∧ QM i v H2 < avIn H i + la.toNat + 1)) := by
  obtain ⟨H0, z, st, d, rfl, C⟩ := I
  have I : SLI h i b la ss (SH H0 i z b st d) := ⟨H0, z, st, d, rfl, C⟩
  obtain ⟨-, -, -, ⟨po, ho, L⟩, w1, w2, h65⟩ := sli_facts I hw0
  unfold quick_try_match
  by_cases hl4 : la ≥ WANT_MIN_MATCH
  · simp only [hl4, ↓reduceIte]
    have hl4' : 4 ≤ la.toNat := by simpa [WANT_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hl4
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.InsertSafe.insert_knuth_val_head_SH L ss str_val) ?_)
    rintro hh _ ⟨d1, rfl, W⟩
    have I1 : SLI h i b la ss (SH H0 i z b st d1) := sli_hw I fun ho' e => by
      rw [L.head] at e
      obtain rfl : ho = ho' := by injection e with e; injection e
      exact W
    obtain ⟨-, hwd, hk, -, -, -, -⟩ := sli_facts I1 hw0
    have none_ok : ∀ H2, H2 = SH H0 i z b st d1 → (fun (o : Option (UInt32 × UInt32 × QuickExit)) H2 =>
        (o = none → SLI h i b la ss H2 ∧ avIn H2 i = avIn (SH H0 i z b st d) i) ∧
        (∀ v, o = some v → QI h i b flush v H2 ∧ QM i v H2 < avIn (SH H0 i z b st d) i + la.toNat + 1)) none H2 :=
      fun H2 e => by subst e; exact ⟨fun _ => ⟨I1, by rw [avIn_SH, avIn_SH]⟩, fun v e => by cases e⟩
    refine Sat.bind (Sat.of_eq ldDState_SH ?_)
    by_cases hc : (decide (ss.toUInt64.toInt64 - hh.toUInt64.toInt64 ≤ (MAX_DIST st).toUInt64.toInt64) &&
        decide (ss.toUInt64.toInt64 - hh.toUInt64.toInt64 > 0)) = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨hlt, hmx, hdv⟩ := dist_ok _ _ _ hc
      have hmd : (MAX_DIST st).toNat = st.w_size.toNat - 262 := by
        have e : MAX_DIST st = st.w_size - 262 := rfl
        rw [e, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by show 262 ≤ st.w_size.toNat; omega))]
        rfl
      rw [hmd] at hmx
      refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH hh.toNat (by omega)) ?_)
      obtain ⟨mv, emv⟩ := ZlibNgF.Proof.WinBase.memread4_SH (H := H0) (i := i) (z := z) (b := b) (st := st) (d := d1)
        (off := wo + hh.toNat) (by omega)
      refine Sat.bind (Sat.of_eq emv ?_)
      by_cases he : (str_val == mv) = true
      · simp only [he, ↓reduceIte]
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH ss.toNat (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
        refine Sat.bind (Sat.of_eq (ZlibNgF.Proof.WinBase.addN_SH 2 (by omega)) ?_)
        refine Sat.bind (Sat.mono (ZlibNgF.Proof.Compare256.compare256_ok (SH_bytes H0 i z b st d1) (by omega)
          (by omega)) ?_)
        rintro r _ ⟨rfl, hr⟩
        have hr2 : (r + 2).toNat = r.toNat + 2 := by rw [UInt32.toNat_add]; simp; omega
        by_cases hm4 : r + 2 ≥ WANT_MIN_MATCH
        · simp only [hm4, ↓reduceIte]
          have hm4' : 4 ≤ r.toNat + 2 := by rw [← hr2]; simpa [WANT_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hm4
          obtain ⟨ml, hml, hml1, hml2, hml3⟩ : ∃ ml : UInt32, (if r + 2 > la then la else r + 2) = ml ∧ 4 ≤ ml.toNat ∧
              ml.toNat ≤ 258 ∧ ml.toNat ≤ la.toNat := by
            refine ⟨_, rfl, ?_⟩
            by_cases hg : r + 2 > la
            · simp only [hg, ↓reduceIte]; have := UInt32.lt_iff_toNat_lt.mp hg; omega
            · simp only [hg, ↓reduceIte]; have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hg); omega
          rw [hml]
          generalize hdd : (ss.toUInt64.toInt64 - hh.toUInt64.toInt64).toUInt64.toUInt32 = dd at hdv
          refine Sat.bind (Sat.mono (qdist_ok T (flush := flush) hn hw0 I1 ml dd (by omega) hml2 hml3
            (by omega) (by omega)) ?_)
          rintro ⟨r2, ss2, la2⟩ H2 ⟨⟨q1, q2⟩, e1, e2, e3⟩
          simp only [] at e1 e2 e3 q1 q2
          subst e1 e2
          have hla2 : (la - ml).toNat = la.toNat - ml.toNat :=
            UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
          have hss2 : (ss + ml).toNat = ss.toNat + ml.toNat := by rw [UInt32.toNat_add]; omega
          rw [avIn_SH] at e3
          cases r2 with
          | true =>
            simp only [↓reduceIte]
            refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
            cases e
            exact ⟨q2 rfl, by simp [QM]⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases hcm : ((ml == STD_MAX_MATCH) && decide (la - ml ≥ MIN_LOOKAHEAD)) = true
            · simp only [hcm, ↓reduceIte]
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcm
              have h262 : 262 ≤ (la - ml).toNat := by
                simpa [MIN_LOOKAHEAD, STD_MAX_MATCH, STD_MIN_MATCH] using UInt32.le_iff_toNat_le.mp hcm.2
              refine Sat.bind (Sat.mono (cloop_ok T (flush := flush) (K := avIn H2 i + (la - ml).toNat) hn hw0
                (q1 rfl) h262 (by omega) (by omega) (by omega) (Nat.le_refl _) _ (fun _ _ _ => rfl)) ?_)
              rintro ⟨ss3, la3, ex⟩ H3 ⟨hI3, hc3⟩
              cases ex with
              | cont => cases hc3
              | brk =>
                obtain ⟨I3, hK3⟩ := hI3
                refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
                cases e
                refine ⟨I3, ?_⟩
                dsimp only [QM] at hK3 ⊢
                rw [e3, hla2] at hK3; rw [avIn_SH]; omega
              | ret r =>
                refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
                cases e
                exact ⟨hI3, by simp [QM]⟩
            · simp only [hcm, Bool.false_eq_true, ↓reduceIte]
              refine Sat.pure ⟨fun e => (by cases e), fun v e => ?_⟩
              cases e
              refine ⟨q1 rfl, ?_⟩
              simp only [QM]
              rw [e3, hla2, avIn_SH]; omega
        · simp only [hm4, ↓reduceIte]
          exact Sat.pure (none_ok _ rfl)
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact Sat.pure (none_ok _ rfl)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact Sat.pure (none_ok _ rfl)
  · simp only [hl4, ↓reduceIte]
    exact Sat.pure ⟨fun _ => ⟨I, rfl⟩, fun v e => by cases e⟩

end ZlibNgF.Proof.QuickP
