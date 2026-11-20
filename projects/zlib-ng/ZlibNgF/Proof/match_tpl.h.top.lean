import ZlibNgF.Proof.«match_tpl.h.accept»

/-!
# `longest_match_c`, `longest_match_slow_knuth_c`, `longest_match_slow_roll_c` (`match_tpl.h`, `ZlibNgF`)

The prologue of `LONGEST_MATCH` (`match_tpl.h:26-136`: the loads, the early `return lookahead` of the slow variants,
the `scan_start` / `scan_end` reads, `chain_length >>= 2`, `limit`, and the head lookups of the slow variants)
establishes the loop invariant `LI` of the outer `for (;;)` (`main_loop_ok`).

Premises: the layout `LN`, `PrevBelow d po st B`, `strstart <= B`, and the entry candidate a `Pos` at or above
`limit_base` (the C's IN assertion: its distance is at most `MAX_DIST`; `deflate_fast`, `find_best_match` and
`deflate_slow` call only with `0 < strstart - hash_head <= MAX_DIST`). Result (`PR`): at most the initial `best_len`,
or at most `lookahead` and 258 with `limit_base <= match_start < B`; only `match_start` changes. With `B = 65536`
(`prevBelow_65536`) the theorems need nothing of the hash chains (`*_safe`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.LongestMatch
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Compare256 ZlibNg.InsertStringP ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem (sat_add sat_memread8 sat_memread4 sat_index8)
open ZlibNgF.Proof.WinBase (knuth_lt roll_lt)

variable {B : Nat}

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {st : DeflateState} {d : Array UInt8}

theorem LH_self : LH H i z b st d st.match_start = SH H i z b st d := by
  cases st; rfl

/-- The head lookups of `longest_match_slow_knuth_c` (`match_tpl.h:115-125`): positions `scan + i`,
`i + 3 <= best_len`; a smaller head entry replaces `cur_match` with `match_offset = i`. -/
theorem knuth_loop_ok {wo po ho : Nat} (N : LN d wo po ho st) (bl cm : UInt32) (hbl : bl.toNat < 65536)
    (hcm : cm.toNat < 65536) (ms : UInt32) :
    Sat (LH H i z b st d ms) (cwhile
      (fun (x : UInt32 × UInt32 × UInt32) => pure (decide (x.fst + (WANT_MIN_MATCH - 1) ≤ bl), x.fst, x.2.fst, x.2.snd))
      (fun x => do
        let p ← Ptr.add (.ref (.heap b) (wo + st.strstart.toNat)) ↑x.fst.toNat
        let val ← memread4 p
        let q ← posLoad (.ref (.heap b) ho) ↑(UPDATE_HASH_KNUTH val).toNat
        if q.toUInt32 < x.2.snd then pure (x.fst + 1, x.fst, q.toUInt32)
          else pure (x.fst + 1, x.2.fst, x.2.snd))
      (1, 0, cm))
      (fun x H' => H' = LH H i z b st d ms ∧ x.2.fst.toNat ≤ bl.toNat ∧ x.2.snd.toNat < 65536) := by
  have hst := N.look
  have hbig := N.big
  have hhd := N.hd
  have G := LH_get (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) ms
  have h3 : (WANT_MIN_MATCH - 1 : UInt32).toNat = 3 := by decide
  refine sat_cwhile
    (fun (x : UInt32 × UInt32 × UInt32) H' => H' = LH H i z b st d ms ∧ 1 ≤ x.1.toNat ∧ x.1.toNat ≤ bl.toNat + 1 ∧
      x.2.1.toNat ≤ bl.toNat ∧ x.2.2.toNat < 65536)
    (fun x => bl.toNat + 1 - x.1.toNat) _ ?_ ⟨rfl, by simp, by simp, by simp, hcm⟩ (by simp [fuel]; omega)
  rintro ⟨j, mo, c⟩ _ ⟨rfl, hj1, hj2, hmo, hc⟩
  dsimp only at hj1 hj2 hmo hc
  refine Sat.pure ⟨fun ht => ?_, fun _ => ⟨rfl, hmo, hc⟩⟩
  simp only [decide_eq_true_eq] at ht
  have ht' := UInt32.le_iff_toNat_le.mp ht
  rw [UInt32.toNat_add, h3, Nat.mod_eq_of_lt (by omega)] at ht'
  have hj : (j + 1).toNat = j.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  dsimp only
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ (wo + st.strstart.toNat + j.toNat) (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread4 G (by omega)) ?_)
  rintro val _ rfl
  refine Sat.bind (Sat.mono (posLoad_v G _ (by have := knuth_lt val; omega)) ?_)
  rintro q _ ⟨rfl, -⟩
  have hq := UInt16.toNat_lt q
  split
  · exact Sat.pure ⟨⟨rfl, by simp only []; omega, by simp only []; omega, by simp only []; omega,
      by simp only [UInt16.toNat_toUInt32]; omega⟩, by simp only []; omega⟩
  · exact Sat.pure ⟨⟨rfl, by simp only []; omega, by simp only []; omega, hmo, hc⟩, by simp only []; omega⟩

/-- The head lookups of `longest_match_slow_roll_c` (`match_tpl.h:102-112`): the rolling hash of `scan[i-2..i]`,
`3 <= i <= best_len`; a smaller head entry replaces `cur_match` with `match_offset = i - 2`. -/
theorem roll_loop_ok {wo po ho : Nat} (N : LN d wo po ho st) (bl cm h0 : UInt32) (hbl : bl.toNat < 65536)
    (hcm : cm.toNat < 65536) (ms : UInt32) :
    Sat (LH H i z b st d ms) (cwhile
      (fun (x : UInt32 × UInt32 × UInt32 × UInt32) => pure (decide (x.fst ≤ bl), x.fst, x.2.fst, x.2.2.fst, x.2.2.snd))
      (fun x => do
        let c ← index8 (.ref (.heap b) (wo + st.strstart.toNat)) ↑x.fst.toNat
        let q ← posLoad (.ref (.heap b) ho) ↑(update_hash_roll x.2.fst c.toUInt32).toNat
        if q.toUInt32 < x.2.2.snd then
            pure (x.fst + 1, update_hash_roll x.2.fst c.toUInt32, x.fst - 2, q.toUInt32)
          else pure (x.fst + 1, update_hash_roll x.2.fst c.toUInt32, x.2.2.fst, x.2.2.snd))
      (3, h0, 0, cm))
      (fun x H' => H' = LH H i z b st d ms ∧ x.2.2.fst.toNat ≤ bl.toNat ∧ x.2.2.snd.toNat < 65536) := by
  have hst := N.look
  have hbig := N.big
  have hhd := N.hd
  have G := LH_get (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) ms
  refine sat_cwhile
    (fun (x : UInt32 × UInt32 × UInt32 × UInt32) H' => H' = LH H i z b st d ms ∧ 3 ≤ x.1.toNat ∧
      x.1.toNat ≤ bl.toNat + 3 ∧ x.2.2.1.toNat ≤ bl.toNat ∧ x.2.2.2.toNat < 65536)
    (fun x => bl.toNat + 3 - x.1.toNat) _ ?_ ⟨rfl, by simp, by simp, by simp, hcm⟩ (by simp [fuel]; omega)
  rintro ⟨j, hh, mo, c⟩ _ ⟨rfl, hj1, hj2, hmo, hc⟩
  dsimp only at hj1 hj2 hmo hc
  refine Sat.pure ⟨fun ht => ?_, fun _ => ⟨rfl, hmo, hc⟩⟩
  simp only [decide_eq_true_eq] at ht
  have ht' := UInt32.le_iff_toNat_le.mp ht
  have hj : (j + 1).toNat = j.toNat + 1 := by rw [UInt32.toNat_add]; simp; omega
  have hj2' : (j - 2).toNat = j.toNat - 2 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; show 2 ≤ _; omega)]; rfl
  dsimp only
  refine Sat.bind (Sat.mono (sat_index8 G (k := wo + st.strstart.toNat) j.toNat (by omega)) ?_)
  rintro x _ rfl
  refine Sat.bind (Sat.mono (posLoad_v G _ (by
    have := roll_lt hh x.toUInt32
    simp only [update_hash_roll] at this ⊢; omega)) ?_)
  rintro q _ ⟨rfl, -⟩
  have hq := UInt16.toNat_lt q
  split
  · exact Sat.pure ⟨⟨rfl, by simp only []; omega, by simp only []; omega, by simp only []; omega,
      by simp only [UInt16.toNat_toUInt32]; omega⟩, by simp only []; omega⟩
  · exact Sat.pure ⟨⟨rfl, by simp only []; omega, by simp only []; omega, hmo, hc⟩, by simp only []; omega⟩

/-- The outer loop of `LONGEST_MATCH` and its `return best_len` (`match_tpl.h:137-297`). -/
theorem main_tail {e : LMEnv} {v : LMVars} {wo po ho bl0 : Nat} (E : LE b wo po ho st e) (N : LN d wo po ho st)
    (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B) (V : VI b wo st v) {ms : UInt32}
    (hb : BL st B bl0 v.best_len ms) :
    Sat (LH H i z b st d ms) (do
      let x ← cwhile (fun (x : LMExit × LMVars) => pure (x.fst.isCont, x.fst, x.snd))
        (fun x => LM.loop_body e x.snd) (LMExit.cont, v)
      match x.fst with
      | .ret r => pure r
      | _ => pure x.snd.best_len)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧ PR st B bl0 r ms) := by
  refine Sat.bind (Sat.mono (main_loop_ok E N hp hBs V hb) ?_)
  rintro ⟨x, v⟩ _ ⟨⟨ms, rfl, hx⟩, hc⟩
  cases x with
  | cont => simp [LMExit.isCont] at hc
  | brk => exact Sat.pure ⟨ms, rfl, BL.pr hx⟩
  | ret r => exact Sat.pure ⟨ms, rfl, hx⟩

/-- `longest_match_c` (levels 2-6): with `prev` entries 0 or below `B`, `strstart <= B` and the entry candidate
`cur_match` a `Pos` at or above `limit_base` (the C's IN assertion `strstart - cur_match <= MAX_DIST`), it runs
without fault, changes only `match_start`, and returns at most `STD_MIN_MATCH - 1`, or at most `lookahead` and 258
with `limit_base <= match_start < B`. -/
theorem longest_match_c_ok {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (N : LN d wo po ho st) (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B)
    (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧ PR st B 2 r ms) := by
  have hst := N.look
  have hbig := N.big
  unfold longest_match_c LONGEST_MATCH
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [hw, hpv, Ival.get, Bool.false_eq_true, ↓reduceIte]
  have h0 : (if STD_MIN_MATCH - 1 ≥ 8 then STD_MIN_MATCH - 1 - 7 else 0 : UInt32) = 0 := by decide
  rw [h0]
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  rw [← LH_self]
  have G := LH_get (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) st.match_start
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ (wo + st.strstart.toNat) (by omega) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 G (by omega)) ?_)
  rintro ss _ rfl
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ (wo + st.strstart.toNat) (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 G (by omega)) ?_)
  rintro se _ rfl
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ wo (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  have hb2 : (STD_MIN_MATCH - 1 : UInt32).toNat = 2 := by decide
  refine main_tail (bl0 := 2) ?E N hp hBs ?V (Or.inl hb2)
  case E => exact ⟨rfl, rfl, rfl, rfl, fun h => (by cases h), rfl, rfl, rfl, fun h => (by simp at h)⟩
  case V => exact ⟨rfl, by simp, by simp, by simp only []; omega, hcm, by simp, by simp only [UInt32.toNat_zero]; rfl,
      by simp only []; exact hlb⟩

/-- The slow variants `LONGEST_MATCH` with `LONGEST_MATCH_SLOW` (levels 7-9), `roll` selecting the rolling-hash
variant. `best_len` starts at `prev_length` (or `STD_MIN_MATCH - 1` when it is 0). -/
theorem longest_match_slow_ok (roll : Bool) {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (hhd : st.head = .val (.ref (.heap b) ho))
    (N : LN d wo po ho st) (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B)
    (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (LONGEST_MATCH true roll (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧
        PR st B (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) := by
  have hst := N.look
  have hbig := N.big
  have hhd' := N.hd
  have hlb2 := (limitBase_le st N.w_lo).1
  unfold LONGEST_MATCH
  refine Sat.bind (Sat.of_eq ldDState_SH ?_)
  simp only [hw, hpv, hhd, Ival.get, ↓reduceIte]
  generalize (if (st.prev_length != 0) = true then st.prev_length else STD_MIN_MATCH - 1) = bl
  rw [← LH_self]
  have G := LH_get (H := H) (i := i) (z := z) (b := b) (st := st) (d := d) st.match_start
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  refine Sat.bind (Sat.pure ?_)
  split
  · rename_i hge
    exact Sat.pure ⟨_, rfl, Or.inl (UInt32.le_iff_toNat_le.mp hge)⟩
  rename_i hlt
  have hbl : bl.toNat < st.lookahead.toNat := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hlt)
  have hoff := off_le bl
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ (wo + st.strstart.toNat) (by omega) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 G (by omega)) ?_)
  rintro ss _ rfl
  refine Sat.bind (Sat.mono (sat_add G (by omega) _
    (wo + st.strstart.toNat + (if bl ≥ 8 then bl - 7 else 0 : UInt32).toNat) (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  refine Sat.bind (Sat.mono (sat_memread8 G (by omega)) ?_)
  rintro se _ rfl
  refine Sat.bind (Sat.mono (sat_add G (by omega) _ (wo + (if bl ≥ 8 then bl - 7 else 0 : UInt32).toNat)
    (by simp) (by omega)) ?_)
  rintro _ _ ⟨rfl, rfl⟩
  have E : ∀ (lb : UInt32), lb = limitBase st → ∀ (osr : Bool),
      LE b wo po ho st
        { slow := true, roll := roll, st := some b, wmask := W_MASK st, strstart := st.strstart,
          window := .ref (.heap b) wo, prev := .ref (.heap b) po, head := .ref (.heap b) ho,
          scan := .ref (.heap b) (wo + st.strstart.toNat), limit_base := lb, nice_match := st.nice_match.toUInt32,
          lookahead := st.lookahead, scan_start := ss, offset_search := osr } :=
    fun lb hlb osr => ⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, hlb, fun _ => rfl⟩
  have tail : ∀ (c mo lim : UInt32), c.toNat < 65536 → mo.toNat ≤ bl.toNat →
      lim.toNat = (limitBase st).toNat + mo.toNat → lim.toNat ≤ c.toNat → ∀ (chain : UInt32) (osr : Bool),
      Sat (LH H i z b st d st.match_start) (do
        let x ← cwhile (fun (x : LMExit × LMVars) => pure (x.fst.isCont, x.fst, x.snd))
          (fun x => LM.loop_body
            { slow := true, roll := roll, st := some b, wmask := W_MASK st,
              strstart := st.strstart, window := .ref (.heap b) wo, prev := .ref (.heap b) po,
              head := .ref (.heap b) ho, scan := .ref (.heap b) (wo + st.strstart.toNat),
              limit_base := if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0,
              nice_match := st.nice_match.toUInt32, lookahead := st.lookahead, scan_start := ss,
              offset_search := osr } x.snd)
          (LMExit.cont,
            { chain_length := chain, best_len := bl, offset := if bl ≥ 8 then bl - 7 else 0,
              cur_match := c, match_offset := mo, scan_end := se, mbase_start := .ref (.heap b) wo,
              mbase_end := .ref (.heap b) (wo + (if bl ≥ 8 then bl - 7 else 0 : UInt32).toNat), limit := lim })
        match x.fst with
        | .ret r => pure r
        | _ => pure x.snd.best_len)
        (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧ PR st B bl.toNat r ms) := by
    intro c mo lim hc hmo hl hle chain osr
    exact main_tail (E _ rfl osr) N hp hBs ⟨rfl, rfl, hoff, show bl.toNat ≤ 65536 by omega, hc, show mo.toNat ≤ 65536 by omega, hl, hle⟩ (Or.inl rfl)
  split
  · rename_i h3
    split
    · refine Sat.bind (Sat.mono (sat_index8 G (k := wo + st.strstart.toNat) 1 (by omega)) ?_)
      rintro x1 _ rfl
      refine Sat.bind (Sat.mono (sat_index8 G (k := wo + st.strstart.toNat) 2 (by omega)) ?_)
      rintro x2 _ rfl
      refine Sat.bind (Sat.mono (roll_loop_ok N bl cm _ (by omega) hcm st.match_start) ?_)
      rintro ⟨j, hh, mo, c⟩ _ ⟨rfl, hmo, hc⟩
      dsimp only at hmo hc ⊢
      by_cases hgt : c ≤ (if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0) + mo
      · simp only [hgt, ↓reduceIte]; exact Sat.pure ⟨_, rfl, Or.inl (Nat.le_refl _)⟩
      · simp only [hgt, ↓reduceIte]
        have hgt' := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt)
        have hl : ((if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0) + mo).toNat =
            (limitBase st).toNat + mo.toNat := by
          show (limitBase st + mo).toNat = _; rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        exact tail c mo _ hc hmo hl (by omega) _ _
    · refine Sat.bind (Sat.mono (knuth_loop_ok N bl cm (by omega) hcm st.match_start) ?_)
      rintro ⟨j, mo, c⟩ _ ⟨rfl, hmo, hc⟩
      dsimp only at hmo hc ⊢
      by_cases hgt : c ≤ (if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0) + mo
      · simp only [hgt, ↓reduceIte]; exact Sat.pure ⟨_, rfl, Or.inl (Nat.le_refl _)⟩
      · simp only [hgt, ↓reduceIte]
        have hgt' := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp hgt)
        have hl : ((if st.strstart > MAX_DIST st then st.strstart - MAX_DIST st else 0) + mo).toNat =
            (limitBase st).toNat + mo.toNat := by
          show (limitBase st + mo).toNat = _; rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        exact tail c mo _ hc hmo hl (by omega) _ _
  · exact tail cm 0 _ hcm (by simp) (by simp [limitBase]) hlb _ _

/-- `longest_match_slow_knuth_c` (levels 7-8). -/
theorem longest_match_slow_knuth_c_ok {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (hhd : st.head = .val (.ref (.heap b) ho))
    (N : LN d wo po ho st) (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B)
    (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_slow_knuth_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧
        PR st B (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) :=
  longest_match_slow_ok false hw hpv hhd N hp hBs hcm hlb

/-- `longest_match_slow_roll_c` (level 9). -/
theorem longest_match_slow_roll_c_ok {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (hhd : st.head = .val (.ref (.heap b) ho))
    (N : LN d wo po ho st) (hp : PrevBelow d po st B) (hBs : st.strstart.toNat ≤ B)
    (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_slow_roll_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧
        PR st B (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) :=
  longest_match_slow_ok true hw hpv hhd N hp hBs hcm hlb

/-! ## Memory safety with no assumption on the hash chains (`B = 65536`) -/

theorem longest_match_c_safe {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (N : LN d wo po ho st) (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧ PR st 65536 2 r ms) :=
  longest_match_c_ok hw hpv N (prevBelow_65536 d po st) (by have := N.look; omega) hcm hlb

theorem longest_match_slow_knuth_c_safe {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (hhd : st.head = .val (.ref (.heap b) ho))
    (N : LN d wo po ho st) (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_slow_knuth_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧
        PR st 65536 (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) :=
  longest_match_slow_knuth_c_ok hw hpv hhd N (prevBelow_65536 d po st) (by have := N.look; omega) hcm hlb

theorem longest_match_slow_roll_c_safe {wo po ho : Nat} {cm : UInt32}
    (hw : st.window = .val (.ref (.heap b) wo)) (hpv : st.prev = .val (.ref (.heap b) po))
    (hhd : st.head = .val (.ref (.heap b) ho))
    (N : LN d wo po ho st) (hcm : cm.toNat < 65536) (hlb : (limitBase st).toNat ≤ cm.toNat) :
    Sat (SH H i z b st d) (longest_match_slow_roll_c (some b) cm)
      (fun r H' => ∃ ms, H' = LH H i z b st d ms ∧
        PR st 65536 (if st.prev_length != 0 then st.prev_length else STD_MIN_MATCH - 1).toNat r ms) :=
  longest_match_slow_roll_c_ok hw hpv hhd N (prevBelow_65536 d po st) (by have := N.look; omega) hcm hlb

end

end ZlibNgF.Proof.LongestMatch
