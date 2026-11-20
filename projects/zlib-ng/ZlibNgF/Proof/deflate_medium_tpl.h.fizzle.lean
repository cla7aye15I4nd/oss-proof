import ZlibNgF.Proof.«deflate_medium_tpl.h.insert»
import ZlibNgF.Proof.«compare256_c.c.safety»

/-!
# `memcmp`, `max_match_continues` and `fizzle_matches` (`ZlibNgF`)

All three only read block `b` (the window and what follows it in the allocation of `alloc_deflate`).

* `memcmp(s1, s2, n)` forms `s1 + n` and `s2 + n` and reads `s1[j]`, `s2[j]` for `j < n`.
* `max_match_continues(window, strstart, dist)` (`deflate_p.h`) reads 8 bytes at `window + strstart` and at
  `window + strstart - dist` and compares 256 bytes from `+ 2` of each: with `dist <= strstart` every pointer is in the
  block, and the result is at most 258.
* `fizzle_matches(window, current, next, max_dist)` (`deflate_medium_tpl.h:100-167`) forms
  `window + next.match_start + 1 - current.match_length` and `window + next.strstart + 1 - current.match_length`; the
  caller's guard `current.match_length - 1 <= next.match_start` (and `next.match_start < next.strstart`) keeps both at
  or above `window` (ISO C17 §6.5.6p8: each intermediate pointer is formed and checked). After a successful fizzle,
  `next` moves back by `need = current.match_length - 1` (or `current.match_length` with the extra byte, whose pointers
  `window + match_start - 1` and `window + strstart - 1` are formed only when `steps == current.match_length <=
  match_start - 1`), its length grows by the same amount and stays at most 258 (`steps <= STD_MAX_MATCH -
  next.match_length`), and the distance `strstart - match_start` is kept.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumFizzle
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.DeflateMedium
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem (sat_add sat_memread8 sat_load)
open ZlibNgF.Proof.Compare256 (compare256_ok)

/-- `MIN` of two `int32_t` as `fizzle_matches` writes it: `a > b ? b : a`. -/
def imin (x y : Int32) : Int32 := if x > y then y else x

theorem imin_def (x y : Int32) : (if x > y then y else x) = imin x y := rfl

theorem imin_toInt (x y : Int32) : (imin x y).toInt = min x.toInt y.toInt := by
  unfold imin; split
  · rename_i h; have := Int32.lt_iff_toInt_lt.mp h; omega
  · rename_i h; have : ¬ y.toInt < x.toInt := fun h' => h (Int32.lt_iff_toInt_lt.mpr h'); omega

theorem chk_eq {H : Heap} (v : Int) (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    chkI32 v H = .ok (Int32.ofInt v, H) := by
  unfold chkI32; rw [ite_eq_left ⟨h1, h2⟩]; rfl

theorem u32_sub (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact h)

theorem u32_add (x y : UInt32) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem ofInt_toInt (v : Int) (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : (Int32.ofInt v).toInt = v :=
  Int32.toInt_ofInt_of_le h1 h2

section
variable {H : Heap} {r : BRef} {a : Array UInt8}

/-- `memcmp(s1, s2, n)` on two ranges of one live object. -/
theorem memcmp_ok (hb : Space.get H r = some a) {o1 o2 n : Nat} (hn : n ≤ 258) (h1 : o1 + n ≤ a.size) (h2 : o2 + n ≤ a.size) :
    Sat H (memcmp (.ref r o1) (.ref r o2) n) (fun _ H' => H' = H) := by
  unfold memcmp
  refine Sat.bind (Sat.mono (sat_add hb (by omega) n (o1 + n) rfl h1) ?_)
  rintro _ H1 ⟨-, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) n (o2 + n) rfl h2) ?_)
  rintro _ H1 ⟨-, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_cwhile (s := ((none : Option Int32), 0))
    (fun (x : Option Int32 × Nat) H' => H' = H ∧ x.2 ≤ n)
    (fun x => n - x.2 + (if x.1.isNone then 1 else 0)) (fun _ H' => H' = H) ?_ ⟨rfl, Nat.zero_le _⟩ ?_) ?_)
  · rintro ⟨q, j⟩ H1 ⟨e, hj⟩; subst H1
    refine Sat.pure ⟨fun hc => ?_, fun _ => rfl⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hq, hjn⟩ := hc
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.LongestMatch.index8_v hb j (by omega)) ?_)
    rintro _ H1 ⟨e, -⟩; subst H1
    refine Sat.bind (Sat.mono (ZlibNgF.Proof.LongestMatch.index8_v hb j (by omega)) ?_)
    rintro _ H1 ⟨e, -⟩; subst H1
    split
    · exact Sat.pure ⟨⟨rfl, hj⟩, by simp <;> omega⟩
    · exact Sat.pure ⟨⟨rfl, by omega⟩, by simp <;> omega⟩
  · simp [fuel]; omega
  · rintro _ H1 e; subst H1; exact Sat.pure rfl

/-- `max_match_continues(window, strstart, dist)` with `dist <= strstart` and 266 bytes after `window + strstart`:
no fault, the heap kept, at most 258. -/
theorem max_match_continues_ok (hb : Space.get H r = some a) {wo : Nat} (ss dist : UInt32)
    (hd : dist.toNat ≤ ss.toNat) (hk : wo + ss.toNat + 266 ≤ a.size) :
    Sat H (max_match_continues (.ref r wo) ss dist) (fun v H' => H' = H ∧ v.toNat ≤ 258) := by
  unfold max_match_continues
  refine Sat.bind (Sat.mono (sat_add hb (by omega) ss.toNat (wo + ss.toNat) rfl (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_)
  rintro _ H1 e; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (-(dist.toNat : Int)) (wo + ss.toNat - dist.toNat) (by omega)
    (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_)
  rintro _ H1 e; subst H1
  split
  · exact Sat.pure ⟨rfl, by simp⟩
  refine Sat.bind (Sat.mono (sat_add hb (by omega) 2 (wo + ss.toNat + 2) rfl (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (-(dist.toNat : Int)) (wo + ss.toNat - dist.toNat) (by omega)
    (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) 2 (wo + ss.toNat - dist.toNat + 2) rfl (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (compare256_ok hb (by omega) (by omega)) ?_)
  rintro v H1 ⟨e, hv⟩; subst H1
  exact Sat.pure ⟨rfl, by rw [UInt32.toNat_add]; simp; omega⟩

/-- What `fizzle_matches` returns: `current` and `next` unchanged, or `next` moved back by `k` (`need` or `need + 1`,
`need = current.match_length - 1`), longer by `k` and at most 258, `orgstart` one higher, and `current` of length
`current.match_length - k` (1 or 0). -/
def FizOk (cur nxt c n : Match) : Prop :=
  (c = cur ∧ n = nxt) ∨ ∃ k : Nat, (k + 1 = cur.match_length.toNat ∨ k = cur.match_length.toNat) ∧
    c = { cur with match_length := c.match_length } ∧ c.match_length.toNat = cur.match_length.toNat - k ∧
    k ≤ nxt.match_start.toNat ∧
    n.match_start.toNat = nxt.match_start.toNat - k ∧ n.strstart.toNat = nxt.strstart.toNat - k ∧
    n.match_length.toNat = nxt.match_length.toNat + k ∧ n.orgstart = nxt.orgstart + 1 ∧ n.match_length.toNat ≤ 258

set_option maxHeartbeats 1600000 in
theorem fizzle_ok (hb : Space.get H r = some a) {wo : Nat} (cur nxt : Match) (md : Int32)
    (hmd0 : 0 ≤ md.toInt) (hmd1 : md.toInt ≤ 65536)
    (hL : 2 ≤ cur.match_length.toNat) (hL2 : cur.match_length.toNat ≤ 258)
    (hLm : cur.match_length.toNat - 1 ≤ nxt.match_start.toNat)
    (hms : nxt.match_start.toNat < nxt.strstart.toNat) (hs : nxt.strstart.toNat ≤ 65536)
    (hnl : nxt.match_length.toNat ≤ 258) (hbig : wo + 65536 + 16 ≤ a.size) :
    Sat H (fizzle_matches (.ref r wo) cur nxt md) (fun cn H' => H' = H ∧ FizOk cur nxt cn.1 cn.2) := by
  unfold fizzle_matches
  dsimp only
  generalize hL' : cur.match_length.toNat = L at *
  generalize hM : nxt.match_start.toNat = ms at *
  generalize hS : nxt.strstart.toNat = ss at *
  refine Sat.bind (Sat.mono (sat_add hb (by omega) ms (wo + ms) (by omega) (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) 1 (wo + ms + 1) rfl (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (-(L : Int)) (wo + ms + 1 - L) (by omega) (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) ss (wo + ss) (by omega) (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) 1 (wo + ss + 1) rfl (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_add hb (by omega) (-(L : Int)) (wo + ss + 1 - L) (by omega) (by omega)) ?_)
  rintro _ H1 ⟨rfl, e⟩; subst H1
  refine Sat.bind (Sat.mono (sat_load hb (by omega)) ?_)
  rintro _ H1 e; subst H1
  refine Sat.bind (Sat.mono (sat_load hb (by omega)) ?_)
  rintro _ H1 e; subst H1
  split
  · exact Sat.pure ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  have u := ZlibNgF.Proof.DeflateAlloc.u32_toInt32_toInt
  have hs32 : nxt.strstart.toInt32.toInt = ss := by rw [u _ (by omega), hS]
  have hms32 : nxt.match_start.toInt32.toInt = ms := by rw [u _ (by omega), hM]
  have hL32 : cur.match_length.toInt32.toInt = L := by rw [u _ (by omega), hL']
  have hnl32 : nxt.match_length.toInt32.toInt = nxt.match_length.toNat := u _ (by omega)
  have e1 : (cur.match_length - 1).toNat = L - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]; simp [hL']
  have hneed32 : (cur.match_length - 1).toInt32.toInt = L - 1 := by rw [u _ (by omega), e1]; omega
  have h258 : ((STD_MAX_MATCH.toNat : Nat) : Int) = 258 := rfl
  split
  case' isTrue =>
    rename_i hgt
    have hgt' : md.toInt < ss := by have := Int32.lt_iff_toInt_lt.mp hgt; rw [hs32] at this; exact this
    refine Sat.bind (Sat.of_eq (chk_eq _ (by rw [hs32]; omega) (by rw [hs32]; omega)) ?_)
    have hl : (Int32.ofInt (nxt.strstart.toInt32.toInt - md.toInt)).toInt = ss - md.toInt := by
      rw [ofInt_toInt _ (by rw [hs32]; omega) (by rw [hs32]; omega), hs32]
    have hl0 : 0 ≤ (Int32.ofInt (nxt.strstart.toInt32.toInt - md.toInt)).toInt := by omega
    have hl1 : (Int32.ofInt (nxt.strstart.toInt32.toInt - md.toInt)).toInt ≤ ss := by omega
    clear hl
    generalize Int32.ofInt (nxt.strstart.toInt32.toInt - md.toInt) = lim at *
  case' isFalse =>
    refine Sat.bind (Sat.pure ?_)
    have hl0 : 0 ≤ (0 : Int32).toInt := by decide
    have hl1 : (0 : Int32).toInt ≤ ss := by simp
    generalize (0 : Int32) = lim at *
  all_goals
    refine Sat.bind (Sat.of_eq (chk_eq _ (by rw [hs32]; omega) (by rw [hs32]; omega)) ?_)
    refine Sat.bind (Sat.of_eq (chk_eq _ (by rw [h258, hnl32]; omega) (by rw [h258, hnl32]; omega)) ?_)
    refine Sat.bind (Sat.of_eq (chk_eq _ (by rw [hms32]; omega) (by rw [hms32]; omega)) ?_)
    have hA : (Int32.ofInt (nxt.strstart.toInt32.toInt - lim.toInt)).toInt = ss - lim.toInt := by
      rw [ofInt_toInt _ (by rw [hs32]; omega) (by rw [hs32]; omega), hs32]
    have hB : (Int32.ofInt ((STD_MAX_MATCH.toNat : Nat) - nxt.match_length.toInt32.toInt)).toInt =
        258 - nxt.match_length.toNat := by
      rw [ofInt_toInt _ (by rw [h258, hnl32]; omega) (by rw [h258, hnl32]; omega), h258, hnl32]
    have hC : (Int32.ofInt (nxt.match_start.toInt32.toInt - 1)).toInt = ms - 1 := by
      rw [ofInt_toInt _ (by rw [hms32]; omega) (by rw [hms32]; omega), hms32]
    generalize Int32.ofInt (nxt.strstart.toInt32.toInt - lim.toInt) = A at *
    generalize Int32.ofInt ((STD_MAX_MATCH.toNat : Nat) - nxt.match_length.toInt32.toInt) = B at *
    generalize Int32.ofInt (nxt.match_start.toInt32.toInt - 1) = C at *
    have hst : (if (if cur.match_length.toInt32 > A then A else cur.match_length.toInt32) >
          (if B > C then C else B) then (if B > C then C else B)
          else (if cur.match_length.toInt32 > A then A else cur.match_length.toInt32)).toInt =
        min (min (L : Int) (ss - lim.toInt)) (min (258 - nxt.match_length.toNat) (ms - 1)) := by
      show (imin (imin cur.match_length.toInt32 A) (imin B C)).toInt = _
      rw [imin_toInt, imin_toInt, imin_toInt, hL32, hA, hB, hC]
    generalize (if (if cur.match_length.toInt32 > A then A else cur.match_length.toInt32) >
          (if B > C then C else B) then (if B > C then C else B)
          else (if cur.match_length.toInt32 > A then A else cur.match_length.toInt32)) = steps at *
    by_cases hge : steps < (cur.match_length - 1).toInt32
    · rw [ite_eq_left hge]; exact Sat.pure ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    rw [ite_eq_right hge]
    have hge' : (L : Int) - 1 ≤ steps.toInt := by
      have : ¬ steps.toInt < (cur.match_length - 1).toInt32.toInt := fun h => hge (Int32.lt_iff_toInt_lt.mpr h)
      omega
    clear hge
    have hms1 : (nxt.match_start - (cur.match_length - 1)).toNat = ms - (L - 1) := by
      rw [u32_sub _ _ (by omega), e1, hM]
    have hss1 : (nxt.strstart - (cur.match_length - 1)).toNat = ss - (L - 1) := by
      rw [u32_sub _ _ (by omega), e1, hS]
    have hml1 : (nxt.match_length + (cur.match_length - 1)).toNat = nxt.match_length.toNat + (L - 1) := by
      rw [u32_add _ _ (by omega), e1]
    -- the result without and with the extra byte
    have post1 : FizOk cur nxt
        ({ match_start := cur.match_start, match_length := 1, strstart := cur.strstart,
            orgstart := cur.orgstart } : Match)
        ({ match_start := nxt.match_start - (cur.match_length - 1),
            match_length := nxt.match_length + (cur.match_length - 1),
            strstart := nxt.strstart - (cur.match_length - 1), orgstart := nxt.orgstart + 1 } : Match) := by
      unfold FizOk; dsimp only
      apply Or.inr
      refine ⟨L - 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hL']; exact Or.inl (Nat.sub_add_cancel (by omega))
      · exact Eq.refl _
      · rw [hL', UInt32.toNat_one]; omega
      · rw [hM]; omega
      · rw [hms1, hM]
      · rw [hss1, hS]
      · rw [hml1]
      · exact Eq.refl _
      · rw [hml1]; omega
    by_cases hn : (cur.match_length - 1).toNat ≤ 8
    focus
      rw [ite_eq_left hn]
      refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro _ H1 rfl
      refine Sat.bind (Sat.mono (sat_memread8 hb (by omega)) ?_); rintro _ H1 rfl
      refine Sat.bind (Sat.mono (ZlibNgF.Proof.MatchBits.mask_ok _ (by omega) (by omega)) ?_)
      rintro _ H1 ⟨rfl, -⟩
      split
      · exact Sat.pure ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    rotate_left
    focus
      rw [ite_eq_right hn]
      refine Sat.bind (Sat.mono (memcmp_ok hb (by omega) (by omega) (by omega)) ?_); rintro _ H1 rfl
      split
      · exact Sat.pure ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    all_goals
        by_cases hx : (steps == cur.match_length.toInt32) = true
        · rw [ite_eq_left hx]
          have hsL : steps.toInt = L := by rw [beq_iff_eq.mp hx, hL32]
          refine Sat.bind (Sat.mono (sat_add hb (by omega) _ (wo + (ms - (L - 1))) (by rw [hms1]; omega)
            (by omega)) ?_)
          rintro _ H1 ⟨rfl, e⟩; subst H1
          refine Sat.bind (Sat.mono (sat_add hb (by omega) (-1) (wo + (ms - (L - 1)) - 1) (by omega) (by omega)) ?_)
          rintro _ H1 ⟨rfl, e⟩; subst H1
          refine Sat.bind (Sat.mono (sat_add hb (by omega) _ (wo + (ss - (L - 1))) (by rw [hss1]; omega)
            (by omega)) ?_)
          rintro _ H1 ⟨rfl, e⟩; subst H1
          refine Sat.bind (Sat.mono (sat_add hb (by omega) (-1) (wo + (ss - (L - 1)) - 1) (by omega) (by omega)) ?_)
          rintro _ H1 ⟨rfl, e⟩; subst H1
          refine Sat.bind (Sat.mono (sat_load hb (by omega)) ?_)
          rintro x H1 e; subst H1
          refine Sat.bind (Sat.mono (sat_load hb (by omega)) ?_)
          rintro y H1 e; subst H1
          by_cases hxy : (x == y) = true
          · rw [ite_eq_left hxy]
            refine Sat.pure ⟨rfl, ?_⟩
            unfold FizOk; dsimp only
            have e2 : (1 : UInt32).toNat = 1 := rfl
            refine Or.inr ⟨L, ?_, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
            · exact Or.inr hL'.symm
            · rw [hL']; simp
            · rw [hM]; omega
            · rw [u32_sub _ _ (by rw [hms1, e2]; omega), hms1, hM, e2]; omega
            · rw [u32_sub _ _ (by rw [hss1, e2]; omega), hss1, hS, e2]; omega
            · rw [u32_add _ _ (by rw [hml1, e2]; omega), hml1, e2]; omega
            · rw [u32_add _ _ (by rw [hml1, e2]; omega), hml1, e2]; omega
          · rw [ite_eq_right hxy]; exact Sat.pure ⟨rfl, post1⟩
        · rw [ite_eq_right hx]; exact Sat.pure ⟨rfl, post1⟩

end

end ZlibNgF.Proof.MediumFizzle
