import ZlibNgF.Proof.«compare256_c.c.safety»

/-!
# Bit helpers of `LONGEST_MATCH` (`ZlibNgF`)

The short-candidate filter of `match_tpl.h:150-183` accepts a candidate when the first `best_len + 1` bytes of
`diff = scan_start ^ cand_start` are zero (`(diff & zng_first_bytes_mask64(best_len + 1)) == 0`) and takes
`len = zng_first_diff_byte64(diff)`. For a non-zero `diff` that length exceeds `best_len` (`short_len_gt`): the lazy
search of the slow variants relies on it to make progress. `zng_first_bytes_mask64(n)` does not fault for
`1 ≤ n ≤ 8` (`mask_ok`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MatchBits
open C ZlibNg.Deflate ZlibNg.Compare256
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-- A loop invariant of a `for` over `List.range' s len` in `Id`. -/
theorem forIn_range_inv {σ : Type} (P : Nat → σ → Prop) (f : Nat → σ → Id (ForInStep σ)) (N : Nat)
    (hf : ∀ j r, j < N → P j r → ∃ r', f j r = .yield r' ∧ P (j + 1) r') :
    ∀ (len s : Nat) (r : σ), s + len ≤ N → P s r → P (s + len) (Id.run (forIn (List.range' s len) r f)) := by
  intro len
  induction len with
  | zero => intro s r _ h; simpa using h
  | succ len ih =>
    intro s r hN h
    obtain ⟨r', e, h'⟩ := hf s r (by omega) h
    have := ih (s + 1) r' (by omega) h'
    rw [show s + (len + 1) = s + 1 + len by omega]
    simp only [List.range'_succ, List.forIn_cons, e]
    exact this

theorem u64_shr_toNat (x : UInt64) (j : Nat) (hj : j < 64) : (x >>> j.toUInt64).toNat = x.toNat / 2 ^ j := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  congr 2
  simp [Nat.toUInt64]; omega

/-- `zng_ctz64(x)` of a non-zero `x` whose low `m` bits are zero is at least `m` (and at most 64). -/
theorem ctz64_ge (x : UInt64) (hx : x ≠ 0) (m : Nat) (hm : m ≤ 64) (hd : x.toNat % 2 ^ m = 0) :
    ∃ n : UInt32, zng_ctz64 x = pure n ∧ m ≤ n.toNat ∧ n.toNat ≤ 64 := by
  have hne : (x == 0) = false := by simpa using hx
  refine ⟨_, by simp only [zng_ctz64, hne, Bool.false_eq_true, ↓reduceIte]; rfl, ?_⟩
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have key := forIn_range_inv
    (fun j (r : UInt32 × UInt64) => r.1.toNat ≤ j ∧ (j ≤ m → r.1.toNat = j ∧ (j < m → r.2 = x >>> j.toUInt64)) ∧
      (m ≤ j → m ≤ r.1.toNat))
    (fun _ (r : UInt32 × UInt64) => if (r.2 &&& 1 == 0) = true then pure (ForInStep.yield (r.1 + 1, r.2 >>> 1))
      else pure (ForInStep.yield (r.1, r.2))) 64 ?_ [:64].size 0 ((0 : UInt32), x) (by simp) ?_
  · simp only [Nat.zero_add] at key
    have h64 : [:64].size = 64 := by simp
    rw [h64] at key
    exact ⟨key.2.2 hm, key.1⟩
  · intro j r hj64 ⟨h1, h2, h3⟩
    by_cases hjm : j < m
    · obtain ⟨e1, e2⟩ := h2 (by omega)
      have e2 := e2 hjm
      have hbit : (r.2 &&& 1 == 0) = true := by
        have : (r.2 &&& 1).toNat = 0 := by
          rw [UInt64.toNat_and, e2, u64_shr_toNat x j (by omega)]
          have : x.toNat / 2 ^ j % 2 = 0 := by
            have hp : 2 ^ m = 2 ^ (j + 1) * 2 ^ (m - (j + 1)) := by rw [← Nat.pow_add]; congr 1; omega
            have h2 : x.toNat % 2 ^ (j + 1) = 0 := by
              rw [hp] at hd; exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_right _ _)
                (Nat.dvd_of_mod_eq_zero hd))
            rw [← Nat.mod_mul_right_div_self, ← Nat.pow_succ, h2]; simp
          simp only [UInt64.toNat_one]
          rw [Nat.and_one_is_mod]; exact this
        have h0 : r.2 &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [this]; rfl)
        simp [h0]
      simp only [hbit, ↓reduceIte]
      refine ⟨_, rfl, ?_, fun _ => ⟨?_, fun hj1 => ?_⟩, fun h => ?_⟩
      · show (r.1 + 1).toNat ≤ j + 1
        rw [UInt32.toNat_add, e1]; simp; omega
      · show (r.1 + 1).toNat = j + 1
        rw [UInt32.toNat_add, e1]; simp; omega
      rotate_left
      · show m ≤ (r.1 + 1).toNat
        rw [UInt32.toNat_add, e1]; simp; omega
      · show r.2 >>> 1 = x >>> (j + 1).toUInt64
        rw [e2]
        apply UInt64.toNat_inj.mp
        rw [u64_shr_toNat _ _ (by omega), UInt64.toNat_shiftRight, u64_shr_toNat _ _ (by omega)]
        simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · split
      · refine ⟨_, rfl, ?_, fun h => by omega, fun _ => ?_⟩
        · show (r.1 + 1).toNat ≤ j + 1
          rw [UInt32.toNat_add]; simp; omega
        · show m ≤ (r.1 + 1).toNat
          rw [UInt32.toNat_add]; simp
          have := h3 (by omega); omega
      · exact ⟨_, rfl, by simp only []; omega, fun h => by omega, fun _ => h3 (by omega)⟩
  · refine ⟨by simp, fun _ => ⟨by simp, fun _ => ?_⟩, fun h => ?_⟩
    · apply UInt64.toNat_inj.mp; rw [u64_shr_toNat _ _ (by omega)]; simp
    · have : m = 0 := by omega
      subst this; simp

/-- `zng_first_bytes_mask64(n)` for `1 ≤ n ≤ 8`: the low `8 n` bits. -/
theorem mask_ok {H : Heap} (n : UInt32) (h1 : 1 ≤ n.toNat) (h8 : n.toNat ≤ 8) :
    Sat H (zng_first_bytes_mask64 n) (fun v H' => H' = H ∧ v.toNat = 2 ^ (8 * n.toNat) - 1) := by
  have hs : ((8 - n) * 8).toNat = 64 - 8 * n.toNat := by
    rw [UInt32.toNat_mul, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using h8)]
    simp; omega
  have hlt : (8 - n) * 8 < 64 := by rw [UInt32.lt_iff_toNat_lt, hs]; simp; omega
  refine ⟨_, H, by simp only [zng_first_bytes_mask64, shr64, hlt, ↓reduceIte]; rfl, rfl, ?_⟩
  rw [UInt64.toNat_shiftRight]
  have e : ((8 - n) * 8).toUInt64.toNat % 64 = 64 - 8 * n.toNat := by
    simp only [UInt32.toNat_toUInt64]; rw [hs]; omega
  rw [e]
  have : n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨ n.toNat = 4 ∨ n.toNat = 5 ∨ n.toNat = 6 ∨ n.toNat = 7 ∨
    n.toNat = 8 := by omega
  rcases this with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

/-- The short-candidate accept: a non-zero `diff` whose first `best_len + 1` bytes are zero has
`zng_first_diff_byte64(diff) > best_len` (and at most 8). -/
theorem short_len_gt {H : Heap} (diff mask : UInt64) (bl : Nat) (hb : bl + 1 ≤ 8) (hd : diff ≠ 0)
    (hm : mask.toNat = 2 ^ (8 * (bl + 1)) - 1) (hz : (diff &&& mask == 0) = true) :
    Sat H (zng_first_diff_byte64 diff) (fun v H' => H' = H ∧ bl < v.toNat ∧ v.toNat ≤ 8) := by
  have hz' : diff.toNat % 2 ^ (8 * (bl + 1)) = 0 := by
    have : (diff &&& mask).toNat = 0 := by
      have := beq_iff_eq.mp hz; rw [this]; rfl
    rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  obtain ⟨n, e, h1, h2⟩ := ctz64_ge diff hd (8 * (bl + 1)) (by omega) hz'
  refine ⟨n / 8, H, by simp [zng_first_diff_byte64, e], rfl, ?_, ?_⟩ <;> rw [UInt32.toNat_div] <;> simp <;> omega

end ZlibNgF.Proof.MatchBits
