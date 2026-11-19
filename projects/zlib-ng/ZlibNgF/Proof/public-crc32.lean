import ZlibNgF.Spec.Safety.Goals
import ZlibNgF.Spec.Functional.Goals

/-!
# Proofs of `crc32.c`, `arch/generic/crc32_braid_c.c`, `crc32_braid_comb.c` and `crc32_braid_comb_p.h` (`ZlibNgF`)

Proves safety and termination of `get_crc_table`, `crc32`, `crc32_z` and the five `crc32_combine*`
entry points, the rejection values of `crc32_combine*` for a negative length, and a concrete
non-vacuity witness for the braided kernel on an unaligned buffer.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Crc32
open C ZlibNg.Crc32Tbl ZlibNg.Crc32P ZlibNg.Crc32Braid ZlibNg.Crc32CombP ZlibNg.Crc32Comb ZlibNg.Crc32
open ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNgF.Spec.Functional

/-! ## Heap-preserving runs -/

/-- `m` terminates on `h` without fault, leaves `h` unchanged, and its value satisfies `Q`. -/
private def Ok {α : Type} (h : Heap) (m : M α) (Q : α → Prop) : Prop :=
  ∃ v, C.run m h = .ok (v, h) ∧ Q v

private theorem Ok.pure {α : Type} {h : Heap} {Q : α → Prop} {v : α} (hq : Q v) :
    Ok h (Pure.pure v) Q := ⟨v, rfl, hq⟩

private theorem Ok.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {P : α → Prop} {Q : β → Prop}
    (hm : Ok h m P) (hf : ∀ v, P v → Ok h (f v) Q) : Ok h (m >>= f) Q := by
  obtain ⟨v, hv, hp⟩ := hm
  obtain ⟨w, hw, hq⟩ := hf v hp
  exact ⟨w, by rw [C.run_bind, hv]; exact hw, hq⟩

private theorem Ok.mono {α : Type} {h : Heap} {m : M α} {P Q : α → Prop}
    (hm : Ok h m P) (hpq : ∀ v, P v → Q v) : Ok h m Q := by
  obtain ⟨v, hv, hp⟩ := hm
  exact ⟨v, hv, hpq v hp⟩

/-- Loop rule with a decreasing measure: `I` is preserved by every iteration, the measure drops,
and `Q` holds of the state left by the final (false) evaluation of the condition. -/
private theorem cwhile_go_measure {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop)
    (hstep : ∀ s, I s → Ok h (cond s) (fun cs =>
      (cs.1 = true → Ok h (body cs.2) (fun s2 => I s2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2))) :
    ∀ n s, I s → μ s < n → Ok h (cwhile.go cond body n s) Q := by
  intro n
  induction n with
  | zero => intro s _ hlt; omega
  | succ n ih =>
    intro s hI hlt
    obtain ⟨⟨c, s1⟩, hc, ht, hf⟩ := hstep s hI
    cases c with
    | false =>
      refine ⟨s1, ?_, hf rfl⟩
      unfold C.run at *
      simp [cwhile.go, hc]
    | true =>
      obtain ⟨s2, hb, hI2, hμ⟩ := ht rfl
      obtain ⟨s', hgo, hq⟩ := ih s2 hI2 (by omega)
      refine ⟨s', ?_, hq⟩
      unfold C.run at *
      simp [cwhile.go, hc, hb, hgo]

private theorem cwhile_measure {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop) {s : σ}
    (hstep : ∀ s, I s → Ok h (cond s) (fun cs =>
      (cs.1 = true → Ok h (body cs.2) (fun s2 => I s2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2)))
    (hI : I s) (hμ : μ s < fuel) : Ok h (cwhile cond body s) Q :=
  cwhile_go_measure I μ Q hstep fuel s hI hμ

/-! ## `multmodp` -/

private theorem and_or_eq_zero {a x y : UInt32} (h1 : a &&& x = 0) (h2 : a &&& y = 0) :
    a &&& (x ||| y) = 0 := by
  apply UInt32.toBitVec_inj.mp
  have e1 := congrArg UInt32.toBitVec h1
  have e2 := congrArg UInt32.toBitVec h2
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or] at *
  rw [BitVec.and_or_distrib_left, e1, e2]
  rfl

/-- The single set bit `2 ^ i` of the mask `m`. -/
private def bit (i : Nat) : UInt32 := UInt32.ofNat (2 ^ i)

private theorem bit_facts : ∀ i, i < 32 →
    (bit i).toNat = 2 ^ i ∧
    (i = 0 → bit i - 1 = 0) ∧
    (0 < i → bit i >>> 1 = bit (i - 1) ∧ bit i - 1 = (bit (i - 1) - 1) ||| bit (i - 1)) := by
  decide

/-! ### A pure model of `multmodp`

`mpGo a i p b` is the value `multmodp` returns from the loop state `m = 2^i`, with `p` and `b` as given. The
loop's control flow depends on `a` only, so the model is linear (for `^^^`) in `(p, b)`. -/

private def mulx (b : UInt32) : UInt32 := if b &&& 1 != 0 then (b >>> 1) ^^^ POLY else b >>> 1

private noncomputable def mpGo (a : UInt32) : Nat → UInt32 → UInt32 → UInt32
  | 0, p, b => if a &&& bit 0 != 0 then p ^^^ b else p
  | i + 1, p, b =>
    if a &&& bit (i + 1) != 0 then
      if a &&& (bit (i + 1) - 1) == 0 then p ^^^ b else mpGo a i (p ^^^ b) (mulx b)
    else mpGo a i p (mulx b)

private theorem xor_and_one (x y : UInt32) : (x ^^^ y) &&& 1 = (x &&& 1) ^^^ (y &&& 1) := by
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;> simp

private theorem and_one_cases (x : UInt32) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have : (x &&& 1).toNat ≤ 1 := by rw [UInt32.toNat_and]; exact Nat.and_le_right
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
  · left; exact UInt32.toNat_inj.mp (by rw [h]; rfl)
  · right; exact UInt32.toNat_inj.mp (by rw [h]; rfl)

/-- Closes an equation between `^^^`-terms of `UInt32` that holds by associativity, commutativity and
`x ^^^ x = 0`. -/
macro "xor_ac" : tactic => `(tactic| (
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro _ _
  simp [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]))

private theorem xor4 (a b c d : UInt32) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  xor_ac

private theorem mulx_xor (x y : UInt32) : mulx (x ^^^ y) = mulx x ^^^ mulx y := by
  unfold mulx
  rw [xor_and_one, UInt32.shiftRight_xor]
  rcases and_one_cases x with hx | hx <;> rcases and_one_cases y with hy | hy <;> rw [hx, hy] <;>
    simp <;> xor_ac

private theorem mpGo_xor (a : UInt32) : ∀ i p1 p2 b1 b2,
    mpGo a i (p1 ^^^ p2) (b1 ^^^ b2) = mpGo a i p1 b1 ^^^ mpGo a i p2 b2 := by
  intro i
  induction i with
  | zero =>
    intro p1 p2 b1 b2
    unfold mpGo
    split
    · exact xor4 _ _ _ _
    · rfl
  | succ i ih =>
    intro p1 p2 b1 b2
    unfold mpGo
    split
    · split
      · exact xor4 _ _ _ _
      · rw [xor4, mulx_xor, ih]
    · rw [mulx_xor, ih]

/-- `multmodp(a, b)` terminates for every non-zero `a`, with the value of the pure model. -/
private theorem mpGo_break (a p b : UInt32) (i : Nat) (hbit : a &&& bit i ≠ 0) (hlow : a &&& (bit i - 1) = 0) :
    mpGo a i p b = p ^^^ b := by
  cases i with
  | zero => simp [mpGo, hbit]
  | succ i => simp [mpGo, hbit, hlow]

private theorem mpGo_shift_set (a p b : UInt32) (i : Nat) (hbit : a &&& bit (i + 1) ≠ 0)
    (hlow : a &&& (bit (i + 1) - 1) ≠ 0) :
    mpGo a (i + 1) p b = mpGo a i (p ^^^ b) (mulx b) := by
  simp [mpGo, hbit, hlow]

private theorem mpGo_shift_unset (a p b : UInt32) (i : Nat) (hbit : a &&& bit (i + 1) = 0) :
    mpGo a (i + 1) p b = mpGo a i p (mulx b) := by
  simp [mpGo, hbit]

private theorem multmodp_ok (h : Heap) (a b : UInt32) (ha : a ≠ 0) :
    Ok h (multmodp a b) (fun r => r = mpGo a 31 0 b) := by
  unfold multmodp
  refine Ok.bind (P := fun (s : UInt32 × UInt32 × UInt32 × Bool) => s.2.1 = mpGo a 31 0 b) ?_
    (fun v hv => by obtain ⟨_, _, _, _⟩ := v; exact Ok.pure hv)
  refine cwhile_measure
    (I := fun (s : UInt32 × UInt32 × UInt32 × Bool) => (s.2.2.2 = true ∧ s.2.1 = mpGo a 31 0 b) ∨
      ∃ i, i < 32 ∧ s.1 = bit i ∧ s.2.2.2 = false ∧ (a &&& (bit i - 1) ≠ 0 ∨ a &&& bit i ≠ 0) ∧
        mpGo a i s.2.1 s.2.2.1 = mpGo a 31 0 b)
    (μ := fun (s : UInt32 × UInt32 × UInt32 × Bool) => if s.2.2.2 then 0 else s.1.toNat + 1)
    (Q := fun (s : UInt32 × UInt32 × UInt32 × Bool) => s.2.1 = mpGo a 31 0 b) ?_ ?_ ?_
  · rintro ⟨m, p, b', brk⟩ hI
    cases brk with
    | true =>
      have hv : p = mpGo a 31 0 b := by
        rcases hI with ⟨_, hv⟩ | ⟨_, _, _, hf, _⟩
        · exact hv
        · cases hf
      exact ⟨(false, m, p, b', true), rfl, fun hc => absurd hc Bool.false_ne_true, fun _ => hv⟩
    | false =>
      refine ⟨(true, m, p, b', false), rfl, fun _ => ?_, fun hc => absurd hc.symm Bool.false_ne_true⟩
      rcases hI with ⟨hI, _⟩ | ⟨i, hi, hm, _, hinv, hval⟩
      · cases hI
      obtain ⟨hnat, h0, hpos⟩ := bit_facts i hi
      dsimp only at hm hval
      subst hm
      by_cases hlow : a &&& (bit i - 1) = 0
      · -- the lowest set bit of `a` is bit `i`: the loop breaks here
        have hbit : a &&& bit i ≠ 0 := by
          rcases hinv with h1 | h1
          · exact absurd hlow h1
          · exact h1
        refine ⟨(bit i, p ^^^ b', b', true), ?_, Or.inl ⟨rfl, ?_⟩, by simp⟩
        · simp [C.run, hbit, hlow]
        · rw [← hval, mpGo_break a p b' i hbit hlow]
      · -- a lower bit of `a` is set: shift the mask
        have hipos : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h1 | h1
          · exact absurd (by rw [h0 h1]; exact UInt32.and_zero) hlow
          · exact h1
        obtain ⟨hshift, hsplit⟩ := hpos hipos
        obtain ⟨hnat', _, _⟩ := bit_facts (i - 1) (by omega)
        have hinv' : a &&& (bit (i - 1) - 1) ≠ 0 ∨ a &&& bit (i - 1) ≠ 0 := by
          by_cases h1 : a &&& (bit (i - 1) - 1) = 0
          · right
            intro h2
            apply hlow
            rw [hsplit]
            exact and_or_eq_zero h1 h2
          · exact Or.inl h1
        have hμ : (bit (i - 1)).toNat + 1 < (bit i).toNat + 1 := by
          rw [hnat, hnat']
          have : 2 ^ i = 2 * 2 ^ (i - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          have : 0 < 2 ^ (i - 1) := Nat.pow_pos (by omega)
          omega
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hinv' hμ hshift hnat'
        by_cases hbit : a &&& bit (j + 1) = 0
        · refine ⟨(bit j, p, mulx b', false),
            ?_, Or.inr ⟨j, by omega, rfl, rfl, hinv', ?_⟩, by simpa using hμ⟩
          · simp [C.run, hbit, hshift, mulx]
          · rw [← hval, mpGo_shift_unset a p b' j hbit]
        · refine ⟨(bit j, p ^^^ b', mulx b', false),
            ?_, Or.inr ⟨j, by omega, rfl, rfl, hinv', ?_⟩, by simpa using hμ⟩
          · simp [C.run, hbit, hlow, hshift, mulx]
          · rw [← hval, mpGo_shift_set a p b' j hbit hlow]
  · refine Or.inr ⟨31, by omega, rfl, rfl, ?_, by simp⟩
    by_cases h1 : a &&& bit 31 = 0
    · left
      intro h2
      apply ha
      have hall : (bit 31 - 1) ||| bit 31 = 0xffffffff := by decide
      have : a &&& 0xffffffff = 0 := by
        rw [← hall]; exact and_or_eq_zero h2 h1
      rw [← this]
      exact (UInt32.and_neg_one).symm
    · exact Or.inr h1
  · show (bit 31).toNat + 1 < fuel
    decide

/-! ### Multiplication by a power of `x` is injective

`multmodp(x2n_table[k], ·)` is multiplication by `x^(2^k)` modulo the CRC polynomial, which has the inverse
`multmodp(x2nInv[k], ·)` (checked on the 32 basis vectors by `decide`; both maps are linear). So it sends a
non-zero value to a non-zero value, and `x2nmodp` never returns 0. -/

private theorem bit_toNat (n : Nat) (hn : n < 32) : (bit n).toNat = 2 ^ n := by
  unfold bit
  rw [UInt32.toNat_ofNat_of_lt' (by have := Nat.pow_lt_pow_right (a := 2) (by omega) hn; omega)]

private theorem nat_mod_succ (x n : Nat) : x % 2 ^ (n + 1) = (x % 2 ^ n) ^^^ (x &&& 2 ^ n) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : j < n
  · have : j < n + 1 := by omega
    have : n ≠ j := by omega
    simp [*]
  · by_cases hjn : j = n
    · subst hjn; simp
    · have : ¬ j < n + 1 := by omega
      have : n ≠ j := by omega
      simp [*]

private theorem nat_and_two_pow (x n : Nat) : x &&& 2 ^ n = 0 ∨ x &&& 2 ^ n = 2 ^ n := by
  by_cases ht : x.testBit n
  · right
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hj : n = j
    · subst hj; simp [ht]
    · simp [hj]
  · left
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : n = j
    · subst hj; simp [ht]
    · simp [hj]

private theorem lin_id (L : UInt32 → UInt32) (hL : ∀ x y, L (x ^^^ y) = L x ^^^ L y)
    (hb : ∀ i, i < 32 → L (bit i) = bit i) (b : UInt32) : L b = b := by
  have h0 : L 0 = 0 := by
    have := hL 0 0
    rw [UInt32.xor_self, UInt32.xor_self] at this
    exact this
  have hpart : ∀ n, n ≤ 32 → L (b &&& UInt32.ofNat (2 ^ n - 1)) = b &&& UInt32.ofNat (2 ^ n - 1) := by
    intro n
    induction n with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn
      have hlt : 2 ^ (n + 1) - 1 < 2 ^ 32 := by
        have := Nat.pow_le_pow_right (n := 2) (by omega) hn; omega
      have hlt' : 2 ^ n - 1 < 2 ^ 32 := by
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show n ≤ 32 by omega); omega
      have hsplit : b &&& UInt32.ofNat (2 ^ (n + 1) - 1) = (b &&& UInt32.ofNat (2 ^ n - 1)) ^^^ (b &&& bit n) := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_and, UInt32.toNat_xor, UInt32.toNat_and, UInt32.toNat_and, bit_toNat n (by omega),
          UInt32.toNat_ofNat_of_lt' hlt, UInt32.toNat_ofNat_of_lt' hlt', Nat.and_two_pow_sub_one_eq_mod,
          Nat.and_two_pow_sub_one_eq_mod, nat_mod_succ]
      rw [hsplit, hL, ih (by omega)]
      congr 1
      rcases nat_and_two_pow b.toNat n with hz | hz
      · have : b &&& bit n = 0 := UInt32.toNat_inj.mp (by rw [UInt32.toNat_and, bit_toNat n (by omega), hz]; rfl)
        rw [this, h0]
      · have : b &&& bit n = bit n := UInt32.toNat_inj.mp (by rw [UInt32.toNat_and, bit_toNat n (by omega), hz])
        rw [this, hb n (by omega)]
  have := hpart 32 (Nat.le_refl _)
  have hall : b &&& UInt32.ofNat (2 ^ 32 - 1) = b := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' (by decide), Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt b.toNat_lt
  rw [hall] at this
  exact this

private def x2nInv : Array UInt32 := #[
    0xdb710641, 0x6d930ac3, 0x6d3d2d4d, 0x6567cb95, 0xd7125358, 0x5b358fd3, 0x2e9bb40b, 0x12a59a49,
    0x8df9403d, 0x5139de12, 0xba340226, 0x29c45641, 0x12fbc105, 0xecd30c55, 0x3755ebd8, 0x24ee460c,
    0x23783fcf, 0x479933fc, 0xa39442a5, 0x9ea0056d, 0xf42608f6, 0x20cacf04, 0x2a0cf83d, 0xeffd8645,
    0x2a39a67d, 0x640ebd82, 0x9dfd8792, 0x277402ab, 0xad31bc4f, 0x31536354, 0x5ea35fca, 0x52b55e39
]

set_option maxRecDepth 100000 in
private theorem inv_basis : ∀ k, k < 32 → ∀ i, i < 32 →
    mpGo (x2nInv[k]!) 31 0 (mpGo (x2n_table[k]!) 31 0 (bit i)) = bit i := by
  decide

/-- `multmodp(x2n_table[k], p)` is non-zero for a non-zero `p`. -/
private theorem mpGo_x2n_ne_zero (k : Nat) (hk : k < 32) (p : UInt32) (hp : p ≠ 0) :
    mpGo (x2n_table[k]!) 31 0 p ≠ 0 := by
  intro h0
  have hlin : ∀ x y : UInt32, mpGo (x2nInv[k]!) 31 0 (mpGo (x2n_table[k]!) 31 0 (x ^^^ y)) =
      mpGo (x2nInv[k]!) 31 0 (mpGo (x2n_table[k]!) 31 0 x) ^^^
        mpGo (x2nInv[k]!) 31 0 (mpGo (x2n_table[k]!) 31 0 y) := by
    intro x y
    have e1 := mpGo_xor (x2n_table[k]!) 31 0 0 x y
    rw [UInt32.xor_self] at e1
    rw [e1]
    have e2 := mpGo_xor (x2nInv[k]!) 31 0 0 (mpGo (x2n_table[k]!) 31 0 x) (mpGo (x2n_table[k]!) 31 0 y)
    rw [UInt32.xor_self] at e2
    exact e2
  have hid := lin_id (fun p => mpGo (x2nInv[k]!) 31 0 (mpGo (x2n_table[k]!) 31 0 p)) hlin (inv_basis k hk) p
  have hz : mpGo (x2nInv[k]!) 31 0 (0 : UInt32) = 0 := by
    have e := mpGo_xor (x2nInv[k]!) 31 0 0 0 0
    rw [UInt32.xor_self, UInt32.xor_self] at e
    exact e
  rw [h0, hz] at hid
  exact hp hid.symm

/-! ## `x2nmodp` -/

private theorem u32_index_ok {h : Heap} {r : URef} {a : Array UInt32}
    (hg : Space.get h r = some a) {i : Nat} (hi : i < a.size) :
    Ok h (Ptr.index (Ptr.ref r 0) (Int.ofNat i) : M UInt32) (fun v => v = a[i]!) := by
  refine ⟨a[i], ?_, (getElem!_pos a i hi).symm⟩
  have hc : (0 : Nat) ≤ a.size ∧ 0 ≤ ((0 : Nat) : Int) + Int.ofNat i ∧
      ((0 : Nat) : Int) + Int.ofNat i ≤ (a.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hnat : (((0 : Nat) : Int) + Int.ofNat i).toNat = i := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [C.run, Ptr.index, Ptr.add, Ptr.load, bind_app, hg, hc, and_self, ↓reduceIte, hnat, hi,
    ↓reduceDIte]

private theorem x2n_table_facts :
    x2n_table.size = 32 ∧ ∀ i, i < 32 → x2n_table[i]! ≠ 0 := by
  decide

private theorem int64_shr1 (n : Int64) : (n >>> 1).toInt = n.toInt / 2 := by
  have h1 : (n >>> 1).toBitVec = n.toBitVec.sshiftRight 1 := rfl
  rw [← Int64.toInt_toBitVec, h1, BitVec.toInt_sshiftRight, Int64.toInt_toBitVec,
    Int.shiftRight_eq_div_pow]
  rfl

/-- `x2nmodp(n, k)` terminates for every non-negative `n` once `x2n_table` is initialised, and its value is
not zero. -/
private theorem x2nmodp_ok (h : Heap) (hx : h.x2nTable = x2n_table) (n : Int64) (k : UInt32)
    (hn : 0 ≤ n.toInt) : Ok h (x2nmodp n k) (fun r => r ≠ 0) := by
  unfold x2nmodp
  refine Ok.bind (P := fun (s : UInt32 × Int64 × UInt32) => s.1 ≠ 0) ?_
    (fun v hv => by obtain ⟨_, _, _⟩ := v; exact Ok.pure hv)
  refine cwhile_measure (I := fun (s : UInt32 × Int64 × UInt32) => 0 ≤ s.2.1.toInt ∧ s.1 ≠ 0)
    (μ := fun (s : UInt32 × Int64 × UInt32) => s.2.1.toInt.toNat)
    (Q := fun (s : UInt32 × Int64 × UInt32) => s.1 ≠ 0) ?_ ⟨hn, show ((1 : UInt32) <<< 31) ≠ 0 by decide⟩ ?_
  · rintro ⟨p, n, k⟩ ⟨hI, hp0⟩
    refine ⟨(n != 0, p, n, k), rfl, fun hc => ?_, fun _ => hp0⟩
    dsimp only at hc hI hp0 ⊢
    have hne : n ≠ 0 := by simpa using hc
    have hpos : 0 < n.toInt := by
      have : n.toInt ≠ 0 := fun h0 => hne (Int64.toInt_inj.mp (h0.trans Int64.toInt_zero.symm))
      omega
    have hfin : ∀ p' : UInt32, p' ≠ 0 → Ok h (pure (p', n >>> 1, k + 1) : M (UInt32 × Int64 × UInt32))
        (fun s2 => (0 ≤ s2.2.1.toInt ∧ s2.1 ≠ 0) ∧ s2.2.1.toInt.toNat < n.toInt.toNat) := by
      intro p' hp'
      refine Ok.pure ⟨⟨?_, hp'⟩, ?_⟩ <;> dsimp only <;> rw [int64_shr1] <;> omega
    by_cases hb : (n &&& 1 != 0) = true
    · simp only [hb, ↓reduceIte]
      have hidx : (k &&& 31).toNat < h.x2nTable.size := by
        rw [hx, x2n_table_facts.1, UInt32.toNat_and]
        exact Nat.lt_succ_of_le Nat.and_le_right
      have hidx' : (k &&& 31).toNat < 32 := by rw [hx, x2n_table_facts.1] at hidx; exact hidx
      refine Ok.bind (P := fun t => t = x2n_table[(k &&& 31).toNat]!) ?_
        (fun t ht => ?_)
      · refine Ok.mono (u32_index_ok (r := URef.st_x2n_table) (a := h.x2nTable) rfl hidx) ?_
        intro v hv
        rw [hv, hx]
      · have ht0 : t ≠ 0 := by rw [ht]; exact x2n_table_facts.2 _ hidx'
        refine Ok.bind (multmodp_ok h t p ht0) (fun p' hp' => hfin p' ?_)
        rw [hp', ht]
        exact mpGo_x2n_ne_zero _ hidx' p hp0
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact hfin p hp0
  · show n.toInt.toNat < fuel
    have := Int64.toInt_lt n
    unfold fuel
    omega

/-! ## Read-only buffer and table primitives -/

private theorem ptr_add_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (k : Nat) (hle : o + k ≤ data.size) :
    Ok h ((Ptr.ref r o).add (Int.ofNat k)) (fun p => p = .ref r (o + k)) := by
  refine ⟨.ref r (o + k), ?_, rfl⟩
  dsimp only [C.run, Ptr.add]
  rw [hg]
  dsimp only
  have hc : o ≤ data.size ∧ 0 ≤ (o : Int) + Int.ofNat k ∧ (o : Int) + Int.ofNat k ≤ (data.size : Int) := by
    simp only [Int.ofNat_eq_natCast]; omega
  have hnat : ((o : Int) + Int.ofNat k).toNat = o + k := by
    simp only [Int.ofNat_eq_natCast]; omega
  split
  · rw [hnat]
  · rename_i hn; exact absurd hc hn

private theorem load8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (hlt : o < data.size) : Ok h (load8 (.ref r o)) (fun _ => True) := by
  refine ⟨data[o], ?_, trivial⟩
  dsimp only [C.run, load8, Ptr.load]
  rw [hg]
  dsimp only
  split
  · rfl
  · rename_i hn; exact absurd hlt hn

private theorem index8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (i : Nat) (hlt : o + i < data.size) :
    Ok h (index8 (.ref r o) (Int.ofNat i)) (fun _ => True) := by
  unfold index8 Ptr.index
  refine Ok.bind (ptr_add_ok hg i (by omega)) ?_
  intro p hp
  subst hp
  exact load8_ok hg hlt

set_option maxRecDepth 100000 in
private theorem crc_table_size : crc_table.size = 256 := by decide

set_option maxRecDepth 100000 in
private theorem braid_table_facts :
    crc_braid_table.size = 8 ∧ ∀ k, k < 8 → (crc_braid_table[k]!).size = 256 := by
  decide

private theorem crcTab_ok {h : Heap} (hc : h.crcTable = crc_table) (i : UInt64) (hi : i.toNat < 256) :
    Ok h (crcTab i) (fun _ => True) := by
  unfold crcTab
  refine Ok.mono (u32_index_ok (r := URef.st_crc_table) (a := h.crcTable) rfl ?_) (fun _ _ => trivial)
  rw [hc, crc_table_size]
  exact hi

private theorem braidTab_ok (h : Heap) (k i : Nat) (hk : k < 8) (hi : i < 256) :
    Ok h (braidTab k i) (fun _ => True) := by
  obtain ⟨hsz, hrow⟩ := braid_table_facts
  have hk' : k < crc_braid_table.size := by rw [hsz]; exact hk
  have hrow' := hrow k hk
  rw [getElem!_pos crc_braid_table k hk'] at hrow'
  have hi' : i < (crc_braid_table[k]'hk').size := by rw [hrow']; exact hi
  unfold braidTab
  rw [Array.getElem?_eq_getElem hk']
  dsimp only
  rw [Array.getElem?_eq_getElem hi']
  exact Ok.pure trivial

private theorem and_ff_32 (x : UInt32) : (x &&& 0xff).toUInt64.toNat < 256 := by
  rw [UInt32.toNat_toUInt64, UInt32.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

private theorem and_ff_64 (x : UInt64) : (x &&& 0xff).toNat < 256 := by
  rw [UInt64.toNat_and]
  exact Nat.lt_succ_of_le Nat.and_le_right

/-! ## `CRC_DO1` .. `CRC_DO8`, `crc32_copy_small`, `crc_word` -/

private theorem index8_ok' {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (i : Int) (h0 : 0 ≤ i) (hlt : o + i.toNat < data.size) :
    Ok h (index8 (.ref r o) i) (fun _ => True) := by
  rw [show i = Int.ofNat i.toNat by rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h0]]
  exact index8_ok hg _ hlt

private theorem CRC_DO1_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i)
    (hle : o + i.toNat + 1 ≤ data.size) :
    Ok h (CRC_DO1 c (.ref r o) i) (fun _ => True) := by
  unfold CRC_DO1
  refine Ok.bind (index8_ok' hg i h0 (by omega)) (fun b _ => ?_)
  exact Ok.bind (crcTab_ok hc _ (and_ff_32 _)) (fun _ _ => Ok.pure trivial)

private theorem CRC_DO2_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i)
    (hle : o + i.toNat + 2 ≤ data.size) :
    Ok h (CRC_DO2 c (.ref r o) i) (fun _ => True) := by
  unfold CRC_DO2
  exact Ok.bind (CRC_DO1_ok hc hg c i h0 (by omega)) (fun c _ => CRC_DO1_ok hc hg c (i + 1) (by omega) (by omega))

private theorem CRC_DO4_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i)
    (hle : o + i.toNat + 4 ≤ data.size) :
    Ok h (CRC_DO4 c (.ref r o) i) (fun _ => True) := by
  unfold CRC_DO4
  exact Ok.bind (CRC_DO2_ok hc hg c i h0 (by omega)) (fun c _ => CRC_DO2_ok hc hg c (i + 2) (by omega) (by omega))

private theorem CRC_DO8_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i)
    (hle : o + i.toNat + 8 ≤ data.size) :
    Ok h (CRC_DO8 c (.ref r o) i) (fun _ => True) := by
  unfold CRC_DO8
  exact Ok.bind (CRC_DO4_ok hc hg c i h0 (by omega)) (fun c _ => CRC_DO4_ok hc hg c (i + 4) (by omega) (by omega))

private theorem u64_ge_toNat {a : UInt64} {n : Nat} (hn : n < 2 ^ 64) :
    (a ≥ UInt64.ofNat n) ↔ n ≤ a.toNat := by
  rw [GE.ge, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hn]

/-- `x != 0` as a statement about `x.toNat`. -/
private theorem ne_zero_toNat {x : UInt64} : (x != 0) = true ↔ x.toNat ≠ 0 := by
  constructor
  · intro hx h0
    have : x = 0 := UInt64.toNat_inj.mp (by rw [h0]; rfl)
    simp [this] at hx
  · intro hx
    have : x ≠ 0 := fun h0 => hx (by rw [h0]; rfl)
    simpa using this

/-- The low three bits of a length, as the three tests `len & 4`, `len & 2`, `len & 1` see them. -/
private theorem low_bits_facts : ∀ m, m < 8 →
    (m &&& 4 = 0 ∨ m &&& 4 = 4) ∧ (m &&& 2 = 0 ∨ m &&& 2 = 2) ∧ (m &&& 1 = 0 ∨ m &&& 1 = 1) ∧
    (m &&& 4) + (m &&& 2) + (m &&& 1) = m := by
  decide

private theorem and_small (x : UInt64) (k : Nat) (hk : k < 8) :
    (x &&& UInt64.ofNat k).toNat = (x.toNat % 8) &&& k := by
  rw [UInt64.toNat_and, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  have hlt : x.toNat &&& k < 2 ^ 3 := Nat.and_lt_two_pow _ (by omega)
  rw [← Nat.mod_eq_of_lt hlt, Nat.and_mod_two_pow, Nat.mod_eq_of_lt (show k < 2 ^ 3 by omega)]

/-- The three tests of `crc32_copy_small` on its remaining length `len`. -/
private theorem len_bits (len : UInt64) :
    ((len &&& 4).toNat = 0 ∨ (len &&& 4).toNat = 4) ∧ ((len &&& 2).toNat = 0 ∨ (len &&& 2).toNat = 2) ∧
    ((len &&& 1).toNat = 0 ∨ (len &&& 1).toNat = 1) ∧
    (len &&& 4).toNat + (len &&& 2).toNat + (len &&& 1).toNat ≤ len.toNat := by
  have hm := low_bits_facts (len.toNat % 8) (Nat.mod_lt _ (by omega))
  have h4 := and_small len 4 (by omega)
  have h2 := and_small len 2 (by omega)
  have h1 := and_small len 1 (by omega)
  have hmod : len.toNat % 8 ≤ len.toNat := Nat.mod_le _ _
  simp only [show (4 : UInt64) = UInt64.ofNat 4 from rfl, show (2 : UInt64) = UInt64.ofNat 2 from rfl,
    show (1 : UInt64) = UInt64.ofNat 1 from rfl]
  rw [h4, h2, h1]
  omega

/-- `crc32_copy_small(crc, NULL, buf, len, MAX_LEN, 0)` reads at most `len` bytes from `buf`. -/
private theorem crc32_copy_small_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) (o : Nat) (len : UInt64) (ML : Int32)
    (hle : o + len.toNat ≤ data.size) :
    Ok h (crc32_copy_small c .null (.ref r o) len ML 0) (fun _ => True) := by
  have hfuel : ∀ l : UInt64, l.toNat < fuel := fun l => by unfold fuel; exact l.toNat_lt
  have hz : ((0 : Int32) != 0) = false := rfl
  unfold crc32_copy_small
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  let I : SmallState → Prop := fun s => ∃ o', s.buf = .ref r o' ∧ o' + s.len.toNat ≤ data.size
  -- the three tests on the low bits, from a state satisfying `I`
  have hrest : ∀ s : SmallState, I s → Ok h (do
      if (s.len &&& 4 != 0) = true then do
        let x1 ← CRC_DO4 s.crc s.buf 0
        let x2 ← Ptr.add s.buf 4
        if (s.len &&& 2 != 0) = true then do
          let x4 ← CRC_DO2 x1 x2 0
          let x5 ← Ptr.add x2 2
          if (s.len &&& 1 != 0) = true then CRC_DO1 x4 x5 0 >>= fun x => pure x
          else pure x4
        else
          if (s.len &&& 1 != 0) = true then CRC_DO1 x1 x2 0 >>= fun x => pure x
          else pure x1
      else
        if (s.len &&& 2 != 0) = true then do
          let x4 ← CRC_DO2 s.crc s.buf 0
          let x5 ← Ptr.add s.buf 2
          if (s.len &&& 1 != 0) = true then CRC_DO1 x4 x5 0 >>= fun x => pure x
          else pure x4
        else
          if (s.len &&& 1 != 0) = true then CRC_DO1 s.crc s.buf 0 >>= fun x => pure x
          else pure s.crc : M UInt32) (fun _ => True) := by
    rintro ⟨crc, dst, buf, len⟩ ⟨o', hb, hl⟩
    dsimp only at hb hl ⊢
    subst hb
    obtain ⟨b4, b2, b1, bsum⟩ := len_bits len
    have d1 : ∀ (c' : UInt32) (o'' : Nat), o'' + 1 ≤ data.size →
        Ok h (CRC_DO1 c' (.ref r o'') 0 >>= fun x => pure x : M UInt32) (fun _ => True) :=
      fun c' o'' hh => Ok.bind (CRC_DO1_ok hc hg c' 0 (by omega) (by simpa using hh)) (fun _ _ => Ok.pure trivial)
    split
    · rename_i t4
      rw [ne_zero_toNat] at t4
      refine Ok.bind (CRC_DO4_ok hc hg _ 0 (by omega) (by simp; omega)) (fun _ _ => ?_)
      refine Ok.bind (ptr_add_ok hg 4 (by omega)) (fun p hp => ?_)
      subst hp
      split
      · rename_i t2
        rw [ne_zero_toNat] at t2
        refine Ok.bind (CRC_DO2_ok hc hg _ 0 (by omega) (by simp; omega)) (fun _ _ => ?_)
        refine Ok.bind (ptr_add_ok hg 2 (by omega)) (fun p hp => ?_)
        subst hp
        split
        · rename_i t1
          rw [ne_zero_toNat] at t1
          exact d1 _ _ (by omega)
        · exact Ok.pure trivial
      · rename_i t2
        rw [ne_zero_toNat] at t2
        split
        · rename_i t1
          rw [ne_zero_toNat] at t1
          exact d1 _ _ (by omega)
        · exact Ok.pure trivial
    · rename_i t4
      rw [ne_zero_toNat] at t4
      split
      · rename_i t2
        rw [ne_zero_toNat] at t2
        refine Ok.bind (CRC_DO2_ok hc hg _ 0 (by omega) (by simp; omega)) (fun _ _ => ?_)
        refine Ok.bind (ptr_add_ok hg 2 (by omega)) (fun p hp => ?_)
        subst hp
        split
        · rename_i t1
          rw [ne_zero_toNat] at t1
          exact d1 _ _ (by omega)
        · exact Ok.pure trivial
      · rename_i t2
        rw [ne_zero_toNat] at t2
        split
        · rename_i t1
          rw [ne_zero_toNat] at t1
          exact d1 _ _ (by omega)
        · exact Ok.pure trivial
  split
  · refine Ok.bind (P := I) ?_ hrest
    refine cwhile_measure (I := I) (μ := fun s => s.len.toNat) (Q := I) ?_ ⟨o, rfl, hle⟩ (hfuel len)
    rintro ⟨crc, dst, buf, l⟩ ⟨o', hb, hl⟩
    dsimp only at hb hl
    subst hb
    refine ⟨_, rfl, fun hcnd => ?_, fun _ => ⟨o', rfl, hl⟩⟩
    have h8 : 8 ≤ l.toNat := (u64_ge_toNat (n := 8) (by decide)).mp (by simpa using hcnd)
    dsimp only
    refine Ok.bind (CRC_DO8_ok hc hg crc 0 (by omega) (by simp; omega)) (fun _ _ => ?_)
    refine Ok.bind (ptr_add_ok hg 8 (by omega)) (fun p hp => ?_)
    subst hp
    have hsub : (l - 8).toNat = l.toNat - 8 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; exact h8)
    exact Ok.pure ⟨⟨o' + 8, rfl, by dsimp only; omega⟩, by dsimp only; omega⟩
  · exact hrest { crc := c, dst := .null, buf := .ref r o, len := len } ⟨o, rfl, hle⟩

/-- Facts about the constant-trip `for (k = …; k < 8; k++)` loops over `int`. -/
private theorem kloop_facts : ∀ j, j < 9 →
    (Int32.ofNat j < BRAID_W_I32 ↔ j < 8) ∧
    (Int32.ofNat j).toInt.toNat = j ∧
    (j < 8 → Int32.ofNat j + 1 = Int32.ofNat (j + 1)) := by
  decide

private theorem crc_word_ok {h : Heap} (hc : h.crcTable = crc_table) (d : UInt64) :
    Ok h (crc_word d) (fun _ => True) := by
  unfold crc_word
  refine Ok.bind (P := fun _ => True) ?_ (fun v _ => by obtain ⟨_, _⟩ := v; exact Ok.pure trivial)
  refine cwhile_measure (I := fun s => ∃ j, j ≤ 8 ∧ s.2 = Int32.ofNat j)
    (μ := fun s => 8 - s.2.toInt.toNat) (Q := fun _ => True) ?_ ⟨0, by omega, rfl⟩
    (by show 8 - (0 : Int32).toInt.toNat < fuel; unfold fuel; decide)
  rintro ⟨d, k⟩ ⟨j, hj, hk⟩
  dsimp only at hk
  subst hk
  obtain ⟨hlt, hnat, hsucc⟩ := kloop_facts j (by omega)
  refine ⟨_, rfl, fun hcnd => ?_, fun _ => trivial⟩
  have hj8 : j < 8 := hlt.mp (by simpa using hcnd)
  refine Ok.bind (crcTab_ok hc _ (and_ff_64 _)) (fun t _ => Ok.pure ⟨⟨j + 1, by omega, hsucc hj8⟩, ?_⟩)
  dsimp only
  rw [hsucc hj8, hnat, (kloop_facts (j + 1) (by omega)).2.1]
  omega

private theorem loadWordAt_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (w : Nat) (hle : o + 8 * w + 8 ≤ data.size) :
    Ok h (loadWordAt (.ref r o) w) (fun _ => True) := by
  unfold loadWordAt
  refine Ok.bind (index8_ok hg (8 * w) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 1) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 2) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 3) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 4) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 5) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 6) (by omega)) (fun _ _ => ?_)
  refine Ok.bind (index8_ok hg (8 * w + 7) (by omega)) (fun _ _ => ?_)
  exact Ok.pure trivial

/-- `ALIGN_DIFF(buf, 8)` is below 8 and moves `buf` to a multiple of 8. -/
private theorem align_diff_facts (h : Heap) (r : BRef) (o : Nat) :
    let a := (8 - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))) &&& (8 - 1 : UInt64)
    a.toNat < 8 ∧ (h.baseAddr r + UInt64.ofNat (o + a.toNat)).toNat % 8 = 0 := by
  intro a
  have h7 : ((8 : UInt64) - 1).toNat = 2 ^ 3 - 1 := rfl
  have hA : ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1)).toNat = (h.baseAddr r + UInt64.ofNat o).toNat % 8 := by
    rw [UInt64.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod]
  have hAlt : (h.baseAddr r + UInt64.ofNat o).toNat % 8 < 8 := Nat.mod_lt _ (by omega)
  have hsub : ((8 : UInt64) - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))).toNat =
      8 - (h.baseAddr r + UInt64.ofNat o).toNat % 8 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hA]; show _ ≤ 8; omega), hA]
    rfl
  have ha : a.toNat = (8 - (h.baseAddr r + UInt64.ofNat o).toNat % 8) % 8 := by
    show (((8 : UInt64) - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))) &&& (8 - 1)).toNat = _
    rw [UInt64.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod, hsub]
  refine ⟨by rw [ha]; exact Nat.mod_lt _ (by omega), ?_⟩
  have hb := (h.baseAddr r).toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', ha]
  rw [UInt64.toNat_add, UInt64.toNat_ofNat'] at hAlt ⊢
  simp only [Nat.reducePow] at *
  omega

set_option maxRecDepth 20000 in
/-- `crc32_braid(crc, buf, len)` reads only `buf[0 .. len)`. -/
private theorem crc32_braid_ok {h : Heap} (hc : h.crcTable = crc_table) {r : BRef} {data : Array UInt8}
    (hg : Space.get h r = some data) (c : UInt32) (o : Nat) (len : UInt64)
    (hle : o + len.toNat ≤ data.size) :
    Ok h (crc32_braid c (.ref r o) len) (fun _ => True) := by
  have hfuel : ∀ l : UInt64, l.toNat < fuel := fun l => by unfold fuel; exact l.toNat_lt
  have hlast : ∀ (c' : UInt32) (o' : Nat) (l' : UInt64), o' + l'.toNat ≤ data.size →
      Ok h (do return ~~~(← crc32_copy_small c' .null (.ref r o') l' 39 0) : M UInt32) (fun _ => True) :=
    fun c' o' l' hl => Ok.bind (crc32_copy_small_ok hc hg c' o' l' 39 hl) (fun _ _ => Ok.pure trivial)
  unfold crc32_braid
  dsimp only
  split
  · rename_i hge
    have h47 : 47 ≤ len.toNat := by
      have : BRAID_N * BRAID_W + BRAID_W - 1 = UInt64.ofNat 47 := by decide
      rw [this] at hge
      exact (u64_ge_toNat (by decide)).mp hge
    obtain ⟨had_lt, had_al⟩ := align_diff_facts h r o
    -- `ALIGN_DIFF(buf, 8)`
    refine Ok.bind (P := fun a => a = (8 - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))) &&& (8 - 1 : UInt64))
      ⟨_, rfl, rfl⟩ (fun a ha => ?_)
    subst ha
    generalize hA : ((8 - ((h.baseAddr r + UInt64.ofNat o) &&& (8 - 1))) &&& (8 - 1 : UInt64)) = A at had_lt had_al
    have hmin : ZlibNg.Zbuild.MIN A len = A := by
      unfold ZlibNg.Zbuild.MIN
      have : ¬ (A > len) := by show ¬ (len.toNat < A.toNat); omega
      simp [this]
    rw [hmin]
    -- the rest after the alignment step, from an aligned buffer position `o'`
    have hmain : ∀ (crc0 : UInt32) (o' : Nat) (l' : UInt64), o' + l'.toNat = o + len.toNat →
        40 ≤ l'.toNat → (h.baseAddr r + UInt64.ofNat o').toNat % 8 = 0 →
        Ok h (do
          let words ← (Ptr.ref r o').castAligned 8
          let st ←
            cwhile
                (fun (s : BraidState) =>
                  pure
                    (s.blks - 1 != 0,
                      { crc0 := s.crc0, crc1 := s.crc1, crc2 := s.crc2, crc3 := s.crc3, crc4 := s.crc4, words := s.words,
                        blks := s.blks - 1 }))
                (fun (s : BraidState) => do
                  let w0 ← loadWordAt s.words 0
                  let w1 ← loadWordAt s.words 1
                  let w2 ← loadWordAt s.words 2
                  let w3 ← loadWordAt s.words 3
                  let w4 ← loadWordAt s.words 4
                  let words ← Ptr.add s.words 40
                  let c0 ← braidTab 0 ((s.crc0 ^^^ w0) &&& 255).toNat
                  let c1 ← braidTab 0 ((s.crc1 ^^^ w1) &&& 255).toNat
                  let c2 ← braidTab 0 ((s.crc2 ^^^ w2) &&& 255).toNat
                  let c3 ← braidTab 0 ((s.crc3 ^^^ w3) &&& 255).toNat
                  let c4 ← braidTab 0 ((s.crc4 ^^^ w4) &&& 255).toNat
                  let __x ←
                    cwhile (fun (x : (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) × Int32) =>
                          pure (decide (x.snd < BRAID_W_I32), x.fst, x.snd))
                        (fun (x : (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) × Int32) => do
                          let t0 ←
                            braidTab x.snd.toInt.toNat ((s.crc0 ^^^ w0) >>> (x.snd.toInt.toNat * 8).toUInt64 &&& 255).toNat
                          let t1 ←
                            braidTab x.snd.toInt.toNat ((s.crc1 ^^^ w1) >>> (x.snd.toInt.toNat * 8).toUInt64 &&& 255).toNat
                          let t2 ←
                            braidTab x.snd.toInt.toNat ((s.crc2 ^^^ w2) >>> (x.snd.toInt.toNat * 8).toUInt64 &&& 255).toNat
                          let t3 ←
                            braidTab x.snd.toInt.toNat ((s.crc3 ^^^ w3) >>> (x.snd.toInt.toNat * 8).toUInt64 &&& 255).toNat
                          let t4 ←
                            braidTab x.snd.toInt.toNat ((s.crc4 ^^^ w4) >>> (x.snd.toInt.toNat * 8).toUInt64 &&& 255).toNat
                          pure
                              ((x.1.fst ^^^ t0.toUInt64, x.1.2.fst ^^^ t1.toUInt64, x.1.2.2.fst ^^^ t2.toUInt64,
                                  x.1.2.2.2.fst ^^^ t3.toUInt64, x.1.2.2.2.snd ^^^ t4.toUInt64),
                                x.snd + 1))
                        ((c0.toUInt64, c1.toUInt64, c2.toUInt64, c3.toUInt64, c4.toUInt64), 1)
                  pure
                      { crc0 := __x.1.fst, crc1 := __x.1.2.fst, crc2 := __x.1.2.2.fst, crc3 := __x.1.2.2.2.fst,
                        crc4 := __x.1.2.2.2.snd, words := words, blks := s.blks })
                { crc0 := crc0.toUInt64, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := words,
                  blks := l' / (BRAID_N * BRAID_W) }
          let lw0 ← loadWordAt st.words 0
          let lw1 ← loadWordAt st.words 1
          let lw2 ← loadWordAt st.words 2
          let lw3 ← loadWordAt st.words 3
          let lw4 ← loadWordAt st.words 4
          let comb0 ← crc_word (st.crc0 ^^^ lw0)
          let comb1 ← crc_word (st.crc1 ^^^ lw1 ^^^ comb0.toUInt64)
          let comb2 ← crc_word (st.crc2 ^^^ lw2 ^^^ comb1.toUInt64)
          let comb3 ← crc_word (st.crc3 ^^^ lw3 ^^^ comb2.toUInt64)
          let comb4 ← crc_word (st.crc4 ^^^ lw4 ^^^ comb3.toUInt64)
          let words ← Ptr.add st.words 40
          let __do_lift ← crc32_copy_small comb4 Ptr.null words (l' - l' / (BRAID_N * BRAID_W) * BRAID_N * BRAID_W) 39 0
          pure (~~~__do_lift)) (fun _ => True) := by
      intro crc0 o' l' hsum hl40 hal
      have hB : (l' / (BRAID_N * BRAID_W)).toNat = l'.toNat / 40 := by
        rw [UInt64.toNat_div]; rfl
      have hlt := l'.toNat_lt
      have hBNW : (l' / (BRAID_N * BRAID_W) * BRAID_N * BRAID_W).toNat = l'.toNat / 40 * 40 := by
        rw [UInt64.toNat_mul, UInt64.toNat_mul, hB, show BRAID_N.toNat = 5 from rfl,
          show BRAID_W.toNat = 8 from rfl]
        simp only [Nat.reducePow] at hlt ⊢
        omega
      have hrem : (l' - l' / (BRAID_N * BRAID_W) * BRAID_N * BRAID_W).toNat = l'.toNat % 40 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hBNW]; omega), hBNW]
        omega
      have hcast : C.run (Ptr.castAligned (.ref r o') 8) h = .ok (.ref r o', h) := by
        have hal' : ((h.baseAddr r).toNat + o') % 8 = 0 := by
          rw [UInt64.toNat_add, UInt64.toNat_ofNat'] at hal
          simp only [Nat.reducePow] at hal
          omega
        simp only [C.run, Ptr.castAligned, bind_app, addrOf]
        simp [hal']
      refine Ok.bind (P := fun w => w = .ref r o') ⟨_, hcast, rfl⟩ (fun words hw => ?_)
      subst hw
      let IB : BraidState → Prop := fun s => 1 ≤ s.blks.toNat ∧
        ∃ o2, s.words = .ref r o2 ∧ o2 + 40 * s.blks.toNat + l'.toNat % 40 ≤ data.size
      refine Ok.bind (P := fun st => ∃ o2, st.words = .ref r o2 ∧ o2 + 40 + l'.toNat % 40 ≤ data.size)
        ?_ ?_
      · refine cwhile_measure (I := IB) (μ := fun s => s.blks.toNat)
          (Q := fun st => ∃ o2, st.words = .ref r o2 ∧ o2 + 40 + l'.toNat % 40 ≤ data.size) ?_
          ⟨by dsimp only; rw [hB]; omega, o', rfl, by dsimp only; rw [hB]; omega⟩ (hfuel _)
        rintro st ⟨hb1, o2, hw, hsz⟩
        have hsub : (st.blks - 1).toNat = st.blks.toNat - 1 := UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le]; exact hb1)
        refine Ok.pure ⟨fun hcnd => ?_, fun hcnd => ?_⟩
        · have hb2 : 2 ≤ st.blks.toNat := by
            have : st.blks - 1 ≠ 0 := by simpa using hcnd
            have : (st.blks - 1).toNat ≠ 0 := fun h0 => this (UInt64.toNat_inj.mp (by rw [h0]; rfl))
            omega
          dsimp only
          rw [hw]
          refine Ok.bind (loadWordAt_ok hg 0 (by omega)) (fun w0 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 1 (by omega)) (fun w1 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 2 (by omega)) (fun w2 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 3 (by omega)) (fun w3 _ => ?_)
          refine Ok.bind (loadWordAt_ok hg 4 (by omega)) (fun w4 _ => ?_)
          refine Ok.bind (ptr_add_ok hg 40 (by omega)) (fun wd hwd => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (braidTab_ok h 0 _ (by omega) (and_ff_64 _)) (fun _ _ => ?_)
          refine Ok.bind (P := fun _ => True) ?_ (fun v _ => ?_)
          · refine cwhile_measure (I := fun s => ∃ j, j ≤ 8 ∧ s.2 = Int32.ofNat j)
              (μ := fun s => 8 - s.2.toInt.toNat) (Q := fun _ => True) ?_ ⟨1, by omega, rfl⟩
              (by show 8 - (1 : Int32).toInt.toNat < fuel; unfold fuel; decide)
            rintro ⟨⟨a0, a1, a2, a3, a4⟩, k⟩ ⟨j, hj, hk⟩
            dsimp only at hk
            subst hk
            obtain ⟨hltj, hnat, hsucc⟩ := kloop_facts j (by omega)
            refine ⟨_, rfl, fun hcnd => ?_, fun _ => trivial⟩
            have hj8 : j < 8 := hltj.mp (by simpa using hcnd)
            dsimp only
            rw [hnat]
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.bind (braidTab_ok h j _ hj8 (and_ff_64 _)) (fun _ _ => ?_)
            refine Ok.pure ⟨⟨j + 1, by omega, hsucc hj8⟩, ?_⟩
            dsimp only
            rw [hsucc hj8, (kloop_facts (j + 1) (by omega)).2.1]
            omega
          · obtain ⟨⟨_, _, _, _, _⟩, _⟩ := v
            subst hwd
            refine Ok.pure ⟨⟨by dsimp only; omega, o2 + 40, rfl, by dsimp only; omega⟩, by dsimp only; omega⟩
        · have hb2 : st.blks.toNat = 1 := by
            have : st.blks - 1 = 0 := by simpa using hcnd
            have : (st.blks - 1).toNat = 0 := by rw [this]; rfl
            omega
          exact ⟨o2, hw, by omega⟩
      · rintro st ⟨o2, hw, hsz⟩
        rw [hw]
        refine Ok.bind (loadWordAt_ok hg 0 (by omega)) (fun w0 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 1 (by omega)) (fun w1 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 2 (by omega)) (fun w2 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 3 (by omega)) (fun w3 _ => ?_)
        refine Ok.bind (loadWordAt_ok hg 4 (by omega)) (fun w4 _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (crc_word_ok hc _) (fun _ _ => ?_)
        refine Ok.bind (ptr_add_ok hg 40 (by omega)) (fun wd hwd => ?_)
        subst hwd
        exact hlast _ (o2 + 40) _ (by rw [hrem]; omega)
    split
    · rename_i hA0
      refine Ok.bind (crc32_copy_small_ok hc hg _ o A 7 (by omega)) (fun crc' _ => ?_)
      refine Ok.bind (ptr_add_ok hg A.toNat (by omega)) (fun p hp => ?_)
      subst hp
      have hsubA : (len - A).toNat = len.toNat - A.toNat := UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; omega)
      have hm := hmain crc' (o + A.toNat) (len - A) (by omega) (by omega) had_al
      exact hm
    · rename_i hA0
      have hA : A.toNat = 0 := by
        have : A = 0 := by simpa using hA0
        rw [this]; rfl
      rw [hA, Nat.add_zero] at had_al
      have hm := hmain (~~~c) o len rfl (by omega) had_al
      exact hm
  · exact hlast _ o len hle


/-! ## Public `get_crc_table`, `crc32`, `crc32_z` -/

theorem get_crc_table_safety : Goal.get_crc_table_safety := by
  intro h hg
  exact ⟨_, h.crcTable, rfl, rfl, rfl, rfl, by rw [hg.1]; exact crc_table_size⟩

theorem crc32_z_safety : Goal.crc32_z_safety := by
  intro h seed buf len bytes hg hb
  rcases hb with ⟨rfl, _⟩ | ⟨r, off, data, rfl, hget, hle, _⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨v, hv, _⟩ := crc32_braid_ok hg.1 hget seed.toUInt32 off len hle
    refine ⟨v.toUInt64, ?_⟩
    have hne : (Ptr.ref r off == (.null : BPtr)) = false := by simp
    unfold crc32_z
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [C.run_bind, hv]
    rfl

theorem crc32_safety : Goal.crc32_safety := by
  intro h seed buf len bytes hg hb
  rcases hb with ⟨rfl, _⟩ | ⟨r, off, data, rfl, hget, hle, _⟩
  · exact ⟨0, rfl⟩
  · obtain ⟨v, hv, _⟩ := crc32_braid_ok hg.1 hget seed.toUInt32 off len.toUInt64
      (by rw [UInt32.toNat_toUInt64]; exact hle)
    refine ⟨v.toUInt64, ?_⟩
    have hne : (Ptr.ref r off == (.null : BPtr)) = false := by simp
    unfold crc32
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [C.run_bind, hv]
    rfl

theorem crc32_nonvacuous : Goal.crc32_nonvacuous := by
  let arr : Array UInt8 := Array.replicate 128 0x41
  let h : Heap :=
    { bytes := upd Heap.empty.bytes 0 (some arr), nextBlk := 1, crcTable := crc_table,
      x2nTable := x2n_table, baseAddr := (fun _ => 3) }
  let buf : BPtr := .ref (.heap 0) 0
  let bytes : List UInt8 := (arr.toList.drop 0).take 128
  have hg : Space.get h (BRef.heap 0) = some arr := by
    simp only [Space.get, Heap.getBytes, h, upd_same]
  have harr_sz : arr.size = 128 := Array.size_replicate
  have hlen_bytes : bytes.length = 128 := by
    dsimp [bytes]
    rw [List.length_take, List.length_drop, Array.length_toList, harr_sz]
    omega
  have hbuf_ne : buf ≠ .null := by dsimp [buf]; intro hc; cases hc
  have hglob : CrcGlobals h := ⟨rfl, rfl⟩
  have hbb : BufferBytes h buf 128 bytes := Or.inr ⟨BRef.heap 0, 0, arr, rfl, hg, by omega, rfl⟩
  obtain ⟨r, hrun⟩ := crc32_z_safety h 0 buf 128 bytes hglob hbb
  exact ⟨h, buf, bytes, r, hglob, hbuf_ne, hlen_bytes, hbb, hrun⟩

/-! ## `crc32_combine*` -/

private theorem crc32_combine_op__ok (h : Heap) (crc1 crc2 op : UInt32) (hop : op ≠ 0) :
    Ok h (crc32_combine_op_ crc1 crc2 op) (fun _ => True) := by
  unfold crc32_combine_op_
  exact Ok.bind (multmodp_ok h op crc1 hop) (fun m _ => Ok.pure trivial)

private theorem crc32_combine_gen__ok (h : Heap) (hx : h.x2nTable = x2n_table) (len2 : Int64) :
    Ok h (crc32_combine_gen_ len2) (fun _ => True) := by
  unfold crc32_combine_gen_
  by_cases hneg : len2 < 0
  · simp only [hneg, ↓reduceIte]
    exact Ok.pure trivial
  · have hn : 0 ≤ len2.toInt := by
      have h1 : ¬ len2.toInt < (0 : Int64).toInt := fun h2 => hneg (Int64.lt_iff_toInt_lt.mpr h2)
      rw [Int64.toInt_zero] at h1
      omega
    simp only [hneg, ↓reduceIte]
    exact Ok.mono (x2nmodp_ok h hx len2 3 hn) (fun _ _ => trivial)

/-- A negative `len2` is rejected before any table is read. -/
private theorem crc32_combine_gen__neg (h : Heap) (len2 : Int64) (hneg : len2 < 0) :
    C.run (crc32_combine_gen_ len2) h = .ok (0, h) := by
  unfold crc32_combine_gen_
  simp only [hneg, ↓reduceIte]
  rfl

private theorem crc32_combine__ok (h : Heap) (hx : h.x2nTable = x2n_table) (crc1 crc2 : UInt32)
    (len2 : Int64) : Ok h (crc32_combine_ crc1 crc2 len2) (fun _ => True) := by
  unfold crc32_combine_
  by_cases hneg : len2 < 0
  · simp only [hneg, ↓reduceIte]
    exact Ok.pure trivial
  · have hn : 0 ≤ len2.toInt := by
      have h1 : ¬ len2.toInt < (0 : Int64).toInt := fun h2 => hneg (Int64.lt_iff_toInt_lt.mpr h2)
      rw [Int64.toInt_zero] at h1
      omega
    simp only [hneg, ↓reduceIte]
    exact Ok.bind (x2nmodp_ok h hx len2 3 hn)
      (fun op hop => Ok.bind (multmodp_ok h op crc1 hop) (fun _ _ => Ok.pure trivial))

private theorem crc32_combine__neg (h : Heap) (crc1 crc2 : UInt32) (len2 : Int64) (hneg : len2 < 0) :
    C.run (crc32_combine_ crc1 crc2 len2) h = .ok (0, h) := by
  unfold crc32_combine_
  simp only [hneg, ↓reduceIte]
  rfl

private theorem ok_toUInt64 {h : Heap} {m : M UInt32} {Q : UInt32 → Prop} (hm : Ok h m Q) :
    ∃ r, C.run (m >>= fun r => pure r.toUInt64) h = .ok (r, h) := by
  obtain ⟨v, hv, _⟩ := hm
  exact ⟨v.toUInt64, by rw [C.run_bind, hv]; rfl⟩

theorem crc32_combine_gen_safety : Goal.crc32_combine_gen_safety := by
  intro h len2 hg
  exact ok_toUInt64 (crc32_combine_gen__ok h hg.2 len2)

theorem crc32_combine_gen64_safety : Goal.crc32_combine_gen64_safety := by
  intro h len2 hg
  exact ok_toUInt64 (crc32_combine_gen__ok h hg.2 len2)

theorem crc32_combine_op_safety : Goal.crc32_combine_op_safety := by
  intro h crc1 crc2 op hop
  exact ok_toUInt64 (crc32_combine_op__ok h crc1.toUInt32 crc2.toUInt32 op.toUInt32 hop)

theorem crc32_combine_safety : Goal.crc32_combine_safety := by
  intro h crc1 crc2 len2 hg
  exact ok_toUInt64 (crc32_combine__ok h hg.2 crc1.toUInt32 crc2.toUInt32 len2)

theorem crc32_combine64_safety : Goal.crc32_combine64_safety := by
  intro h crc1 crc2 len2 hg
  exact ok_toUInt64 (crc32_combine__ok h hg.2 crc1.toUInt32 crc2.toUInt32 len2)

theorem crc32_combine_rejection_functional : Goal.crc32_combine_rejection_functional := by
  intro h crc1 crc2 len2 hneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · show C.run (crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine__neg h _ _ len2 hneg]
    rfl
  · show C.run (crc32_combine_ crc1.toUInt32 crc2.toUInt32 len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine__neg h _ _ len2 hneg]
    rfl
  · show C.run (crc32_combine_gen_ len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine_gen__neg h len2 hneg]
    rfl
  · show C.run (crc32_combine_gen_ len2 >>= fun r => pure r.toUInt64) h = _
    rw [C.run_bind, crc32_combine_gen__neg h len2 hneg]
    rfl

end ZlibNgF.Proof.Crc32
