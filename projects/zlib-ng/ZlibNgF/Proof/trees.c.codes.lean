import ZlibNgF.Proof.«trees.c.bitlen»
import ZlibNgF.Math.BitReverse

/-!
# `gen_codes` on `SH` heaps (`ZlibNgF`)

`gen_codes` (`trees.c:382-409`) cut into its two loops (`gen_codes_eq`): `next_code[l]` is `nextCode bl_count l`
modulo `2^16` (`gc1_SH`), and every code `n ≤ max_code` with `Len ≠ 0` gets `Code = bi_reverse(next_code[Len]++, Len)`,
which is the canonical code `nextCode bl_count Len + #{m < n : Len m = Len}` reversed in `Len` bits (`gc2_SH`,
`bi_reverse_eq`, with `zng_bitreverse16` reversing all 16 bits).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesCodes
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.TreesScan (chkI32_ok i32_ofInt aget_ok aset_ok set!_get_eq set!_get_ne)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f u32_toInt32_toInt)
open ZlibNgF.Math.BitReverse (rev rev_succ rev_lt rev_mod testBit_rev)
open ZlibNgF.Proof.TreesBuildSpec (nextCode revBits)

/-- The condition of the `next_code` loop. -/
def gc1Cond : Int32 × UInt16 × Array UInt16 → M (Bool × (Int32 × UInt16 × Array UInt16)) :=
  fun ((bits, code, nc) : Int32 × UInt16 × Array UInt16) => pure (bits <= MAX_BITS.toInt32, (bits, code, nc))

/-- The body of the `next_code` loop. -/
def gc1Body (bl_count : DHPtr) : Int32 × UInt16 × Array UInt16 → M (Int32 × UInt16 × Array UInt16) :=
  fun ((bits, code, nc) : Int32 × UInt16 × Array UInt16) => do
    let bc : UInt16 ← Ptr.index bl_count (bits - 1).toInt
    let code : UInt16 := ((code.toUInt32 + bc.toUInt32) <<< 1).toUInt16
    let nc ← lset nc bits code
    pure (bits + 1, code, nc)

/-- The condition of the code loop. -/
def gc2Cond (max_code : Int32) : Int32 × Array UInt16 → M (Bool × (Int32 × Array UInt16)) :=
  fun ((n, nc) : Int32 × Array UInt16) => pure (n <= max_code, (n, nc))

/-- The body of the code loop. -/
def gc2Body (tree : CtPtr) : Int32 × Array UInt16 → M (Int32 × Array UInt16) :=
  fun ((n, nc) : Int32 × Array UInt16) => do
    let len : Int32 := (← ctDl tree n.toInt).toUInt32.toInt32
    if len == 0 then
      return (← chkI32 (n.toInt + 1), nc)
    let v ← lget nc len
    let nc ← lset nc len (v + 1)
    ctSetFc tree n.toInt (← bi_reverse v len)
    pure (← chkI32 (n.toInt + 1), nc)

theorem gen_codes_eq (tree : CtPtr) (max_code : Int32) (bl_count : DHPtr) :
    gen_codes tree max_code bl_count = (do
      let (_, _, next_code) ← cwhile gc1Cond (gc1Body bl_count) (1, 0, Array.replicate (MAX_BITS + 1) 0)
      let _ ← cwhile (gc2Cond max_code) (gc2Body tree) (0, next_code)) := rfl

/-- A trip of the code loop after reading `tree[n].Len`. -/
def gc2Rest (tree : CtPtr) (n : Int32) (nc : Array UInt16) (x : UInt16) : M (Int32 × Array UInt16) := do
    let len : Int32 := x.toUInt32.toInt32
    if len == 0 then
      return (← chkI32 (n.toInt + 1), nc)
    let v ← lget nc len
    let nc ← lset nc len (v + 1)
    ctSetFc tree n.toInt (← bi_reverse v len)
    pure (← chkI32 (n.toInt + 1), nc)

theorem gc2Body_bind {tree : CtPtr} {n : Int32} {nc : Array UInt16} {H : Heap} {Q : Int32 × Array UInt16 → Heap → Prop}
    (h : Sat H (ctDl tree n.toInt) (fun x H' => Sat H' (gc2Rest tree n nc x) Q)) : Sat H (gc2Body tree (n, nc)) Q := by
  delta gc2Body
  exact Sat.bind h

/-! ## `bi_reverse` -/

/-- One trip of the loop of `zng_bitreverse16`. -/
def revStep (v : UInt16) (i : Nat) (r : UInt16) : UInt16 :=
  if ((v >>> i.toUInt16) &&& 1 == 1) = true then r ||| ((1 : UInt16) <<< (15 - i).toUInt16) else r

theorem ite_yield {c : Prop} [Decidable c] (a b : UInt16) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep UInt16)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem bitreverse16_unroll (v : UInt16) : zng_bitreverse16 v =
    revStep v 15 (revStep v 14 (revStep v 13 (revStep v 12 (revStep v 11 (revStep v 10 (revStep v 9
      (revStep v 8 (revStep v 7 (revStep v 6 (revStep v 5 (revStep v 4 (revStep v 3 (revStep v 2
      (revStep v 1 (revStep v 0 0))))))))))))))) := by
  unfold zng_bitreverse16
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range', List.forIn_cons,
    List.forIn_nil, ite_yield, revStep, pure_bind, Id.run_pure]

theorem revStep_testBit (v : UInt16) (i : Nat) (hi : i < 16) (r : UInt16) (j : Nat) :
    (revStep v i r).toNat.testBit j = (r.toNat.testBit j || (v.toNat.testBit i && decide (i + j = 15))) := by
  have hc : (((v >>> i.toUInt16) &&& 1 == 1) = true) ↔ v.toNat.testBit i = true := by
    have e : ((v >>> i.toUInt16) &&& 1).toNat = (v.toNat >>> i) &&& 1 := by
      rw [UInt16.toNat_and, UInt16.toNat_shiftRight]
      have : i.toUInt16.toNat % 16 = i := by
        rw [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
      rw [this]
      rfl
    have e2 : ((v >>> i.toUInt16) &&& 1 == 1) = true ↔ ((v >>> i.toUInt16) &&& 1).toNat = 1 := by
      rw [beq_iff_eq, ← UInt16.toNat_inj]
      rfl
    rw [e2, e, Nat.testBit, Nat.and_comm]
    have h1 : 1 &&& v.toNat >>> i < 2 := by
      have := Nat.and_le_left (n := 1) (m := v.toNat >>> i); omega
    constructor
    · intro h; simp [h]
    · intro h
      have : (1 &&& v.toNat >>> i) ≠ 0 := by simpa using h
      omega
  have hm : ((1 : UInt16) <<< (15 - i).toUInt16).toNat = 2 ^ (15 - i) := by
    rw [UInt16.toNat_shiftLeft]
    have : (15 - i).toUInt16.toNat % 16 = 15 - i := by
      rw [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
    rw [this]
    have : (1 : UInt16).toNat = 1 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  unfold revStep
  by_cases hb : v.toNat.testBit i = true
  · simp only [hc.2 hb, ↓reduceIte]
    rw [UInt16.toNat_or, Nat.testBit_or, hm, Nat.testBit_two_pow, hb]
    simp only [Bool.true_and]
    congr 1
    simp only [decide_eq_decide]
    omega
  · rw [ite_eq_right (fun x => hb (hc.1 x))]
    simp at hb
    simp [hb]

theorem bitreverse16_toNat (v : UInt16) : (zng_bitreverse16 v).toNat = rev 16 v.toNat := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitreverse16_unroll, testBit_rev]
  simp only [revStep_testBit v _ (by decide : (15 : Nat) < 16), revStep_testBit v _ (by decide : (14 : Nat) < 16),
    revStep_testBit v _ (by decide : (13 : Nat) < 16), revStep_testBit v _ (by decide : (12 : Nat) < 16),
    revStep_testBit v _ (by decide : (11 : Nat) < 16), revStep_testBit v _ (by decide : (10 : Nat) < 16),
    revStep_testBit v _ (by decide : (9 : Nat) < 16), revStep_testBit v _ (by decide : (8 : Nat) < 16),
    revStep_testBit v _ (by decide : (7 : Nat) < 16), revStep_testBit v _ (by decide : (6 : Nat) < 16),
    revStep_testBit v _ (by decide : (5 : Nat) < 16), revStep_testBit v _ (by decide : (4 : Nat) < 16),
    revStep_testBit v _ (by decide : (3 : Nat) < 16), revStep_testBit v _ (by decide : (2 : Nat) < 16),
    revStep_testBit v _ (by decide : (1 : Nat) < 16), revStep_testBit v _ (by decide : (0 : Nat) < 16)]
  have z : (0 : UInt16).toNat = 0 := rfl
  rw [z, Nat.zero_testBit]
  by_cases hj : j < 16
  · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
        j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · have e : ∀ i, decide (i + j = 15) = false := fun i => by simp; omega
    simp only [e, hj, Bool.and_false, Bool.or_false, decide_false, Bool.false_and]

theorem rev_split : ∀ (a b x : Nat), rev (a + b) x = rev a x * 2 ^ b + rev b (x / 2 ^ a)
  | 0, b, x => by simp
  | a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega, rev_succ, rev_succ, rev_split a b (x / 2), Nat.pow_add,
      Nat.add_mul, Nat.mul_assoc, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ a)]
    omega

theorem rev16_div (l x : Nat) (hl : l ≤ 16) : rev 16 x / 2 ^ (16 - l) = rev l x := by
  have h := rev_split l (16 - l) x
  rw [show l + (16 - l) = 16 by omega] at h
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (rev_lt _ _), Nat.zero_add]

theorem rev_mod16 (l x : Nat) (hl : l ≤ 16) : rev l (x % 2 ^ 16) = rev l x := by
  rw [← rev_mod l (x % 2 ^ 16), ← rev_mod l x]
  congr 1
  exact Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 hl)

/-- **`bi_reverse(code, len)`** for `1 ≤ len ≤ 15` reverses the low `len` bits of `code`. -/
theorem bi_reverse_eq (v : UInt16) (len : Int32) (l : Nat) (hl : len.toInt = l) (hl1 : 1 ≤ l) (hl15 : l ≤ 15)
    (H : Heap) : ∃ r : UInt16, bi_reverse v len H = .ok (r, H) ∧ r.toNat = rev l v.toNat := by
  unfold bi_reverse
  rw [chkI32_ok (v := 16 - len.toInt) (by omega) (by omega), pure_bind_M]
  have hk : (Int32.ofInt (16 - len.toInt)).toUInt32.toNat = 16 - l := by
    rw [ZlibNgF.Proof.TreesBitlen.i32_u32 _ (by rw [i32_ofInt _ (by omega) (by omega)]; omega),
      i32_ofInt _ (by omega) (by omega)]; omega
  have hlt : (Int32.ofInt (16 - len.toInt)).toUInt32 < 32 := by
    rw [UInt32.lt_iff_toNat_lt, hk]; simp; omega
  simp only [shr32, hlt, ↓reduceIte, pure_bind_M]
  refine ⟨_, rfl, ?_⟩
  rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, hk, UInt16.toNat_toUInt32, bitreverse16_toNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := 16 - l) (by omega), rev16_div l _ (by omega)]
  have := rev_lt l v.toNat
  have : 2 ^ l ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ## `next_code` -/

theorem lset_ok {α : Type} (a : Array α) (i : Int32) (k : Nat) (v : α) (hk : i.toInt = k) (h : k < a.size) :
    lset a i v = pure (a.set! k v) := by
  have : ¬ i < 0 := fun h' => by have := Int32.lt_iff_toInt_lt.mp h'; simp at this; omega
  simp only [lset, this, ↓reduceIte]
  rw [show i.toInt.toNat = k by omega]; exact aset_ok h

theorem lget_ok {α : Type} [Inhabited α] (a : Array α) (i : Int32) (k : Nat) (hk : i.toInt = k) (h : k < a.size) :
    lget a i = pure a[k]! := by
  have : ¬ i < 0 := fun h' => by have := Int32.lt_iff_toInt_lt.mp h'; simp at this; omega
  simp only [lget, this, ↓reduceIte]
  rw [show i.toInt.toNat = k by omega]; exact aget_ok h

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem bcIdx_SH (s : DeflateState) (k : Nat) (hk : k < s.bl_count.size) :
    Ptr.index (Ptr.ref (DHRef.bl_count b) 0 : DHPtr) (k : Int) (SH H i z b s d) = .ok (s.bl_count[k]!, SH H i z b s d) := by
  simp [Ptr.index, bind_app, bcadd s k hk, Ptr.load, bc_get, hk]

/-- **The `next_code` loop**: `next_code[l] = nextCode bl_count l` (modulo `2^16`) for `1 ≤ l ≤ 15`. -/
theorem gc1_SH (Y : DeflateState) (hbs : Y.bl_count.size = 16) :
    Sat (SH H i z b Y d) (cwhile gc1Cond (gc1Body (.ref (DHRef.bl_count b) 0)) (1, 0, Array.replicate (MAX_BITS + 1) 0))
      (fun r H' => H' = SH H i z b Y d ∧ r.2.2.size = 16 ∧
        ∀ l, 1 ≤ l → l ≤ 15 → (r.2.2[l]!).toNat = nextCode (fun j => (Y.bl_count[j]!).toNat) l % 2 ^ 16) := by
  refine sat_cwhile (I := fun (x : Int32 × UInt16 × Array UInt16) H' => ∃ j : Nat, H' = SH H i z b Y d ∧
      x.1.toInt = j ∧ 1 ≤ j ∧ j ≤ 16 ∧ x.2.1.toNat = nextCode (fun j => (Y.bl_count[j]!).toNat) (j - 1) % 2 ^ 16 ∧
      x.2.2.size = 16 ∧ ∀ l, 1 ≤ l → l < j → (x.2.2[l]!).toNat = nextCode (fun j => (Y.bl_count[j]!).toNat) l % 2 ^ 16)
    (μ := fun x => (17 - x.1.toInt).toNat) _ ?_ ⟨1, rfl, rfl, Nat.le_refl _, by omega, by simp [nextCode],
      by simp [MAX_BITS], fun l h1 h2 => by omega⟩ (by simp [fuel])
  rintro ⟨bits, code, nc⟩ _ ⟨j, rfl, hj, hj1, hj16, hcode, hncs, hnc⟩
  dsimp only at hj hcode hncs hnc
  simp only [gc1Cond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : j ≤ 15 := by
      have := Int32.le_iff_toInt_le.mp (show bits ≤ MAX_BITS.toInt32 by simpa using hc)
      have h15 : (MAX_BITS.toInt32).toInt = 15 := by decide
      omega
    simp only [gc1Body]
    have hb1 : (bits - 1).toInt = ((j - 1 : Nat) : Int) := by
      rw [ZlibNgF.Proof.TreesSort.i32_sub1 _ (by omega) (by omega)]; omega
    rw [hb1]
    refine Sat.bind (Sat.of_eq (bcIdx_SH Y (j - 1) (by omega)) ?_)
    rw [lset_ok nc bits j _ hj (by omega)]
    refine Sat.bind (Sat.pure (Sat.pure ⟨⟨j + 1, rfl, by rw [ZlibNgF.Proof.TreesScan.i32_add1 _ (by omega) (by omega)]; omega,
      by omega, by omega, ?_, by simp [hncs], fun l h1 h2 => ?_⟩, ?_⟩))
    · have hlt := (Y.bl_count[j - 1]!).toNat_lt
      have hct := code.toNat_lt
      rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftLeft, UInt32.toNat_add, UInt16.toNat_toUInt32,
        UInt16.toNat_toUInt32, hcode]
      simp only [Nat.add_sub_cancel]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, nextCode]
      rw [show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq, Nat.pow_one]
      omega
    · by_cases hl : l = j
      · subst hl
        rw [set!_get_eq _ _ _ (by omega)]
        have hlt := (Y.bl_count[l - 1]!).toNat_lt
        have hct := code.toNat_lt
        rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftLeft, UInt32.toNat_add, UInt16.toNat_toUInt32,
          UInt16.toNat_toUInt32, hcode]
        obtain ⟨j', rfl⟩ : ∃ j', l = j' + 1 := ⟨l - 1, by omega⟩
        simp only [Nat.add_sub_cancel, nextCode]
        rw [show (1 : UInt32).toNat % 32 = 1 from rfl, Nat.shiftLeft_eq, Nat.pow_one]
        omega
      · rw [set!_get_ne _ _ _ _ hl]; exact hnc l h1 (by omega)
    · dsimp only; rw [ZlibNgF.Proof.TreesScan.i32_add1 _ (by omega) (by omega)]; omega
  · have hc' : 16 ≤ j := by
      have h15 : (MAX_BITS.toInt32).toInt = 15 := by decide
      refine Nat.le_of_not_lt fun hh => ?_
      have : bits ≤ MAX_BITS.toInt32 := Int32.le_iff_toInt_le.mpr (by rw [h15]; omega)
      simp [this] at hc
    exact ⟨rfl, hncs, fun l h1 h2 => hnc l h1 (by omega)⟩


/-- `tree[m].Len`. -/
def lenOf (A : Array Ct) (m : Nat) : Nat := (A[m]!).dl.toNat

/-- The number of codes `m' < m` with length `l`. -/
def cntBelow (A : Array Ct) (m l : Nat) : Nat := (List.range m).countP (fun m' => decide (lenOf A m' = l))

theorem cntBelow_succ (A : Array Ct) (m l : Nat) :
    cntBelow A (m + 1) l = cntBelow A m l + if lenOf A m = l then 1 else 0 := by
  simp only [cntBelow, List.range_succ, List.countP_append, List.countP_singleton]
  by_cases h : lenOf A m = l <;> simp [h]

/-- **The code loop**: every code `m ≤ max_code` with `Len ≠ 0` gets `Code = rev(next_code[Len] + #{m' < m : Len m' =
Len m})` in `Len` bits; `Len` is unchanged, codes with `Len = 0` or beyond `max_code` keep `Code`. -/
theorem gc2_SH (t : DescSel) (Y : DeflateState) (mc : Int32) (MC : Nat) (hmc : mc.toInt + 1 = MC)
    (hMC : MC ≤ (tArr t Y).size) (hsz : (tArr t Y).size ≤ 1000) (c : Nat → Nat) (nc0 : Array UInt16)
    (hncs : nc0.size = 16) (hnc : ∀ l, 1 ≤ l → l ≤ 15 → (nc0[l]!).toNat = nextCode c l % 2 ^ 16)
    (hlen : ∀ m, m < MC → lenOf (tArr t Y) m ≤ 15) :
    Sat (SH H i z b Y d) (cwhile (gc2Cond mc) (gc2Body (.ref (tRef t b) 0)) (0, nc0))
      (fun _ H' => ∃ A', H' = SH H i z b (tPut t Y A') d ∧ A'.size = (tArr t Y).size ∧
        (∀ m : Nat, (A'[m]!).dl = ((tArr t Y)[m]!).dl) ∧
        (∀ m : Nat, (MC ≤ m ∨ lenOf (tArr t Y) m = 0) → (A'[m]!).fc = ((tArr t Y)[m]!).fc) ∧
        ∀ m, m < MC → lenOf (tArr t Y) m ≠ 0 → (A'[m]!).fc.toNat =
          rev (lenOf (tArr t Y) m) (nextCode c (lenOf (tArr t Y) m) + cntBelow (tArr t Y) m (lenOf (tArr t Y) m))) := by
  generalize hA : tArr t Y = A at *
  refine sat_cwhile (I := fun (x : Int32 × Array UInt16) H' => ∃ (k : Nat) (A' : Array Ct), x.1.toInt = k ∧ k ≤ MC ∧
      H' = SH H i z b (tPut t Y A') d ∧ A'.size = A.size ∧ (∀ m : Nat, (A'[m]!).dl = (A[m]!).dl) ∧
      (∀ m : Nat, (k ≤ m ∨ lenOf A m = 0) → (A'[m]!).fc = (A[m]!).fc) ∧
      (∀ m, m < k → lenOf A m ≠ 0 → (A'[m]!).fc.toNat = rev (lenOf A m) (nextCode c (lenOf A m) + cntBelow A m (lenOf A m))) ∧
      x.2.size = 16 ∧ ∀ l, 1 ≤ l → l ≤ 15 → (x.2[l]!).toNat = (nextCode c l + cntBelow A k l) % 2 ^ 16)
    (μ := fun x => (MC - x.1.toInt).toNat) _ ?_ ⟨0, A, rfl, by omega, by rw [← hA, ZlibNgF.Proof.TreesScan.tPut_self], rfl, fun _ => rfl,
      fun _ _ => rfl, fun m hm => by omega, hncs, fun l h1 h2 => by simp [cntBelow, hnc l h1 h2]⟩ (by simp [fuel]; omega)
  rintro ⟨n, nc⟩ _ ⟨k, A', hk, hkM, rfl, hA's, hA'dl, hA'fc, hA'set, hncs', hnc'⟩
  dsimp only at hk hncs' hnc'
  simp only [gc2Cond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : k < MC := by
      have := Int32.le_iff_toInt_le.mp (show n ≤ mc by simpa using hc); omega
    refine gc2Body_bind ?_
    rw [hk]
    refine Sat.of_eq (ctDl_T t _ k (by simp; omega)) ?_
    simp only [tArr_tPut]
    rw [hA'dl k]
    delta gc2Rest
    dsimp only
    rw [hk]
    have hlk := hlen k hc'
    have hl32 : ((A[k]!).dl.toUInt32.toInt32).toInt = lenOf A k := by
      rw [u32_toInt32_toInt _ (by simp [lenOf] at hlk ⊢; omega)]; simp [lenOf]
    by_cases h0 : lenOf A k = 0
    · have hz : ((A[k]!).dl.toUInt32.toInt32 == 0) = true := by
        have : (A[k]!).dl.toUInt32.toInt32 = 0 := Int32.toInt_inj.mp (by rw [hl32, h0]; rfl)
        simp [this]
      rw [ite_t hz, chkI32_ok (v := (k : Int) + 1) (by omega) (by omega)]
      refine Sat.bind (Sat.pure (Sat.pure ⟨⟨k + 1, A', by rw [i32_ofInt _ (by omega) (by omega)]; omega, by omega,
        rfl, hA's, hA'dl, fun m hm => hA'fc m (by omega), fun m hm hm0 => ?_, hncs', fun l h1 h2 => ?_⟩, ?_⟩))
      · by_cases hmk : m = k
        · subst hmk; exact absurd h0 hm0
        · exact hA'set m (by omega) hm0
      · rw [hnc' l h1 h2, cntBelow_succ, h0]; simp only [show ¬ (0 = l) by omega, ↓reduceIte, Nat.add_zero]
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
    · have hz : ((A[k]!).dl.toUInt32.toInt32 == 0) = false := by
        have : (A[k]!).dl.toUInt32.toInt32 ≠ 0 := fun e => h0 (by
          have : ((A[k]!).dl.toUInt32.toInt32).toInt = 0 := by rw [e]; rfl
          omega)
        simp [this]
      rw [ite_f (by simp [hz])]
      have hl1 : 1 ≤ lenOf A k := by omega
      rw [lget_ok nc _ (lenOf A k) hl32 (by omega)]
      refine Sat.bind (Sat.pure ?_)
      rw [lset_ok nc _ (lenOf A k) _ hl32 (by omega)]
      refine Sat.bind (Sat.pure ?_)
      obtain ⟨r, hr, hrv⟩ := bi_reverse_eq nc[lenOf A k]! _ (lenOf A k) hl32 hl1 hlk
        (SH H i z b (tPut t Y A') d)
      refine Sat.bind (Sat.of_eq hr ?_)
      refine Sat.bind (Sat.of_eq (ctSetFc_T t _ k (by simp; omega) _) ?_)
      simp only [tArr_tPut, tPut_tPut]
      rw [chkI32_ok (v := (k : Int) + 1) (by omega) (by omega)]
      refine Sat.bind (Sat.pure (Sat.pure ⟨⟨k + 1, _, by rw [i32_ofInt _ (by omega) (by omega)]; omega, by omega,
        rfl, by simp [hA's], fun m => ?_, fun m hm => ?_, fun m hm hm0 => ?_, by simp [hncs'], fun l h1 h2 => ?_⟩, ?_⟩))
      · by_cases hmk : m = k
        · subst hmk; rw [set!_get_eq _ _ _ (by omega)]; exact hA'dl m
        · rw [set!_get_ne _ _ _ _ hmk]; exact hA'dl m
      · have hmk : m ≠ k := by
          rintro rfl
          rcases hm with hm | hm
          · omega
          · exact h0 hm
        rw [set!_get_ne _ _ _ _ hmk]; exact hA'fc m (by omega)
      · by_cases hmk : m = k
        · subst hmk
          rw [set!_get_eq _ _ _ (by omega)]
          dsimp only
          rw [hrv, hnc' _ hl1 hlk, rev_mod16 _ _ (by omega)]
        · rw [set!_get_ne _ _ _ _ hmk]; exact hA'set m (by omega) hm0
      · dsimp only
        rw [cntBelow_succ]
        by_cases hl : l = lenOf A k
        · subst hl
          rw [set!_get_eq _ _ _ (by omega), UInt16.toNat_add, hnc' _ h1 h2]
          simp only [↓reduceIte]
          rw [show ((1 : UInt16)).toNat = 1 from rfl]
          omega
        · rw [set!_get_ne _ _ _ _ hl, hnc' l h1 h2]
          simp [show ¬ (lenOf A k = l) from fun e => hl e.symm]
      · dsimp only; rw [i32_ofInt _ (by omega) (by omega)]; omega
  · have hc' : MC ≤ k := by
      refine Nat.le_of_not_lt fun hh => ?_
      have : n ≤ mc := Int32.le_iff_toInt_le.mpr (by omega)
      simp [this] at hc
    have hkM' : k = MC := by omega
    subst hkM'
    exact ⟨A', rfl, hA's, hA'dl, hA'fc, hA'set⟩


/-- **`gen_codes`** on the tree of `t` with `max_code + 1 = MC`, from `bl_count`. -/
theorem gen_codes_SH (t : DescSel) (Y : DeflateState) (mc : Int32) (MC : Nat) (hmc : mc.toInt + 1 = MC)
    (hMC : MC ≤ (tArr t Y).size) (hsz : (tArr t Y).size ≤ 1000) (hbs : Y.bl_count.size = 16)
    (hlen : ∀ m, m < MC → lenOf (tArr t Y) m ≤ 15) :
    Sat (SH H i z b Y d) (gen_codes (.ref (tRef t b) 0) mc (.ref (DHRef.bl_count b) 0))
      (fun _ H' => ∃ A', H' = SH H i z b (tPut t Y A') d ∧ A'.size = (tArr t Y).size ∧
        (∀ m : Nat, (A'[m]!).dl = ((tArr t Y)[m]!).dl) ∧
        (∀ m : Nat, (MC ≤ m ∨ lenOf (tArr t Y) m = 0) → (A'[m]!).fc = ((tArr t Y)[m]!).fc) ∧
        ∀ m, m < MC → lenOf (tArr t Y) m ≠ 0 → (A'[m]!).fc.toNat =
          rev (lenOf (tArr t Y) m) (nextCode (fun j => (Y.bl_count[j]!).toNat) (lenOf (tArr t Y) m) +
            cntBelow (tArr t Y) m (lenOf (tArr t Y) m))) := by
  rw [gen_codes_eq]
  refine Sat.bind (Sat.mono (gc1_SH Y hbs) fun r H1 h1 => ?_)
  obtain ⟨rfl, hs, hv⟩ := h1
  obtain ⟨r1, r2, nc⟩ := r
  exact Sat.bind (Sat.mono (gc2_SH t Y mc MC hmc hMC hsz _ nc hs hv hlen) fun _ H2 h2 => Sat.pure h2)

end

end ZlibNgF.Proof.TreesCodes
