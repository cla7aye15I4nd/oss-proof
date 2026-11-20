import ZlibNgF.Proof.«trees.c.bitlen»
import ZlibNgF.Math.BitReverse

/-!
# `gen_codes` on `SH` heaps (`ZlibNgF`)

`gen_codes` (`trees.c:382-409`) cut into its two loops (`gen_codes_eq`): `next_code[l]` is `nextCode bl_count l`
modulo `2^16` (`gc1_SH`), and every code `n ≤ max_code` with `Len ≠ 0` gets `Code = bi_reverse(next_code[Len]++, Len)`,
which is the canonical code `nextCode bl_count Len + #{m < n : Len m = Len}` reversed in `Len` bits (`gc2_SH`,
`bi_reverse_eq`, with `zng_bitreverse16` reversing all 16 bits).

`buildTreeSpec` glues `build_tree` together (`prefix_SH`, `merge_SH`, `gen_bitlen_SH`, `gen_codes_SH`) and proves
`BuildTreeSpec`: the lengths are the model's `treeLengths`, the codes `tCode`, and the net increments of `opt_len` /
`static_len` are `optAdd` / `statAdd` (the forcing loop's decrements cancel against the forced leaves' terms
`1 * (1 + 0)` and `1 * (stree[n].Len + 0)`).
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

/-! # `build_tree` -/

namespace ZlibNgF.Proof.TreesCodes
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Math.BitReverse (rev rev_succ)
open ZlibNgF.Proof.TreesBuildSpec (nextCode revBits xb tElems tMaxLen tSize)
open ZlibNgF.Math.Huff (forced forceNode forceNext scanLeaves maxCode1 posOf)
open ZlibNgF.Math.HuffSymbols (mass)
open ZlibNgF.Math.TreesLabeled
open ZlibNgF.Proof.TreesBitlen (glen LS sumF statT stp BC)
open ZlibNgF.Proof.TreesBuildSpec (BuildPre BuildPost BuildTreeSpec optAdd statAdd tLen tCode treeCode blFinal)
open ZlibNgF.Proof.TreesScan (frq pk tPut_self qPut_self)
open ZlibNgF.Proof.TreesForce (sdl optSub statSub setOnes)
open ZlibNgF.Proof.TreesBuild (buildTail prefix_SH tSize_ge elems_tSD)
open ZlibNgF.Proof.TreesMerge (merge_SH tSize_eq)
open ZlibNgF.Proof.TreesScan (chkI32_ok i32_ofInt)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Model facts for the glue -/

theorem revBits_eq : ∀ l x, revBits l x = rev l x
  | 0, _ => rfl
  | l + 1, x => by simp only [revBits, rev_succ, revBits_eq l (x / 2)]

theorem nextCode_congr (c c' : Nat → Nat) : ∀ l, (∀ j, j < l → c j = c' j) → nextCode c l = nextCode c' l
  | 0, _ => rfl
  | l + 1, h => by
    simp only [nextCode, nextCode_congr c c' l (fun j hj => h j (by omega)), h l (by omega)]

theorem forced_prefix (L : List (Nat × Nat)) (m : Nat) : (forced L m).1 = L ++ (forced L m).1.drop L.length := by
  match L with
  | [] => simp [forced]
  | [_] => simp [forced]
  | _ :: _ :: _ => simp [forced]

theorem forced_ex (L : List (Nat × Nat)) (m : Nat) : ∀ e ∈ (forced L m).1.drop L.length, e.1 = 1 ∧ e.2 ≤ 2 := by
  have h1 := ZlibNgF.Proof.TreesForce.forceNode_le m
  have h2 := ZlibNgF.Proof.TreesForce.forceNode_le (forceNext m)
  match L with
  | [] => intro e he; simp [forced] at he; rcases he with rfl | rfl <;> simp <;> omega
  | [_] => intro e he; simp [forced] at he; subst he; simp; omega
  | _ :: _ :: _ => intro e he; simp [forced] at he

theorem forced_ex_two (L : List (Nat × Nat)) (m : Nat) (h : (forced L m).1.drop L.length ≠ []) :
    (forced L m).1.length = 2 := by
  match L with
  | [] => simp [forced]
  | [_] => simp [forced]
  | _ :: _ :: _ => simp [forced] at h

theorem forced_lt (f : Nat → Nat) (n : Nat) :
    ∀ e ∈ (forced (scanLeaves f n) (maxCode1 f n)).1, e.2 < (forced (scanLeaves f n) (maxCode1 f n)).2 := by
  have hge := ZlibNgF.Math.Huff.maxCode1_ge f n
  have fn : ∀ m, forceNode m < forceNext m := fun m => by unfold forceNode forceNext; split <;> omega
  have fm : ∀ m, m ≤ forceNext m := fun m => by unfold forceNext; split <;> omega
  generalize scanLeaves f n = L at hge
  generalize maxCode1 f n = m at hge
  match L with
  | [] =>
    intro e he; simp only [forced, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    have := fn m; have := fn (forceNext m); have := fm (forceNext m)
    rcases he with h | h <;> rw [h] <;> (try simp only) <;> omega
  | [l] =>
    intro e he; simp only [forced, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
    have := hge l (by simp); have := fm m; have := fn m
    rcases he with h | h <;> rw [h] <;> (try simp only) <;> omega
  | a :: c :: r =>
    intro e he; simp only [forced] at he ⊢; have := hge e he; omega

/-- The scanned leaves add up to the `mass` of their weights. -/
theorem scan_mass (f w : Nat → Nat) : ∀ n,
    ((scanLeaves f n).map (fun e => e.1 * w e.2)).sum = mass (fun k => f k * w k) n
  | 0 => rfl
  | n + 1 => by
    simp only [scanLeaves, List.map_append, List.sum_append, mass, scan_mass f w n]
    by_cases h : f n = 0 <;> simp [h]

theorem posOf_idx : ∀ (l : List (Nat × Nat)), (l.map Prod.snd).Nodup → ∀ j, j < l.length → posOf (l[j]!).2 l = some j
  | [], _, j, hj => by simp at hj
  | x :: l, hnd, j, hj => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    cases j with
    | zero => simp [posOf]
    | succ j =>
      simp only [List.length_cons] at hj
      have hne : x.2 ≠ (l[j]!).2 := by
        intro e
        apply hnd.1
        refine ⟨l[j]!, ?_, e.symm⟩
        rw [getElem!_pos l j (by omega)]; exact List.getElem_mem (by omega)
      simp only [posOf, List.getElem!_cons_succ, hne, ↓reduceIte, posOf_idx l hnd.2 j (by omega), Option.map_some]

theorem posOf_none (v : Nat) : ∀ (l : List (Nat × Nat)), v ∉ l.map Prod.snd → posOf v l = none
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [posOf, Ne.symm h.1, ↓reduceIte, posOf_none v l h.2, Option.map_none]

theorem xb_small (t : DescSel) (k : Nat) (hk : k ≤ 2) : xb t k = 0 := by
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  cases t <;> rcases this with rfl | rfl | rfl <;> decide

theorem sum_ones' {α : Type} : ∀ l : List α, (l.map fun _ => 1).sum = l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_ones' l, List.length_cons]; omega

theorem u32_sum (l : List Nat) : (l.map Nat.toUInt32).sum = l.sum.toUInt32 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat']
    omega


/-- Every leaf gets a length `≥ 1`; with two leaves, both get 1. -/
theorem glen_facts (L : Nat) (hL : 1 ≤ L) (srt : List (Nat × Nat)) (T : NT) (E N : Nat) (hN : N = srt.length)
    (hN2 : 2 ≤ N) (hlab : T.lab = E + N - 2) (hlnd : T.labs.Nodup) (hints : T.ints.Perm (List.range' E (N - 1)))
    (hlvs : T.lvs.Perm (srt.map Prod.snd)) (hb : ∀ e ∈ srt, e.2 < E) (hNp : N ≤ 2 ^ L) :
    (∀ j, j < N → 1 ≤ glen L srt T.erase j) ∧ (N = 2 → ∀ j, j < N → glen L srt T.erase j = 1) := by
  have hlvnd : T.lvs.Nodup := (List.nodup_append.mp ((NT.labs_perm T).nodup_iff.mp hlnd)).2.1
  -- every leaf has a parent `p ∈ [E, E + N - 2]`, one level up
  have hpar : ∀ j, j < N → ∃ p, E ≤ p ∧ p ≤ E + N - 2 ∧ T.dep 0 (srt[j]!).2 = T.dep 0 p + 1 := by
    intro j hj
    have hm : srt[j]! ∈ srt := ZlibNgF.Proof.TreesBitlen.mem_of_idx' srt j (by omega)
    have hv : (srt[j]!).2 ∈ T.lvs := hlvs.mem_iff.mpr (List.mem_map_of_mem hm)
    have hvE := hb _ hm
    obtain ⟨p, hp⟩ := NT.has_parent T _ (NT.lvs_sub T hv) (by rw [hlab]; omega)
    have hpp := List.mem_range'_1.mp (hints.mem_iff.mp (NT.edge_par T hp))
    exact ⟨p, by simp only at hpp; omega, by simp only at hpp; omega, NT.dep_edge T 0 hlnd _ hp⟩
  have hdI : ∀ j, j < N → ZlibNgF.Math.Huff.depthIn T.erase (srt[j]!).2 = T.dep 0 (srt[j]!).2 := fun j hj =>
    NT.depthIn_erase T hlnd _ (hlvs.mem_iff.mpr (List.mem_map_of_mem
      (ZlibNgF.Proof.TreesBitlen.mem_of_idx' srt j (by omega))))
  constructor
  · intro j hj
    unfold glen
    split
    · rw [hdI j hj]; obtain ⟨p, _, _, hd⟩ := hpar j hj; omega
    · rename_i hov
      have hnode : ∃ n a c, T = NT.node n a c := by
        cases T with
        | leaf s w => simp [NT.ints] at hints; omega
        | node n a c => exact ⟨n, a, c, rfl⟩
      obtain ⟨n0, a0, c0, hT⟩ := hnode
      have hpos : ∀ x ∈ T.erase.leaves, 1 ≤ x.d := by rw [hT]; exact ZlibNgF.Math.TreesRank.leaves_pos _ _
      have hR0 := ZlibNgF.Math.TreesRank.init_inv L hL srt T.erase (by rw [NT.erase_syms]; exact hlvnd)
        (by rw [NT.erase_syms]; exact hlvs) hpos hov
      have hev := ZlibNgF.Math.Huff.overflow_even L T.erase
      rw [show (ZlibNgF.Math.Huff.overflowCount L T.erase + 1) / 2 = ZlibNgF.Math.Huff.overflowCount L T.erase / 2
        by omega]
      have hRF := ZlibNgF.Math.TreesRank.riter_inv L srt.length (by omega) _ _ hR0
      have h4 := (ZlibNgF.Math.Huff.lenSearch_spec (ZlibNgF.Math.Huff.repairIter L
        (ZlibNgF.Math.Huff.overflowCount L T.erase / 2) (ZlibNgF.Math.Huff.blCount L srt T.erase))
        (srt.length - j) L 0).2.2.2
      simp only [Nat.zero_add] at h4
      have h5 := h4 (by rw [hRF.tot]; omega)
      refine Nat.pos_of_ne_zero fun h0 => ?_
      unfold ZlibNgF.Math.Huff.lenOfRank at h0
      rw [h0] at h5
      simp only [ZlibNgF.Math.Huff.cumC, hRF.z] at h5
      omega
  · intro h2 j hj
    -- the root is the only internal node
    have hint : T.ints = [E] := by
      rw [h2] at hints
      simpa using hints
    have hlabE : T.lab = E := by omega
    have hdep1 : ∀ j, j < N → T.dep 0 (srt[j]!).2 = 1 := by
      intro j hj
      obtain ⟨p, h1, h2', hd⟩ := hpar j hj
      have : p = E := by omega
      rw [hd, this, ← hlabE, NT.dep_lab]
    have hov : ZlibNgF.Math.Huff.overflowCount L T.erase = 0 := by
      unfold ZlibNgF.Math.Huff.overflowCount
      rw [NT.ovf_erase L 0 T hlnd, hint, hlvs.countP_eq, List.countP_map]
      have e1 : [E].countP (fun x => decide (L < T.dep 0 x)) = 0 := by
        rw [← hlabE]; simp [NT.dep_lab]
      have e2 : srt.countP ((fun x => decide (L < T.dep 0 x)) ∘ Prod.snd) = 0 := by
        rw [List.countP_eq_zero]
        intro e he
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
        have := hdep1 k (by omega)
        rw [getElem!_pos srt k hk] at this
        simp [this]; omega
      rw [e1, e2]
    unfold glen
    rw [ite_eq_left hov, hdI j hj, hdep1 j hj]
    omega


theorem nd_eq_of_snd {l : List (Nat × Nat)} (h : (l.map Prod.snd).Nodup) {a c : Nat × Nat} (ha : a ∈ l) (hc : c ∈ l)
    (e : a.2 = c.2) : a = c := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hc with rfl | hc'
      · rfl
      · exact absurd ⟨c, hc', e.symm⟩ h.1
    · rcases List.mem_cons.mp hc with rfl | hc'
      · exact absurd ⟨a, ha', e⟩ h.1
      · exact ih h.2 ha' hc'

theorem forced_snd_le (L : List (Nat × Nat)) (m E : Nat) (hm : m ≤ E) (hE : 3 ≤ E) : (forced L m).2 ≤ E := by
  match L with
  | [] => simp only [forced, forceNext]; split <;> (try split) <;> omega
  | [_] => simp only [forced, forceNext]; split <;> omega
  | _ :: _ :: _ => simp only [forced]; omega

theorem statT_ne (t : DescSel) (ht : t ≠ .bl_desc) (e : Nat × Nat) :
    statT t e = e.1 * ((sdl t e.2).toNat + xb t e.2) := by
  cases t
  · rfl
  · rfl
  · exact absurd rfl ht

theorem statAdd_ne (t : DescSel) (ht : t ≠ .bl_desc) (F : Array Ct) :
    statAdd t F = mass (fun k => frq F k * ((sdl t k).toNat + xb t k)) (tElems t) := by
  cases t
  · rfl
  · rfl
  · exact absurd rfl ht

/-! ## The state of `buildTail` -/

section
variable (t : DescSel) (s : DeflateState) (A : Array Ct) (Lv Sc : Array UInt32) (mc : Int32) (o0 s0 : UInt32)

/-- The state when `buildTail` starts. -/
def XB : DeflateState :=
  { t.set (tPut t { s with opt_len := o0, static_len := s0 } A) { t.get s with max_code := mc } with
    pq_leaves := Lv, pq_scratch := Sc }

theorem XB_tArr : tArr t (XB t s A Lv Sc mc o0 s0) = A := by cases t <;> rfl
theorem XB_q (q : Bool) : qArr q (XB t s A Lv Sc mc o0 s0) = if q then Sc else Lv := by cases t <;> cases q <;> rfl
theorem XB_get : t.get (XB t s A Lv Sc mc o0 s0) = { t.get s with max_code := mc } := by cases t <;> rfl
theorem XB_bc : (XB t s A Lv Sc mc o0 s0).bl_count = s.bl_count := by cases t <;> rfl
theorem XB_opt : (XB t s A Lv Sc mc o0 s0).opt_len = o0 := by cases t <;> rfl
theorem XB_stat : (XB t s A Lv Sc mc o0 s0).static_len = s0 := by cases t <;> rfl
theorem XB_pql : (XB t s A Lv Sc mc o0 s0).pq_leaves = Lv := by cases t <;> rfl
theorem XB_pqs : (XB t s A Lv Sc mc o0 s0).pq_scratch = Sc := by cases t <;> rfl

theorem final_shape (qS : Bool) (Iq : Array UInt32) (A' A3 A5 : Array Ct) (blc : Array UInt16) (o sl : UInt32) :
    tPut t (LS t (tPut t (qPut (!qS) (XB t s A Lv Sc mc o0 s0) Iq) A') A3 blc o sl) A5 =
      t.set { tPut t s A5 with
        bl_count := blc
        pq_leaves := (qPut (!qS) (XB t s A Lv Sc mc o0 s0) Iq).pq_leaves
        pq_scratch := (qPut (!qS) (XB t s A Lv Sc mc o0 s0) Iq).pq_scratch
        opt_len := o
        static_len := sl } { t.get s with max_code := mc } := by
  cases t <;> cases qS <;> cases s <;> rfl

end

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

theorem buildTreeSpec_aux (t : DescSel) (s : DeflateState) (pre : BuildPre t b s) :
    Sat (SH H i z b s d) (build_tree (some b) t) (fun _ H' => ∃ s', H' = SH H i z b s' d ∧ BuildPost t s s') := by
  obtain ⟨hdyn, hstat, hF, hql, hqs, hblc, hmass⟩ := pre
  obtain ⟨hEs, hE3, hE286⟩ := tSize_ge t
  have hsz := tSize_eq t
  obtain ⟨hL, hLm1, hLm15, hE2⟩ := ZlibNgF.Proof.TreesBitlen.maxlen_tSD t
  refine prefix_SH t s hdyn hstat hF hql hqs _ ?_
  intro A Lv Sc qS nl mc hAs hAfc hAdl hnl hmc hLs hSs hsorted
  have hX : { t.set (tPut t { s with
            opt_len := optSub s.opt_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length)
            static_len := statSub t s.static_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length) } A)
            { t.get s with max_code := mc } with pq_leaves := Lv, pq_scratch := Sc } =
      XB t s A Lv Sc mc (optSub s.opt_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length))
        (statSub t s.static_len ((forced (scanLeaves (frq (tArr t s)) (tElems t))
              (maxCode1 (frq (tArr t s)) (tElems t))).1.drop (scanLeaves (frq (tArr t s)) (tElems t)).length)) := rfl
  rw [hX] at hsorted ⊢
  -- the model
  obtain ⟨hok, hfnd, hf2, hfE, hfcomp, hfsum⟩ := ZlibNgF.Math.Huff.forced_ok (elems := tElems t)
    (freq := frq (tArr t s)) hE3
  have hperm := ZlibNgF.Math.Huff.sortKeys_perm (forced (scanLeaves (frq (tArr t s)) (tElems t))
    (maxCode1 (frq (tArr t s)) (tElems t))).1
  have hpre := forced_prefix (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))
  have hexf := forced_ex (scanLeaves (frq (tArr t s)) (tElems t)) (maxCode1 (frq (tArr t s)) (tElems t))
  have hlt := forced_lt (frq (tArr t s)) (tElems t)
  generalize hsc : scanLeaves (frq (tArr t s)) (tElems t) = sc at *
  generalize hfo : forced sc (maxCode1 (frq (tArr t s)) (tElems t)) = fo at *
  generalize hsrt : ZlibNgF.Math.Huff.sortKeys fo.1 = srt at *
  generalize hex : fo.1.drop sc.length = ex at *
  generalize hE : tElems t = E at *
  generalize hFd : tArr t s = F at *
  clear hX
  generalize hXB : XB t s A Lv Sc mc (optSub s.opt_len ex) (statSub t s.static_len ex) = X at hsorted
  have hXt : tArr t X = A := by rw [← hXB, XB_tArr]
  have hXq : ∀ q, qArr q X = if q then Sc else Lv := fun q => by rw [← hXB, XB_q]
  -- facts on the sorted leaves
  have hN : srt.length = fo.1.length := hperm.length_eq
  have hsnd : (srt.map Prod.snd).Nodup := (hperm.map Prod.snd).nodup_iff.mpr hfnd
  have hmem : ∀ e, e ∈ srt ↔ e ∈ fo.1 := fun e => hperm.mem_iff
  have hsum : (srt.map Prod.fst).sum < 65536 := by
    rw [ZlibNgF.Math.Huff.perm_sum (hperm.map Prod.fst)]; omega
  have hb : ∀ e ∈ srt, e.1 < 65536 ∧ e.2 < E := fun e he => by
    have h1 : e.1 ≤ (srt.map Prod.fst).sum := ZlibNgF.Proof.TreesMerge.nat_le_sum (List.mem_map_of_mem he)
    exact ⟨by omega, (hok e ((hmem e).mp he)).1⟩
  unfold buildTail
  refine Sat.bind (Sat.mono (merge_SH (H := H) (i := i) (z := z) (b := b) (d := d) t X qS srt nl (tSD t).get.elems
    (by rw [elems_tSD, hE]) (by rw [hnl, hN]) (by omega) (by rw [hE]; omega) (by rw [hXt, hAs, hF])
    (by rw [hXq]; split <;> assumption) (by rw [hXq]; cases qS <;> simp [hLs, hSs])
    (fun p hp => hsorted p (by omega)) hsnd (by rw [hE]; exact fun e he => (hb e he).2) hsum) fun x H1 h1 => ?_)
  obtain ⟨Iq, A', q, rfl, hnd, hIqs, hA's, hA'fc, hA'o, hmq, hqn, hqed⟩ := h1
  rw [hE] at hnd hA'fc hA'o hmq hqn
  obtain ⟨q', hq', hq'n, hlab, hlnd, hints, hlvs, hed, hml⟩ := ZlibNgF.Math.TreesLabeled.final_tree srt E hsnd
    (fun e he => (hb e he).2) (by omega)
  rw [hmq] at hq'
  obtain rfl : q = q' := by simpa using hq'
  clear hq' hq'n
  obtain ⟨_, _, _, _, nd⟩ := x
  dsimp only at hnd ⊢
  have hN2 : 2 ≤ srt.length := by omega
  rw [chkI32_ok (v := nd.toInt - 1) (by omega) (by omega), pure_bind_M]
  -- `gen_bitlen`
  have hX1g : ∀ t' : DescSel, t'.get (tPut t (qPut (!qS) X Iq) A') = t'.get X := fun t' => by
    cases t <;> cases t' <;> cases qS <;> rfl
  have hXg : t.get X = { t.get s with max_code := mc } := by rw [← hXB, XB_get]
  have hfcA : ∀ e ∈ srt, ((tArr t (tPut t (qPut (!qS) X Iq) A'))[e.2]!).fc.toNat = e.1 := by
    intro e he
    have hE' := (hb e he).2
    have hlok := hok e ((hmem e).mp he)
    rw [tArr_tPut, hA'fc e.2 hE', hXt, hAfc e.2 (by omega)]
    unfold setOnes
    split
    · rename_i hin
      obtain ⟨e', he', hee⟩ := List.mem_map.mp hin
      have := (hexf e' he').1
      have he'f : e' ∈ fo.1 := by rw [hpre]; exact List.mem_append_right _ he'
      have : e' = e := by
        have h1 : e' ∈ fo.1 := he'f
        have h2 : e ∈ fo.1 := (hmem e).mp he
        exact nd_eq_of_snd hfnd h1 h2 hee
      subst this
      simp [(hexf e' he').1]
    · rename_i hnin
      rcases hlok.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]; rfl
      · exfalso; apply hnin
        have hef : e ∈ fo.1 := (hmem e).mp he
        rw [hpre] at hef
        rcases List.mem_append.mp hef with h3 | h3
        · rw [← hsc] at h3
          have := (ZlibNgF.Math.Huff.scan_mem h3).2.2; exact absurd h2 this
        · exact List.mem_map_of_mem h3
  have hnonleaf : ∀ k, k < E → k ∉ srt.map Prod.snd → frq F k = 0 := by
    intro k hk hn
    refine Classical.byContradiction fun h0 => hn ?_
    exact List.mem_map.mpr ⟨_, (hmem _).mpr (hfcomp k hk h0), rfl⟩
  have hX1t : tArr t (tPut t (qPut (!qS) X Iq) A') = A' := tArr_tPut _ _ _
  have hX1q : qArr qS (tPut t (qPut (!qS) X Iq) A') = qArr qS X := by
    rw [ZlibNgF.Proof.TreesScan.qArr_tPut, ZlibNgF.Proof.TreesSort.qArr_qPut_not]
  have hX1bc : (tPut t (qPut (!qS) X Iq) A').bl_count = s.bl_count := by
    rw [ZlibNgF.Proof.TreesBitlen.bc_tPut, ← hXB]; cases qS <;> exact XB_bc ..
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.TreesBitlen.gen_bitlen_SH (H := H) (i := i) (z := z) (b := b) (d := d) t
    (tPut t (qPut (!qS) X Iq) A') qS srt q.tree srt.length (E + srt.length - 2) nl (Int32.ofInt (nd.toInt - 1))
    (by rw [hX1g, hXg]; exact hdyn) (by rw [hX1g, hXg]; exact hstat) rfl hN2 (by rw [hE]; omega) (by rw [hE])
    (by rw [i32_ofInt _ (by omega) (by omega)]; omega) (by rw [hnl, hN]) (by rw [hX1t, hA's, hXt, hAs, hF])
    (by rw [hX1bc, hblc]) (by rw [hX1q, hXq]; split <;> assumption)
    (fun p hp => by rw [hX1q]; exact hsorted p (by omega)) (by rw [hE]; exact hb) hsnd hfcA
    (by rw [hlab, hqn]) hlnd (by rw [hE]; exact hints) hlvs hed (fun e he => by rw [hX1t]; exact hqed e he))
    fun _ H2 h2 => ?_)
  obtain ⟨A3, blc, rfl, hBC, hA3s, hA3fc, hA3o, hA3l⟩ := h2
  rw [hE] at hA3o
  generalize hLmd : tMaxLen t = Lm at *
  -- the built tree of the model
  have hbuilt : ZlibNgF.Math.Huff.buildTree E (frq F) = ⟨srt, fo.2, q.tree.erase⟩ := by
    unfold ZlibNgF.Math.Huff.buildTree
    simp only [hsc, hfo, hsrt, hml]
    rfl
  have hgf := glen_facts Lm hLm1 srt q.tree E srt.length rfl hN2 (by rw [hlab, hqn]) hlnd hints hlvs
    (fun e he => (hb e he).2) (by omega)
  have hglen_le : ∀ j, j < srt.length → glen Lm srt q.tree.erase j ≤ Lm := by
    intro j hj
    unfold glen
    split
    · omega
    · exact ZlibNgF.Math.TreesRank.lenOfRank_leL _ _ _
  -- every leaf is some `srt[j]`
  have hidx : ∀ k, k ∈ srt.map Prod.snd → ∃ j, j < srt.length ∧ (srt[j]!).2 = k := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    exact ⟨j, hj, by rw [getElem!_pos srt j hj]⟩
  -- the lengths of the model
  have htLen : ∀ k, tLen t F k = ZlibNgF.Math.Huff.genBitlen Lm ⟨srt, fo.2, q.tree.erase⟩ k := by
    intro k
    unfold tLen ZlibNgF.Math.Huff.treeLengths
    simp only [hE, hLmd, hbuilt]
  have hlenLeaf : ∀ j, j < srt.length → tLen t F (srt[j]!).2 = glen Lm srt q.tree.erase j := by
    intro j hj
    rw [htLen]
    unfold ZlibNgF.Math.Huff.genBitlen glen
    rw [posOf_idx srt hsnd j hj]
  have hlenNon : ∀ k, k ∉ srt.map Prod.snd → tLen t F k = 0 := by
    intro k hk
    rw [htLen]
    unfold ZlibNgF.Math.Huff.genBitlen
    rw [posOf_none k srt hk]
  -- non-leaves keep the entry of the forced tree
  have hA3non : ∀ k, k < E → k ∉ srt.map Prod.snd → A3[k]! = A[k]! := by
    intro k hk hn
    rw [hA3o k hk hn, hX1t, hA'o k hk hn, hXt]
  have hAnon : ∀ k, k < E → k ∉ srt.map Prod.snd → (A[k]!).dl.toNat = 0 ∧ (A[k]!).fc = (F[k]!).fc := by
    intro k hk hn
    have h0 := hnonleaf k hk hn
    have hfc0 : (F[k]!).fc = 0 := UInt16.toNat_inj.mp (by simpa [frq] using h0)
    refine ⟨by rw [hAdl k (by omega)]; simp [hk, hfc0], ?_⟩
    rw [hAfc k (by omega)]
    unfold setOnes
    split
    · rename_i hin
      exfalso; apply hn
      obtain ⟨e', he', hee⟩ := List.mem_map.mp hin
      have : e' ∈ fo.1 := by rw [hpre]; exact List.mem_append_right _ he'
      exact List.mem_map.mpr ⟨e', (hmem e').mpr this, hee⟩
    · rfl
  -- `gen_codes`
  have hMC : fo.2 ≤ E := by
    rw [← hfo]; exact forced_snd_le _ _ _ (ZlibNgF.Math.Huff.maxCode1_le _ _) hE3
  refine Sat.bind (Sat.of_eq (show blCountP (some b) _ = _ from rfl) ?_)
  have hA3sz : A3.size = 2 * E + 1 := by rw [hA3s, hX1t, hA's, hXt, hAs, hF, hsz]
  refine Sat.mono (gen_codes_SH t _ mc fo.2 hmc (by rw [ZlibNgF.Proof.TreesBitlen.tArr_LS]; omega)
    (by rw [ZlibNgF.Proof.TreesBitlen.tArr_LS]; omega) (by simp; exact hBC.1)
    (fun m hm => ?_)) fun _ H3 h3 => ?_
  · simp only [ZlibNgF.Proof.TreesBitlen.tArr_LS, lenOf]
    by_cases hm' : m ∈ srt.map Prod.snd
    · obtain ⟨j, hj, rfl⟩ := hidx m hm'
      rw [hA3l j hj]; have := hglen_le j hj; omega
    · rw [hA3non m (by omega) hm', (hAnon m (by omega) hm').1]; omega
  obtain ⟨A5, rfl, hA5s, hA5dl, hA5fc, hA5code⟩ := h3
  simp only [ZlibNgF.Proof.TreesBitlen.tArr_LS, ZlibNgF.Proof.TreesBitlen.LS_bc] at hA5s hA5dl hA5fc hA5code
  -- the lengths
  have hA3leaf : ∀ e ∈ srt, (A3[e.2]!).dl.toNat = tLen t F e.2 := by
    intro e he
    obtain ⟨j, hj, hje⟩ := hidx e.2 (List.mem_map_of_mem he)
    rw [← hje, hA3l j hj, hlenLeaf j hj]
  have hA3all : ∀ k, k < E → lenOf A3 k = tLen t F k := by
    intro k hk
    by_cases hk' : k ∈ srt.map Prod.snd
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
      exact hA3leaf e he
    · unfold lenOf; rw [hA3non k hk hk', (hAnon k hk hk').1, hlenNon k hk']
  -- `opt_len`
  have hex1 : ∀ e ∈ ex, e.1 * (tLen t F e.2 + xb t e.2) = 1 := by
    intro e he
    obtain ⟨h1, h2⟩ := hexf e he
    have hne : ex ≠ [] := List.ne_nil_of_mem he
    have h2' := forced_ex_two sc (maxCode1 (frq F) E) (by rw [hfo, hex]; exact hne)
    rw [hfo] at h2'
    have hef : e ∈ srt := (hmem e).mpr (by rw [hpre]; exact List.mem_append_right _ he)
    obtain ⟨j, hj, hje⟩ := hidx e.2 (List.mem_map_of_mem hef)
    rw [h1, ← hje, hlenLeaf j hj, hgf.2 (by omega) j hj, hje, xb_small t e.2 h2]
  have hsumF : sumF t srt A3 = ZlibNgF.Proof.TreesBuildSpec.optAdd t F + ex.length := by
    unfold sumF ZlibNgF.Proof.TreesBuildSpec.optAdd
    rw [List.map_congr_left (fun e he => by rw [hA3leaf e he]),
      ZlibNgF.Math.Huff.perm_sum (hperm.map _), hpre, List.map_append, List.sum_append, ← hsc,
      scan_mass (frq F) (fun k => tLen t F k + xb t k) E, hE,
      List.map_congr_left hex1, sum_ones']
  have hX1o : (tPut t (qPut (!qS) X Iq) A').opt_len = optSub s.opt_len ex := by
    rw [ZlibNgF.Proof.TreesBitlen.opt_tPut, ← hXB]; cases qS <;> exact XB_opt ..
  have hX1s : (tPut t (qPut (!qS) X Iq) A').static_len = statSub t s.static_len ex := by
    rw [ZlibNgF.Proof.TreesBitlen.stat_tPut, ← hXB]; cases qS <;> exact XB_stat ..
  have hopt : (tPut t (qPut (!qS) X Iq) A').opt_len + (sumF t srt A3).toUInt32 =
      s.opt_len + (ZlibNgF.Proof.TreesBuildSpec.optAdd t F).toUInt32 := by
    rw [hX1o, hsumF]
    unfold optSub
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_sub, Nat.toUInt32_eq, UInt32.toNat_ofNat']
    omega
  have hstatv : (tPut t (qPut (!qS) X Iq) A').static_len + ((srt.map (statT t)).sum).toUInt32 =
      s.static_len + (statAdd t F).toUInt32 := by
    rw [hX1s, ZlibNgF.Math.Huff.perm_sum (hperm.map _), hpre, List.map_append, List.sum_append]
    unfold statSub
    by_cases ht : t = .bl_desc
    · subst ht
      have h0 : ∀ l : List (Nat × Nat), (l.map (statT .bl_desc)).sum = 0 := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; rfl
      have h1 : ∀ l : List (Nat × Nat), (l.map (fun e => sdl .bl_desc e.2)).sum = 0 := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; rfl
      rw [h0, h0, h1, show statAdd DescSel.bl_desc F = 0 from rfl, UInt32.sub_zero]
    · rw [List.map_congr_left (fun e _ => statT_ne t ht e), List.map_congr_left (fun e _ => statT_ne t ht e),
        ← hsc, scan_mass (frq F) (fun k => (sdl t k).toNat + xb t k) E, statAdd_ne t ht, hE]
      have hexs : (ex.map (fun e => e.1 * ((sdl t e.2).toNat + xb t e.2))).sum =
          (ex.map (fun e => (sdl t e.2).toNat)).sum := by
        congr 1
        exact List.map_congr_left (fun e he => by
          rw [(hexf e he).1, xb_small t e.2 (hexf e he).2]; simp)
      have hu : (ex.map (fun e => sdl t e.2)).sum = ((ex.map (fun e => (sdl t e.2).toNat)).sum).toUInt32 := by
        rw [← u32_sum, List.map_map]
        congr 1
        exact List.map_congr_left (fun e _ => by apply UInt32.toNat_inj.mp; simp)
      rw [hexs, hu]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_sub, Nat.toUInt32_eq, UInt32.toNat_ofNat']
      omega
  rw [hopt, hstatv, ← hXB, final_shape]
  subst hFd
  refine ⟨_, rfl, ⟨A5, blc, _, _, mc, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hA5s, hA3sz, ← hsz, ← hF]
  · rw [hBC.1, hblc]
  · cases qS
    · show (XB t s A Lv Sc mc (optSub s.opt_len ex) (statSub t s.static_len ex)).pq_leaves.size = _
      rw [XB_pql, hLs, hql]
    · show Iq.size = _; rw [hIqs, hql]
  · cases qS
    · show Iq.size = _; rw [hIqs, hqs]
    · show (XB t s A Lv Sc mc (optSub s.opt_len ex) (statSub t s.static_len ex)).pq_scratch.size = _
      rw [XB_pqs, hSs, hqs]
  · rw [hE, hbuilt]; exact hmc
  · intro k hk
    rw [hE] at hk
    rw [hA5dl k]; exact hA3all k hk
  · intro k hk
    rw [hE] at hk
    by_cases hk' : k ∈ srt.map Prod.snd
    · obtain ⟨j, hj, hjk⟩ := hidx k hk'
      have hl0 : tLen t (tArr t s) k ≠ 0 := by
        rw [← hjk, hlenLeaf j hj]; have := hgf.1 j hj; omega
      simp only [hl0, ↓reduceIte]
      have hkMC : k < fo.2 := by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk'
        exact hlt e ((hmem e).mp he)
      have hl15 : tLen t (tArr t s) k ≤ 15 := by
        rw [← hjk, hlenLeaf j hj]; have := hglen_le j hj; omega
      rw [hA5code k hkMC (by rw [hA3all k hk]; exact hl0)]
      unfold tCode treeCode
      rw [revBits_eq, hA3all k hk]
      congr 2
      · refine nextCode_congr _ _ _ (fun j' hj' => ?_)
        rw [hBC.2 j' (by omega), hE, hbuilt, hLmd]
        rfl
      · unfold cntBelow
        refine List.countP_congr (fun m hm => ?_)
        have hm' : m < k := List.mem_range.mp hm
        rw [hA3all m (by omega)]
    · have hl0 : tLen t (tArr t s) k = 0 := hlenNon k hk'
      simp only [hl0, ↓reduceIte]
      rw [hA5fc k (Or.inr (by rw [hA3all k hk]; exact hl0)), hA3non k hk hk', (hAnon k hk hk').2]

end

/-- **`build_tree` meets its specification** (`BuildTreeSpec` of `Proof/trees.c.buildspec.lean`) on each descriptor. -/
theorem buildTreeSpec : BuildTreeSpec := fun t _ _ _ _ s _ pre => buildTreeSpec_aux t s pre

end ZlibNgF.Proof.TreesCodes
