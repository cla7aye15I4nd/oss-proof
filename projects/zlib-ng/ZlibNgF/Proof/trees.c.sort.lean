import ZlibNgF.Proof.«trees.c.force»
import ZlibNgF.Math.TreesRadix

/-!
# The sort of `build_tree`: `pq_radix_pass` on `SH` heaps (`ZlibNgF`)

`pq_radix_pass(src, dst, n, shift, count)` (`trees.c:137-144`), with `count[c + 1]` the number of entries of
`src[0 .. n)` whose digit `(v >> shift) & 0xFF` is `c`, turns `count` into the prefix sums and stores entry `j` of
`src` at `dst[krank n digit j]` (`Math/TreesRadix.lean`): a stable counting sort.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesSort
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Proof.TreesScan
open ZlibNgF.Math.TreesRadix
open ZlibNg.Inftrees (aget aset)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Copies of the loops -/

/-- The condition of the prefix-sum loop. -/
def r1Cond : Int32 × Array UInt16 → M (Bool × (Int32 × Array UInt16)) :=
  fun ((i, count) : Int32 × Array UInt16) => pure (i <= 256, (i, count))

/-- The body of the prefix-sum loop. -/
def r1Body : Int32 × Array UInt16 → M (Int32 × Array UInt16) :=
  fun ((i, count) : Int32 × Array UInt16) => do
    let a ← lget count i
    let b ← lget count (i - 1)
    let count ← lset count i (a.toUInt32 + b.toUInt32).toUInt16
    pure (i + 1, count)

/-- The condition of the placement loop. -/
def r2Cond (n : Int32) : Int32 × Array UInt16 → M (Bool × (Int32 × Array UInt16)) :=
  fun ((i, count) : Int32 × Array UInt16) => pure (i < n, (i, count))

/-- The body of the placement loop. -/
def r2Body (src dst : DWPtr) (shift : Int32) : Int32 × Array UInt16 → M (Int32 × Array UInt16) :=
  fun ((i, count) : Int32 × Array UInt16) => do
    let v ← dwGet src i.toInt
    let d := ((← shr32 v shift.toUInt32) &&& 0xFF).toNat
    let k ← aget count d
    let count ← aset count d (k + 1)
    dwSet dst k.toNat v
    pure (i + 1, count)

theorem radix_eq (src dst : DWPtr) (n shift : Int32) (count : Array UInt16) :
    pq_radix_pass src dst n shift count = (do
      let (_, count) ← cwhile r1Cond r1Body (1, count)
      let (_, count) ← cwhile (r2Cond n) (r2Body src dst shift) (0, count)
      return count) := rfl

/-! ## Local arrays -/

theorem lget_ok {α : Type} [Inhabited α] (a : Array α) (i : Int32) (k : Nat) (hk : i.toInt = k) (h : k < a.size) :
    lget a i = pure a[k]! := by
  have : ¬ i < 0 := fun c => by have := Int32.lt_iff_toInt_lt.mp c; simp at this; omega
  simp only [lget, this, ↓reduceIte, hk, Int.toNat_natCast]
  exact aget_ok h

theorem lset_ok {α : Type} (a : Array α) (i : Int32) (k : Nat) (v : α) (hk : i.toInt = k) (h : k < a.size) :
    lset a i v = pure (a.set! k v) := by
  have : ¬ i < 0 := fun c => by have := Int32.lt_iff_toInt_lt.mp c; simp at this; omega
  simp only [lset, this, ↓reduceIte, hk, Int.toNat_natCast]
  exact aset_ok h

theorem i32_sub1 (n : Int32) (h0 : -1000 ≤ n.toInt) (h1 : n.toInt ≤ 1000) : (n - 1).toInt = n.toInt - 1 := by
  rw [Int32.toInt_sub, Int32.toInt_one]; exact Int.bmod_eq_of_le (by omega) (by omega)

@[simp] theorem qArr_qPut_not (q : Bool) (s : DeflateState) (A : Array UInt32) :
    qArr q (qPut (!q) s A) = qArr q s := by cases q <;> rfl

theorem qPut_not_qPut (q : Bool) (s : DeflateState) (A B : Array UInt32) :
    qPut (!q) (qPut (!q) s A) B = qPut (!q) s B := by cases q <;> rfl

/-- The digit of entry `l` of `src` for a pass with shift `sh`. -/
def dig (src : Array UInt32) (sh : UInt32) (l : Nat) : Nat := (((src[l]!) >>> sh) &&& 0xFF).toNat

theorem dig_lt (src : Array UInt32) (sh : UInt32) (l : Nat) : dig src sh l < 256 := by
  unfold dig
  rw [UInt32.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- **`pq_radix_pass`** from queue `qs` into the other queue: entry `j < N` of the source lands at
`krank N digit j`. -/
theorem radix_SH (qs : Bool) (s : DeflateState) (n shift : Int32) (N : Nat) (hn : n.toInt = N) (hN : N ≤ 287)
    (hsh0 : 0 ≤ shift.toInt) (hsh : shift.toInt < 32)
    (hqs : (qArr qs s).size = 287) (hqd : (qArr (!qs) s).size = 287) (count : Array UInt16) (hc : count.size = 257)
    (hcv : ∀ c, c < 257 → (count[c]!).toNat =
      (List.range N).countP (fun l => decide (dig (qArr qs s) shift.toUInt32 l + 1 = c))) :
    Sat (SH H i z b s d) (pq_radix_pass (.ref (qRef qs b) 0) (.ref (qRef (!qs) b) 0) n shift count)
      (fun _ H' => ∃ D, H' = SH H i z b (qPut (!qs) s D) d ∧ D.size = 287 ∧
        ∀ j, j < N → D[krank N (dig (qArr qs s) shift.toUInt32) j]! = (qArr qs s)[j]!) := by
  generalize hg : dig (qArr qs s) shift.toUInt32 = g at hcv
  have hglt : ∀ l, g l < 256 := fun l => hg ▸ dig_lt _ _ l
  rw [radix_eq]
  -- the prefix sums
  let cum : Nat → Nat := fun c => (List.range N).countP (fun l => decide (g l < c))
  refine Sat.bind (Sat.mono (sat_cwhile (I := fun (x : Int32 × Array UInt16) H' => H' = SH H i z b s d ∧
      1 ≤ x.1.toInt ∧ x.1.toInt ≤ 257 ∧ x.2.size = 257 ∧
      ∀ c : Nat, c < 257 → (x.2[c]!).toNat = if (c : Int) < x.1.toInt then cum c else
        (List.range N).countP (fun l => decide (g l + 1 = c)))
    (μ := fun x => 257 - x.1.toInt.toNat) (fun x H' => H' = SH H i z b s d ∧ x.2.size = 257 ∧
      ∀ c : Nat, c < 257 → (x.2[c]!).toNat = cum c) ?_ ⟨rfl, by simp, by simp, hc, fun c hc' => by
      rw [hcv c hc']
      by_cases h0 : c = 0
      · subst h0; simp [cum]
      · simp only [show ¬ (c : Int) < (1 : Int32).toInt by simp; omega, ↓reduceIte]⟩ (by simp [fuel])) fun x H' h => ?_)
  · rintro ⟨k, cnt⟩ _ ⟨rfl, h1, h2, hsz, hv⟩
    dsimp only at h1 h2 hsz hv ⊢
    simp only [r1Cond]
    refine Sat.pure ⟨fun hc1 => ?_, fun hc1 => ?_⟩
    · simp only [decide_eq_true_eq] at hc1
      have hle : k.toInt ≤ 256 := by have := Int32.le_iff_toInt_le.mp hc1; simpa using this
      generalize hK : k.toInt.toNat = K
      have hkK : k.toInt = (K : Int) := by omega
      have hk1 : (k - 1).toInt = ((K - 1 : Nat) : Int) := by rw [i32_sub1 k (by omega) (by omega)]; omega
      simp only [r1Body]
      rw [lget_ok cnt k K hkK (by omega), pure_bind_M, lget_ok cnt (k - 1) (K - 1) hk1 (by omega), pure_bind_M,
        lset_ok _ k K _ hkK (by omega), pure_bind_M]
      have va := hv K (by omega)
      have vb := hv (K - 1) (by omega)
      simp only [show ¬ ((K : Nat) : Int) < k.toInt by omega, ↓reduceIte] at va
      simp only [show ((K - 1 : Nat) : Int) < k.toInt by omega, ↓reduceIte] at vb
      have hcumK : cum K = cum (K - 1) + (List.range N).countP (fun l => decide (g l + 1 = K)) := by
        simp only [cum]
        have := cnt_split g (K - 1) (List.range N)
        rw [show K - 1 + 1 = K by omega] at this
        rw [this]; congr 1
        apply List.countP_congr; intro l _; simp; omega
      have bnd : cum K ≤ N := by
        simp only [cum]; have := List.countP_le_length (p := fun l => decide (g l < K)) (l := List.range N)
        simpa using this
      refine Sat.pure ⟨⟨rfl, ?_, ?_, by simp [hsz], fun c hc' => ?_⟩, ?_⟩
      · rw [i32_add1 k (by omega) (by omega)]; omega
      · rw [i32_add1 k (by omega) (by omega)]; omega
      · rw [i32_add1 k (by omega) (by omega)]
        by_cases e : c = K
        · subst e
          rw [set!_get_eq _ _ _ (by omega)]
          simp only [show ((c : Nat) : Int) < k.toInt + 1 by omega, ↓reduceIte]
          rw [UInt32.toNat_toUInt16, UInt32.toNat_add, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32, va, vb]
          omega
        · rw [set!_get_ne _ _ _ _ e, hv c hc']
          by_cases c1 : (c : Int) < k.toInt
          · simp [c1, show (c : Int) < k.toInt + 1 by omega]
          · simp [c1, show ¬ (c : Int) < k.toInt + 1 by omega]
      · dsimp only; rw [i32_add1 k (by omega) (by omega)]; omega
    · simp only [decide_eq_false_iff_not] at hc1
      have hge : 257 ≤ k.toInt := by
        refine Int.not_lt.mp fun hh => hc1 (Int32.le_iff_toInt_le.mpr ?_); simp; omega
      exact ⟨rfl, hsz, fun c hc' => by rw [hv c hc']; simp [show (c : Int) < k.toInt by omega]⟩
  -- the placement
  obtain ⟨k0, cnt⟩ := x
  obtain ⟨rfl, hsz, hv⟩ := h
  dsimp only at hsz hv ⊢
  refine Sat.bind (Sat.mono (sat_cwhile (I := fun (x : Int32 × Array UInt16) H' => ∃ D, H' = SH H i z b (qPut (!qs) s D) d ∧
      0 ≤ x.1.toInt ∧ x.1.toInt ≤ N ∧ x.2.size = 257 ∧ D.size = 287 ∧
      (∀ c : Nat, c < 256 → (x.2[c]!).toNat = cum c + (List.range x.1.toInt.toNat).countP (fun l => decide (g l = c))) ∧
      ∀ j, j < x.1.toInt.toNat → D[krank N g j]! = (qArr qs s)[j]!)
    (μ := fun x => N - x.1.toInt.toNat) (fun _ H' => ∃ D, H' = SH H i z b (qPut (!qs) s D) d ∧ D.size = 287 ∧
        ∀ j, j < N → D[krank N g j]! = (qArr qs s)[j]!) ?_ ⟨qArr (!qs) s, by rw [qPut_self], by simp, by simp, hsz, hqd,
      fun c hc' => by rw [hv c (by omega)]; simp, fun j hj => by simp at hj⟩ (by simp [fuel]; omega))
      fun x H' h => ?_)
  · rintro ⟨k, cnt⟩ _ ⟨D, rfl, h0, h1, hsz2, hD, hcv2, hDv⟩
    dsimp only at h0 h1 hsz2 hcv2 hDv ⊢
    simp only [r2Cond]
    refine Sat.pure ⟨fun hc1 => ?_, fun hc1 => ?_⟩
    · simp only [decide_eq_true_eq] at hc1
      have hlt : k.toInt < N := by have := Int32.lt_iff_toInt_lt.mp hc1; omega
      generalize hK : k.toInt.toNat = K at hcv2 hDv
      have hkK : k.toInt = (K : Int) := by omega
      simp only [r2Body]
      rw [hkK]
      have e1 := dwGet_Q (H := H) (i := i) (z := z) (b := b) (d := d) qs (qPut (!qs) s D) K (by simp; omega)
      refine Sat.bind (Sat.of_eq e1 ?_)
      simp only [qArr_qPut_not]
      have hs32 : shift.toUInt32 < 32 := by
        rw [UInt32.lt_iff_toNat_lt, ZlibNgF.Proof.DeflatePrime.toUInt32_toNat shift hsh0]
        show shift.toInt.toNat < 32; omega
      rw [show shr32 ((qArr qs s)[K]!) shift.toUInt32 = pure ((qArr qs s)[K]! >>> shift.toUInt32) by
        simp [shr32, hs32], pure_bind_M]
      have hdK : (((qArr qs s)[K]! >>> shift.toUInt32) &&& 0xFF).toNat = g K := by rw [← hg]; rfl
      have hgK := hglt K
      rw [hdK, aget_ok (by omega), pure_bind_M, aset_ok (by omega), pure_bind_M]
      have hkr : (cnt[g K]!).toNat = krank N g K := by
        rw [hcv2 _ (hglt K), krank_split N g K (by omega)]
      have hkrN := krank_lt (n := N) g (show K < N by omega)
      have e2 := dwSet_Q (H := H) (i := i) (z := z) (b := b) (d := d) (!qs) (qPut (!qs) s D) (cnt[g K]!).toNat
        (by simp; omega) ((qArr qs s)[K]!)
      refine Sat.bind (Sat.of_eq e2 ?_)
      simp only [qArr_qPut, qPut_not_qPut]
      refine Sat.pure ⟨⟨_, rfl, ?_, ?_, by simp [hsz2], by simp [hD], fun c hc' => ?_, fun j hj => ?_⟩, ?_⟩
      · rw [i32_add1 k (by omega) (by omega)]; omega
      · rw [i32_add1 k (by omega) (by omega)]; omega
      · rw [i32_add1 k (by omega) (by omega), show (k.toInt + 1).toNat = K + 1 by omega, countP_range_succ]
        by_cases e : c = g K
        · subst e
          rw [set!_get_eq _ _ _ (by omega), UInt16.toNat_add, UInt16.toNat_one, hcv2 _ hc']
          have bnd : cum (g K) + (List.range K).countP (fun l => decide (g l = g K)) < N := by
            rw [← krank_split N g K (by omega)]; exact hkrN
          simp; omega
        · rw [set!_get_ne _ _ _ _ e, hcv2 c hc']
          simp [Ne.symm e]
      · rw [i32_add1 k (by omega) (by omega), show (k.toInt + 1).toNat = K + 1 by omega] at hj
        rw [hkr]
        by_cases e : j = K
        · subst e; rw [set!_get_eq _ _ _ (by omega)]
        · have ne : krank N g j ≠ krank N g K := fun c => e (krank_inj g (by omega) (by omega) c)
          rw [set!_get_ne _ _ _ _ ne]; exact hDv j (by omega)
      · dsimp only; rw [i32_add1 k (by omega) (by omega)]; omega
    · simp only [decide_eq_false_iff_not] at hc1
      have hge : N ≤ k.toInt := by
        refine Int.not_lt.mp fun hh => hc1 (Int32.lt_iff_toInt_lt.mpr ?_); omega
      exact ⟨D, rfl, hD, fun j hj => hDv j (by omega)⟩
  obtain ⟨D, rfl, hD, hDv⟩ := h
  exact Sat.pure ⟨D, rfl, hD, hDv⟩

end

end ZlibNgF.Proof.TreesSort
