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
open ZlibNgF.Math.Huff (sortKeys keyLt)
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

/-- The sort of the leaves: the swap of two leaves, or one or two radix passes. Returns `(sorted, internals)`. -/
def sortBlock (leaves scratch : DWPtr) (nleaves : Int32) (count_lo count_hi : Array UInt16) : M (DWPtr × DWPtr) := do
  if nleaves == 2 then
    let l0 ← dwGet leaves 0
    let l1 ← dwGet leaves 1
    if l0 > l1 then
      let t := l0
      dwSet leaves 0 l1
      dwSet leaves 1 t
      pure (leaves, scratch)
    else pure (leaves, scratch)
  else if (← aget count_hi 1).toUInt32.toInt32 == nleaves then
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    pure (scratch, leaves)
  else
    let _ ← pq_radix_pass leaves scratch nleaves PQ_NODE_BITS.toInt32 count_lo
    let _ ← pq_radix_pass scratch leaves nleaves (PQ_NODE_BITS + 8).toInt32 count_hi
    pure (leaves, scratch)

/-! ## Packed entries -/

theorem pk_toNat (e : Nat × Nat) (h1 : e.1 < 4194304) (h2 : e.2 < 1024) : (pk e).toNat = e.1 * 1024 + e.2 := by
  simp only [pk, UInt32.toNat_or, UInt32.toNat_shiftLeft]
  have a1 : e.1.toUInt32.toNat = e.1 := by simp; omega
  have a2 : e.2.toUInt32.toNat = e.2 := by simp; omega
  rw [a1, a2]
  have a3 : (10 : UInt32).toNat % 32 = 10 := rfl
  rw [a3, Nat.shiftLeft_eq]
  have : e.1 * 2 ^ 10 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt this, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (i := 10) (by simpa using h2),
    Nat.shiftLeft_eq]

theorem pk_lt_iff (a c : Nat × Nat) (ha1 : a.1 < 65536) (ha2 : a.2 < 1024) (hc1 : c.1 < 65536) (hc2 : c.2 < 1024) :
    pk a < pk c ↔ ZlibNgF.Math.Huff.keyLt a c = true := by
  rw [UInt32.lt_iff_toNat_lt, pk_toNat a (by omega) ha2, pk_toNat c (by omega) hc2, keyLt_iff]
  omega

theorem dig_lo (e : Nat × Nat) (h1 : e.1 < 65536) (h2 : e.2 < 1024) :
    ((pk e >>> (10 : Int32).toUInt32) &&& 0xFF).toNat = e.1 % 256 := by
  have : (10 : Int32).toUInt32 = 10 := rfl
  rw [this, UInt32.toNat_and, UInt32.toNat_shiftRight, pk_toNat e (by omega) h2]
  have a3 : (10 : UInt32).toNat % 32 = 10 := rfl
  rw [a3, Nat.shiftRight_eq_div_pow, show (0xFF : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem dig_hi (e : Nat × Nat) (h1 : e.1 < 65536) (h2 : e.2 < 1024) :
    ((pk e >>> (18 : Int32).toUInt32) &&& 0xFF).toNat = e.1 / 256 := by
  have : (18 : Int32).toUInt32 = 18 := rfl
  rw [this, UInt32.toNat_and, UInt32.toNat_shiftRight, pk_toNat e (by omega) h2]
  have a3 : (18 : UInt32).toNat % 32 = 18 := rfl
  rw [a3, Nat.shiftRight_eq_div_pow, show (0xFF : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- From the ranks to the sorted list. -/
theorem sorted_of_rank (Ls : List (Nat × Nat)) (inc : Ls.Pairwise (fun a b => a.2 < b.2)) (D : Array UInt32)
    (h : ∀ j, j < Ls.length → D[krank Ls.length (fun l => (Ls[l]!).1) j]! = pk Ls[j]!) :
    ∀ p, p < Ls.length → D[p]! = pk (sortKeys Ls)[p]! := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := krank_onto Ls.length (fun l => (Ls[l]!).1) p hp
  rw [h j hj, (sortKeys_at Ls inc j hj).1]

/-- The histograms of `ScanOK` as counts over indices. -/
theorem hist_idx (Ls : List (Nat × Nat)) (f : Nat → Nat) (c : Nat) :
    (Ls.filter (fun e => f e.1 + 1 == c)).length =
      (List.range Ls.length).countP (fun l => decide (f (Ls[l]!).1 + 1 = c)) := by
  rw [← List.countP_eq_length_filter, countP_idx]
  apply List.countP_congr; intro l _; simp

theorem i32_beq_iff (x : Int32) (v : Int) (y : Int32) (hy : y.toInt = v) :
    (x == y) = true ↔ x.toInt = v := by
  rw [beq_iff_eq, ← hy]
  exact ⟨fun e => by rw [e], fun e => Int32.toInt_inj.mp e⟩

theorem mem_of_idx (Ls : List (Nat × Nat)) (j : Nat) (hj : j < Ls.length) : Ls[j]! ∈ Ls := by
  rw [show Ls[j]! = Ls[j] by simp [hj]]; exact List.getElem_mem hj

theorem sortKeys_two (a c : Nat × Nat) :
    sortKeys [a, c] = if keyLt a c = true then [a, c] else [c, a] := by
  cases h : keyLt a c <;> simp [sortKeys, ZlibNgF.Math.Huff.insKey, h]

theorem krank_congr (N : Nat) (g g' : Nat → Nat) (h : ∀ l, l < N → g l = g' l) (j : Nat) (hj : j < N) :
    krank N g j = krank N g' j := by
  unfold krank
  apply List.countP_congr
  intro l hl
  simp only [kLt, h l (List.mem_range.mp hl), h j hj]

theorem toInt32_u16 (x : UInt16) : x.toUInt32.toInt32.toInt = x.toNat := by
  have := x.toNat_lt
  have e : x.toUInt32 = UInt32.ofNat x.toNat := by apply UInt32.toNat_inj.mp; simp
  rw [e, UInt32.toInt32_ofNat', Int32.toInt_ofNat_of_lt (by omega)]

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- **The sort of `build_tree`** (`nleaves ≥ 2` leaves `Ls` in `pq_leaves`): the result pointer `sorted` holds the
packed `sortKeys Ls`, `internals` is the other queue. With three leaves or more, the leaves are those of the scan
(nodes in increasing order, the histograms of `ScanOK`). -/
theorem sort_SH (s : DeflateState) (Ls : List (Nat × Nat)) (nl : Int32) (clo chi : Array UInt16)
    (hql : s.pq_leaves.size = 287) (hqs : s.pq_scratch.size = 287)
    (hLv : ∀ j, j < Ls.length → s.pq_leaves[j]! = pk Ls[j]!)
    (hnl : nl.toInt = Ls.length) (h2 : 2 ≤ Ls.length) (h286 : Ls.length ≤ 286)
    (hb : ∀ e ∈ Ls, e.1 < 65536 ∧ e.2 < 1024) (hd : Ls.Pairwise (fun a c => a.2 ≠ c.2))
    (h3 : 3 ≤ Ls.length → Ls.Pairwise (fun a c => a.2 < c.2) ∧ clo.size = 257 ∧ chi.size = 257 ∧
      (∀ c, c < 257 → (clo[c]!).toNat = histLo Ls c) ∧ (∀ c, c < 257 → (chi[c]!).toNat = histHi Ls c)) :
    Sat (SH H i z b s d) (sortBlock (.ref (qRef false b) 0) (.ref (qRef true b) 0) nl clo chi)
      (fun r H' => ∃ (qS : Bool) (Lv Sc : Array UInt32), r = (.ref (qRef qS b) 0, .ref (qRef (!qS) b) 0) ∧
        H' = SH H i z b { s with pq_leaves := Lv, pq_scratch := Sc } d ∧ Lv.size = 287 ∧ Sc.size = 287 ∧
        ∀ p, p < Ls.length → (qArr qS { s with pq_leaves := Lv, pq_scratch := Sc })[p]! = pk (sortKeys Ls)[p]!) := by
  have hself : s = { s with pq_leaves := s.pq_leaves, pq_scratch := s.pq_scratch } := rfl
  unfold sortBlock
  by_cases e2 : Ls.length = 2
  · -- two leaves: the swap
    have c2 : (nl == 2) = true := (i32_beq_iff nl 2 2 rfl).mpr (by omega)
    simp only [c2, ↓reduceIte]
    obtain ⟨a, c, hac⟩ : ∃ a c, Ls = [a, c] := by
      match Ls, e2 with
      | [a, c], _ => exact ⟨a, c, rfl⟩
    subst hac
    have ha := hb a (by simp)
    have hc := hb c (by simp)
    have hne : a.2 ≠ c.2 := by simpa using hd
    have l0 : s.pq_leaves[0]! = pk a := hLv 0 (by simp)
    have l1 : s.pq_leaves[1]! = pk c := hLv 1 (by simp)
    have g0 := dwGet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false s 0 (by simp [qArr, hql])
    have g1 := dwGet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false s 1 (by simp [qArr, hql])
    refine Sat.bind (Sat.of_eq g0 (Sat.bind (Sat.of_eq g1 ?_)))
    simp only [qArr, Bool.false_eq_true, ↓reduceIte, l0, l1]
    by_cases sw : pk a > pk c
    · simp only [sw, ↓reduceIte]
      have k : keyLt a c = false := by
        cases h : keyLt a c
        · rfl
        · have := (pk_lt_iff a c ha.1 ha.2 hc.1 hc.2).mpr h
          exact absurd (UInt32.lt_trans this sw) (UInt32.lt_irrefl _)
      have s0 := dwSet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false s 0 (by simp [qArr, hql]) (pk c)
      refine Sat.bind (Sat.of_eq s0 ?_)
      have s1 := dwSet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false (qPut false s ((qArr false s).set! 0 (pk c))) 1
        (by simp [qArr, qPut, hql]) (pk a)
      refine Sat.bind (Sat.of_eq s1 (Sat.pure ⟨false, _, s.pq_scratch, rfl, rfl, by simp [qArr, qPut, hql], hqs, ?_⟩))
      intro p hp
      rw [sortKeys_two, k]
      simp only [qArr, qPut, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      simp at hp
      match p, hp with
      | 0, _ => simp [hql]
      | 1, _ => simp [hql]
    · simp only [sw, ↓reduceIte]
      have k : keyLt a c = true := by
        have : pk a ≠ pk c := fun e => by
          have h1 := pk_toNat a (by omega) ha.2
          have h2 := pk_toNat c (by omega) hc.2
          rw [e] at h1; omega
        have : pk a < pk c := by
          rw [UInt32.lt_iff_toNat_lt]
          have sw' : ¬ (pk c).toNat < (pk a).toNat := fun h => sw (UInt32.lt_iff_toNat_lt.mpr h)
          have : (pk a).toNat ≠ (pk c).toNat := fun e => this (UInt32.toNat_inj.mp e)
          omega
        exact (pk_lt_iff a c ha.1 ha.2 hc.1 hc.2).mp this
      refine Sat.pure ⟨false, s.pq_leaves, s.pq_scratch, rfl, rfl, hql, hqs, fun p hp => ?_⟩
      rw [sortKeys_two, k]
      simp at hp
      simp only [Bool.false_eq_true, ↓reduceIte]
      match p, hp with
      | 0, _ => exact l0
      | 1, _ => exact l1
  · have c2 : (nl == 2) = false := by
      cases h : (nl == 2)
      · rfl
      · exact absurd ((i32_beq_iff nl 2 2 rfl).mp h) (by omega)
    simp only [c2, Bool.false_eq_true, ↓reduceIte]
    have h3' : 3 ≤ Ls.length := by omega
    obtain ⟨inc, hclo, hchi, hlo, hhi⟩ := h3 h3'
    generalize hN : Ls.length = N at *
    have hidx : ∀ l, l < N → (Ls[l]!).1 < 65536 ∧ (Ls[l]!).2 < 1024 := fun l hl => hb _ (mem_of_idx Ls l (by omega))
    rw [aget_ok (by omega), pure_bind_M]
    have hh1 := hhi 1 (by omega)
    have hcnt := (hist_le Ls 1).2
    -- the low-byte pass
    have hcv1 : ∀ c, c < 257 → (clo[c]!).toNat =
        (List.range N).countP (fun l => decide (dig (qArr false s) (10 : Int32).toUInt32 l + 1 = c)) := by
      intro c hc
      rw [hlo c hc, histLo, hist_idx Ls (· % 256) c, hN]
      apply List.countP_congr; intro l hl
      have hl' := List.mem_range.mp hl
      simp only [dig, qArr, Bool.false_eq_true, ↓reduceIte, hLv l (by omega), dig_lo _ (hidx l hl').1 (hidx l hl').2]
    have P1 := radix_SH (H := H) (i := i) (z := z) (b := b) (d := d) false s nl 10 N (by omega) (by omega)
      (by decide) (by decide) (by simp [qArr, hql]) (by simp [qArr, hqs]) clo hclo hcv1
    have g1 : ∀ l, l < N → dig (qArr false s) (10 : Int32).toUInt32 l = (Ls[l]!).1 % 256 := by
      intro l hl
      simp only [dig, qArr, Bool.false_eq_true, ↓reduceIte, hLv l (by omega), dig_lo _ (hidx l hl).1 (hidx l hl).2]
    have r1 : ∀ j, j < N → krank N (dig (qArr false s) (10 : Int32).toUInt32) j = krank N (fun l => (Ls[l]!).1 % 256) j :=
      fun j hj => krank_congr N _ _ g1 j hj
    by_cases one : chi[1]!.toNat = N
    · -- every frequency below 256: one pass
      have c3 : ((chi[1]!).toUInt32.toInt32 == nl) = true := by
        rw [beq_iff_eq]; apply Int32.toInt_inj.mp; rw [toInt32_u16, hnl, one]
      simp only [c3, ↓reduceIte]
      have all : ∀ l, l < N → (Ls[l]!).1 < 256 := by
        intro l hl
        rw [hh1, histHi, ← List.countP_eq_length_filter, ← hN, List.countP_eq_length] at one
        have := one _ (mem_of_idx Ls l (by omega))
        have := beq_iff_eq.mp this
        omega
      refine Sat.bind (Sat.mono P1 fun _ H1 ⟨D, hH1, hD, hDv⟩ => ?_)
      subst hH1
      refine Sat.pure ⟨true, s.pq_leaves, D, rfl, rfl, hql, hD, ?_⟩
      have := sorted_of_rank Ls inc D (fun j hj => by
        rw [hN] at hj ⊢
        rw [← krank_congr N (fun l => (Ls[l]!).1 % 256) _ (fun l hl => Nat.mod_eq_of_lt (all l hl)) j hj, ← r1 j hj,
          hDv j hj, ← hLv j (by omega)]; rfl)
      rw [hN] at this
      exact this
    · have c3 : ((chi[1]!).toUInt32.toInt32 == nl) = false := by
        cases h : ((chi[1]!).toUInt32.toInt32 == nl)
        · rfl
        · rw [beq_iff_eq] at h
          have := congrArg Int32.toInt h
          rw [toInt32_u16, hnl] at this; omega
      simp only [c3, Bool.false_eq_true, ↓reduceIte]
      refine Sat.bind (Sat.mono P1 fun _ H1 ⟨D1, hH1, hD1, hDv1⟩ => ?_)
      subst hH1
      -- the high-byte pass
      have hcv2 : ∀ c, c < 257 → (chi[c]!).toNat =
          (List.range N).countP (fun l => decide (dig (qArr true (qPut true s D1)) ((10 : UInt32) + 8).toInt32.toUInt32 l + 1 = c)) := by
        intro c hc
        rw [countP_reindex N (krank N (dig (qArr false s) (10 : Int32).toUInt32)) (fun _ h => krank_lt _ h)
          (fun _ _ hl hj e => krank_inj _ hl hj e)]
        rw [hhi c hc, histHi, hist_idx Ls (· / 256) c, hN]
        apply List.countP_congr; intro l hl
        have hl' := List.mem_range.mp hl
        have e8 : ((10 : UInt32) + 8).toInt32.toUInt32 = (18 : Int32).toUInt32 := rfl
        rw [qArr_qPut, e8]
        have hd1 := hDv1 l hl'
        unfold dig at hd1 ⊢
        rw [hd1]
        simp only [qArr, Bool.false_eq_true, ↓reduceIte, hLv l (by omega), dig_hi _ (hidx l hl').1 (hidx l hl').2]
      have P2 := radix_SH (H := H) (i := i) (z := z) (b := b) (d := d) true (qPut true s D1) nl
        ((10 : UInt32) + 8).toInt32 N (by omega) (by omega) (by decide) (by decide) (by rw [qArr_qPut]; exact hD1)
        (by simp [qArr, qPut, hql]) chi hchi hcv2
      refine Sat.bind (Sat.mono P2 fun _ H2 ⟨D2, hH2, hD2, hDv2⟩ => ?_)
      subst hH2
      refine Sat.pure ⟨false, D2, D1, rfl, rfl, hD2, hD1, ?_⟩
      simp only [qArr, Bool.false_eq_true, ↓reduceIte]
      have := sorted_of_rank Ls inc D2 (fun j hj => by
        rw [hN] at hj ⊢
        have tp := two_pass N (fun l => pk Ls[l]!) (fun q => D1[q]!)
          (fun v => ((v >>> (10 : Int32).toUInt32) &&& 0xFF).toNat)
          (fun v => ((v >>> (18 : Int32).toUInt32) &&& 0xFF).toNat) (fun j hj => by
            have := hDv1 j hj
            rw [r1 j hj] at this
            rw [krank_congr N _ (fun l => (Ls[l]!).1 % 256) (fun l hl => dig_lo _ (hidx l hl).1 (hidx l hl).2) j hj]
            rw [this]; simp only [qArr, Bool.false_eq_true, ↓reduceIte, hLv j (by omega)]) j hj
        have e1 : krank N (fun l => ((pk Ls[l]! >>> (10 : Int32).toUInt32) &&& 0xFF).toNat) j =
            krank N (dig (qArr false s) (10 : Int32).toUInt32) j := by
          rw [r1 j hj]; exact krank_congr N _ _ (fun l hl => dig_lo _ (hidx l hl).1 (hidx l hl).2) j hj
        rw [e1] at tp
        have e2 : (fun q => ((D1[q]! >>> (18 : Int32).toUInt32) &&& 0xFF).toNat) =
            dig (qArr true (qPut true s D1)) ((10 : UInt32) + 8).toInt32.toUInt32 := rfl
        rw [e2] at tp
        have hfin := hDv2 (krank N (dig (qArr false s) (10 : Int32).toUInt32) j) (krank_lt _ hj)
        rw [tp] at hfin
        have e3 : (List.range N).countP (fun l => decide (((pk Ls[l]! >>> (18 : Int32).toUInt32) &&& 0xFF).toNat <
            ((pk Ls[j]! >>> (18 : Int32).toUInt32) &&& 0xFF).toNat ∨
            (((pk Ls[l]! >>> (18 : Int32).toUInt32) &&& 0xFF).toNat =
              ((pk Ls[j]! >>> (18 : Int32).toUInt32) &&& 0xFF).toNat ∧
            (((pk Ls[l]! >>> (10 : Int32).toUInt32) &&& 0xFF).toNat <
              ((pk Ls[j]! >>> (10 : Int32).toUInt32) &&& 0xFF).toNat ∨
             (((pk Ls[l]! >>> (10 : Int32).toUInt32) &&& 0xFF).toNat =
              ((pk Ls[j]! >>> (10 : Int32).toUInt32) &&& 0xFF).toNat ∧ l < j))))) =
            krank N (fun l => (Ls[l]!).1) j := by
          unfold krank
          apply List.countP_congr; intro l hl
          have hl' := List.mem_range.mp hl
          rw [dig_hi _ (hidx l hl').1 (hidx l hl').2, dig_hi _ (hidx j hj).1 (hidx j hj).2,
            dig_lo _ (hidx l hl').1 (hidx l hl').2, dig_lo _ (hidx j hj).1 (hidx j hj).2]
          simp only [kLt, decide_eq_true_eq]
          exact digits_iff _ _ l j
        rw [e3] at hfin
        rw [hfin, qArr_qPut, hDv1 j hj]; simp only [qArr, Bool.false_eq_true, ↓reduceIte, hLv j (by omega)])
      rw [hN] at this
      exact this

end

end ZlibNgF.Proof.TreesSort
