import ZlibNgF.Proof.«trees.c.prims»
import ZlibNgF.Math.HuffModel

/-!
# The leaf scan of `build_tree` (`ZlibNgF`)

The first loop of `build_tree` (`for (n = 0; n < elems; n++)`) on `SH` heaps computes what the model of
`Math/HuffModel.lean` says: `pq_leaves[0 .. nleaves)` holds the packed entries of `scanLeaves` (the pairs
`(freq, node)` of the nonzero frequencies in node order), `max_code + 1 = maxCode1`, `count_lo` / `count_hi` hold
the histograms of the low / high frequency byte at offset +1, and `tree[n].Len = 0` exactly for the zero
frequencies; the frequencies are unchanged.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.TreesScan
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNg.Trees ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.TreesPrims
open ZlibNgF.Math.Huff (scanLeaves maxCode1)
open ZlibNg.Inftrees (aget aset)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.DeflateAlloc (pure_bind_M ite_t ite_f)

/-! ## Arithmetic -/

/-- The packed queue entry of a leaf `(freq, node)`: `pq_pack(freq, node)`. -/
def pk (e : Nat × Nat) : UInt32 := (e.1.toUInt32 <<< 10) ||| e.2.toUInt32

/-- The frequency of code `k` in tree `F`. -/
def frq (F : Array Ct) (k : Nat) : Nat := (F[k]!).fc.toNat

/-- `count_lo[c]`: the leaves whose low frequency byte is `c - 1`. -/
def histLo (L : List (Nat × Nat)) (c : Nat) : Nat := (L.filter (fun e => e.1 % 256 + 1 == c)).length

/-- `count_hi[c]`: the leaves whose high frequency byte is `c - 1`. -/
def histHi (L : List (Nat × Nat)) (c : Nat) : Nat := (L.filter (fun e => e.1 / 256 + 1 == c)).length

theorem aget_ok {α : Type} [Inhabited α] {a : Array α} {k : Nat} (hk : k < a.size) : aget a k = pure a[k]! := by
  simp [aget, hk]

theorem aset_ok {α : Type} {a : Array α} {k : Nat} {v : α} (hk : k < a.size) : aset a k v = pure (a.set! k v) := by
  simp [aset, hk, Array.set!_eq_setIfInBounds]

theorem chkI32_ok {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : chkI32 v = pure (Int32.ofInt v) := by
  simp [chkI32, h1, h2]

theorem i32_ofInt (v : Int) (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : (Int32.ofInt v).toInt = v := by
  rw [Int32.toInt_ofInt]; apply Int.bmod_eq_of_le <;> simp [Int32.size] <;> omega

theorem i32_add1 (n : Int32) (h0 : -1000 ≤ n.toInt) (h1 : n.toInt ≤ 1000) : (n + 1).toInt = n.toInt + 1 := by
  rw [Int32.toInt_add, Int32.toInt_one]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem pq_pack_pk (f : UInt16) (n : Int32) (h0 : 0 ≤ n.toInt) (h1 : n.toInt < 1024) :
    pq_pack f.toUInt32 n = pk (f.toNat, n.toInt.toNat) := by
  have e1 : f.toUInt32 = f.toNat.toUInt32 := by apply UInt32.toNat_inj.mp; simp
  have e2 : n.toUInt32 = n.toInt.toNat.toUInt32 := by
    apply UInt32.toNat_inj.mp
    rw [ZlibNgF.Proof.DeflatePrime.toUInt32_toNat n h0, Nat.toUInt32, UInt32.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp only [pq_pack, pk, PQ_NODE_BITS, e1, e2]

theorem lo_idx (f : UInt16) : ((f &&& 0xFF) + 1).toNat = f.toNat % 256 + 1 := by
  have := f.toNat_lt
  have e : f.toNat &&& 255 = f.toNat % 256 := Nat.and_two_pow_sub_one_eq_mod _ 8
  simp [UInt16.toNat_add, UInt16.toNat_and, e]
  omega

theorem hi_idx (f : UInt16) : ((f >>> 8) + 1).toNat = f.toNat / 256 + 1 := by
  have := f.toNat_lt
  simp [UInt16.toNat_add, UInt16.toNat_shiftRight]
  omega

/-! ## The model lists -/

theorem scan_succ (fr : Nat → Nat) (n : Nat) :
    scanLeaves fr (n + 1) = scanLeaves fr n ++ (if fr n ≠ 0 then [(fr n, n)] else []) := rfl

theorem scan_len (fr : Nat → Nat) (n : Nat) : (scanLeaves fr n).length ≤ n := by
  induction n with
  | zero => simp [scanLeaves]
  | succ n ih => rw [scan_succ]; split <;> simp <;> omega

theorem scan_mem (fr : Nat → Nat) (n : Nat) (e : Nat × Nat) (he : e ∈ scanLeaves fr n) :
    e.2 < n ∧ e.1 = fr e.2 ∧ e.1 ≠ 0 := by
  induction n with
  | zero => simp [scanLeaves] at he
  | succ n ih =>
    rw [scan_succ] at he
    split at he
    · rcases List.mem_append.mp he with h | h
      · have := ih h; omega
      · simp at h; subst h; simp; omega
    · simp at he; have := ih he; omega

theorem hist_le (L : List (Nat × Nat)) (c : Nat) : histLo L c ≤ L.length ∧ histHi L c ≤ L.length :=
  ⟨List.length_filter_le _ _, List.length_filter_le _ _⟩

theorem getElem!_append_lt {L : List (Nat × Nat)} {e : Nat × Nat} {j : Nat} (hj : j < L.length) :
    (L ++ [e])[j]! = L[j]! := by
  simp [List.getElem?_append_left hj]

theorem getElem!_append_eq {L : List (Nat × Nat)} {e : Nat × Nat} : (L ++ [e])[L.length]! = e := by
  simp

theorem set!_get_ne {α : Type} [Inhabited α] (a : Array α) (k j : Nat) (v : α) (h : j ≠ k) :
    (a.set! k v)[j]! = a[j]! := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [Ne.symm h]

theorem set!_get_eq {α : Type} [Inhabited α] (a : Array α) (k : Nat) (v : α) (h : k < a.size) :
    (a.set! k v)[k]! = v := by
  simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
  simp [h]

theorem histLo_snoc (L : List (Nat × Nat)) (e : Nat × Nat) (c : Nat) :
    histLo (L ++ [e]) c = histLo L c + (if e.1 % 256 + 1 = c then 1 else 0) := by
  simp only [histLo, List.filter_append, List.length_append]
  by_cases h : e.1 % 256 + 1 = c
  · simp [List.filter, h]
  · have h' : (e.1 % 256 + 1 == c) = false := by simpa using h
    simp [List.filter, h, h']

theorem histHi_snoc (L : List (Nat × Nat)) (e : Nat × Nat) (c : Nat) :
    histHi (L ++ [e]) c = histHi L c + (if e.1 / 256 + 1 = c then 1 else 0) := by
  simp only [histHi, List.filter_append, List.length_append]
  by_cases h : e.1 / 256 + 1 = c
  · simp [List.filter, h]
  · have h' : (e.1 / 256 + 1 == c) = false := by simpa using h
    simp [List.filter, h, h']

/-! ## Commuting the array updates -/

@[simp] theorem tArr_qPut (t : DescSel) (q : Bool) (s : DeflateState) (A : Array UInt32) :
    tArr t (qPut q s A) = tArr t s := by cases t <;> cases q <;> rfl
@[simp] theorem qArr_tPut (t : DescSel) (q : Bool) (s : DeflateState) (A : Array Ct) :
    qArr q (tPut t s A) = qArr q s := by cases t <;> cases q <;> rfl
theorem tPut_qPut (t : DescSel) (q : Bool) (s : DeflateState) (A A' : Array Ct) (L : Array UInt32) :
    tPut t (qPut q (tPut t s A) L) A' = qPut q (tPut t s A') L := by cases t <;> cases q <;> rfl
@[simp] theorem qPut_qPut (q : Bool) (s : DeflateState) (L L' : Array UInt32) :
    qPut q (qPut q s L) L' = qPut q s L' := by cases q <;> rfl
theorem tPut_self (t : DescSel) (s : DeflateState) : tPut t s (tArr t s) = s := by cases t <;> rfl
theorem qPut_self (q : Bool) (s : DeflateState) : qPut q s (qArr q s) = s := by cases q <;> rfl

/-! ## The loop -/

/-- What the leaf scan has done after codes `[0, n)` of the tree `F`: tree `A`, `pq_leaves` `Lv`. -/
def ScanOK (F : Array Ct) (n : Nat) (nl mc : Int32) (clo chi : Array UInt16) (A : Array Ct) (Lv : Array UInt32) :
    Prop :=
  A.size = F.size ∧ (∀ k, k < F.size → (A[k]!).fc = (F[k]!).fc) ∧
    (∀ k, k < F.size → (A[k]!).dl = if k < n ∧ (F[k]!).fc = 0 then 0 else (F[k]!).dl) ∧ Lv.size = 287 ∧
    nl.toInt = (scanLeaves (frq F) n).length ∧
    (∀ j, j < (scanLeaves (frq F) n).length → Lv[j]! = pk (scanLeaves (frq F) n)[j]!) ∧
    mc.toInt + 1 = maxCode1 (frq F) n ∧ clo.size = 257 ∧ chi.size = 257 ∧
    (∀ c, c < 257 → (clo[c]!).toNat = histLo (scanLeaves (frq F) n) c) ∧
    (∀ c, c < 257 → (chi[c]!).toNat = histHi (scanLeaves (frq F) n) c)

/-- The condition of the leaf scan. -/
def scanCond (elems : Int32) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16 →
    M (Bool × (Int32 × Int32 × Int32 × Array UInt16 × Array UInt16)) :=
  fun ((n, nl, mc, clo, chi) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) =>
    pure (n < elems, (n, nl, mc, clo, chi))

/-- The body of the leaf scan. -/
def scanBody (tree : CtPtr) (leaves : DWPtr) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16 →
    M (Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) :=
  fun ((n, nl, mc, clo, chi) : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) => do
    let freq ← ctFc tree n.toInt
    if freq != 0 then
      dwSet leaves nl.toInt (pq_pack freq.toUInt32 n)
      let nl ← chkI32 (nl.toInt + 1)
      let ilo := ((freq &&& 0xFF) + 1).toNat
      let clo ← aset clo ilo ((← aget clo ilo) + 1)
      let ihi := ((freq >>> 8) + 1).toNat
      let chi ← aset chi ihi ((← aget chi ihi) + 1)
      pure (n + 1, nl, n, clo, chi)
    else
      ctSetDl tree n.toInt 0
      pure (n + 1, nl, mc, clo, chi)

section
variable {H : Heap} {i : Nat} {z : ZStream} {b : Nat} {d : Array UInt8}

/-- The leaf scan of `build_tree` on the tree of descriptor `t` (`E = elems` codes, at most 286, all inside the
tree array; `pq_leaves` of `L_CODES + 1` entries). -/
theorem scan_SH (t : DescSel) (s : DeflateState) (elems : Int32) (E : Nat) (hE : elems.toInt = E) (hE1 : E ≤ 286)
    (hF : E ≤ (tArr t s).size) (hq : s.pq_leaves.size = 287) :
    Sat (SH H i z b s d)
      (cwhile (scanCond elems) (scanBody (.ref (tRef t b) 0) (.ref (qRef false b) 0))
        ((0 : Int32), (0 : Int32), (-1 : Int32), Array.replicate 257 (0 : UInt16), Array.replicate 257 (0 : UInt16)))
      (fun x H' => ∃ A Lv, H' = SH H i z b (qPut false (tPut t s A) Lv) d ∧ x.1.toInt = E ∧
        ScanOK (tArr t s) E x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 A Lv) := by
  have hm1 : (-1 : Int32).toInt = -1 := by decide
  refine sat_cwhile (I := fun (x : Int32 × Int32 × Int32 × Array UInt16 × Array UInt16) H' =>
      ∃ A Lv, H' = SH H i z b (qPut false (tPut t s A) Lv) d ∧ 0 ≤ x.1.toInt ∧ x.1.toInt ≤ E ∧
        ScanOK (tArr t s) x.1.toInt.toNat x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 A Lv)
    (μ := fun x => E - x.1.toInt.toNat) _ ?_
    ⟨tArr t s, s.pq_leaves, by rw [tPut_self]; rfl, by decide, by simp,
      rfl, fun _ _ => rfl, fun k _ => by simp, hq, by simp [scanLeaves], by simp [scanLeaves],
      by simp [hm1, maxCode1], by simp, by simp,
      fun c hc => by simp [scanLeaves, histLo, hc], fun c hc => by simp [scanLeaves, histHi, hc]⟩
    (by simp [fuel]; omega)
  rintro ⟨n, nl, mc, clo, chi⟩ _ ⟨A, Lv, rfl, h0, hn, hA, hfc, hdl, hLv, hnl, hLvj, hmc, hclo, hchi, hclov, hchiv⟩
  dsimp only at h0 hn hA hfc hdl hLv hnl hLvj hmc hclo hchi hclov hchiv ⊢
  simp only [scanCond]
  refine Sat.pure ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [decide_eq_true_eq] at hc
    have hlt : n.toInt < E := by have := Int32.lt_iff_toInt_lt.mp hc; omega
    generalize hk : n.toInt.toNat = k at hfc hdl hLvj hnl hmc hclov hchiv
    have hkn : n.toInt = (k : Int) := by omega
    have hkF : k < (tArr t s).size := by omega
    have hkA : k < A.size := by omega
    have hs1 : (n + 1).toInt = n.toInt + 1 := i32_add1 n (by omega) (by omega)
    have hLk := scan_len (frq (tArr t s)) k
    simp only [scanBody]
    have e1 := ctFc_T (H := H) (i := i) (z := z) (b := b) (d := d) t (qPut false (tPut t s A) Lv) k (by simpa using hkA)
    rw [← hkn] at e1
    refine Sat.bind (Sat.of_eq e1 ?_)
    simp only [tArr_qPut, tArr_tPut]
    have hfk : frq (tArr t s) k = (A[k]!).fc.toNat := by simp [frq, hfc k hkF]
    by_cases hf : (A[k]!).fc = 0
    · -- a zero frequency: `tree[n].Len = 0`
      have hf' : ((A[k]!).fc != 0) = false := by simp [hf]
      simp only [hf', Bool.false_eq_true, ↓reduceIte]
      have e2 := ctSetDl_T (H := H) (i := i) (z := z) (b := b) (d := d) t (qPut false (tPut t s A) Lv) k (by simpa using hkA) 0
      rw [← hkn] at e2
      refine Sat.bind (Sat.of_eq e2 (Sat.pure ⟨⟨A.set! k { A[k]! with dl := 0 }, Lv,
        by simp only [tArr_qPut, tArr_tPut, tPut_qPut], ?_⟩, ?_⟩))
      rotate_left
      · dsimp only; omega
      have hfz : frq (tArr t s) k = 0 := by rw [hfk, hf]; rfl
      have hsc : scanLeaves (frq (tArr t s)) (k + 1) = scanLeaves (frq (tArr t s)) k := by
        rw [scan_succ]; simp [hfz]
      have hmc1 : maxCode1 (frq (tArr t s)) (k + 1) = maxCode1 (frq (tArr t s)) k := by simp [maxCode1, hfz]
      have hk1 : (n + 1).toInt.toNat = k + 1 := by omega
      dsimp only
      refine ⟨by omega, by omega, ?_⟩
      unfold ScanOK
      rw [hk1, hsc, hmc1]
      refine ⟨by simp [hA], fun k' hk' => ?_, fun k' hk' => ?_, hLv, hnl, hLvj, hmc, hclo, hchi, hclov, hchiv⟩
      · by_cases e : k' = k
        · subst e; rw [set!_get_eq _ _ _ hkA]; exact hfc _ hk'
        · rw [set!_get_ne _ _ _ _ e]; exact hfc _ hk'
      · by_cases e : k' = k
        · subst e; rw [set!_get_eq _ _ _ hkA]
          have : (tArr t s)[k']!.fc = 0 := by rw [← hfc _ hk', hf]
          simp [this]
        · rw [set!_get_ne _ _ _ _ e, hdl _ hk']
          by_cases c1 : k' < k
          · simp [c1, show k' < k + 1 by omega]
          · simp [c1, show ¬ k' < k + 1 by omega]
    · -- a nonzero frequency: a new leaf
      have hf' : ((A[k]!).fc != 0) = true := by simp [hf]
      simp only [hf', ↓reduceIte]
      have hfz : frq (tArr t s) k ≠ 0 := by
        rw [hfk]; intro e; exact hf (UInt16.toNat_inj.mp (by simpa using e))
      generalize hL : scanLeaves (frq (tArr t s)) k = L at hLvj hnl hclov hchiv hLk
      have hsc : scanLeaves (frq (tArr t s)) (k + 1) = L ++ [(frq (tArr t s) k, k)] := by
        rw [scan_succ, hL]; simp [hfz]
      have hmc1 : maxCode1 (frq (tArr t s)) (k + 1) = k + 1 := by simp [maxCode1, hfz]
      rw [hnl]
      have e2 := dwSet_Q (H := H) (i := i) (z := z) (b := b) (d := d) false (qPut false (tPut t s A) Lv) L.length
        (by simp [hLv]; omega) (pq_pack (A[k]!).fc.toUInt32 n)
      refine Sat.bind (Sat.of_eq e2 ?_)
      simp only [qArr_qPut, qPut_qPut]
      rw [chkI32_ok (by omega) (by omega), pure_bind_M, lo_idx, hi_idx,
        aget_ok (by rw [hclo]; have := (A[k]!).fc.toNat_lt; omega), pure_bind_M,
        aset_ok (by rw [hclo]; have := (A[k]!).fc.toNat_lt; omega), pure_bind_M,
        aget_ok (by rw [hchi]; have := (A[k]!).fc.toNat_lt; omega), pure_bind_M,
        aset_ok (by rw [hchi]; have := (A[k]!).fc.toNat_lt; omega), pure_bind_M]
      refine Sat.pure ⟨⟨A, _, rfl, ?_⟩, ?_⟩
      rotate_left
      · dsimp only; omega
      have hk1 : (n + 1).toInt.toNat = k + 1 := by omega
      dsimp only
      refine ⟨by omega, by omega, ?_⟩
      unfold ScanOK
      rw [hk1, hsc, hmc1]
      have hpk : pq_pack (A[k]!).fc.toUInt32 n = pk (frq (tArr t s) k, k) := by
        rw [pq_pack_pk _ n h0 (by omega), hfk, hk]
      have hlo : ∀ c, histLo L c ≤ 286 := fun c => by have := (hist_le L c).1; omega
      have hhi : ∀ c, histHi L c ≤ 286 := fun c => by have := (hist_le L c).2; omega
      have hfk2 : (A[k]!).fc.toNat = frq (tArr t s) k := hfk.symm
      refine ⟨hA, hfc, fun k' hk' => ?_, by simp [hLv], ?_, fun j hj => ?_, ?_, by simp [hclo], by simp [hchi],
        fun c hc => ?_, fun c hc => ?_⟩
      · rw [hdl _ hk']
        by_cases e : k' = k
        · subst e
          have : ¬ (tArr t s)[k']!.fc = 0 := by rw [← hfc _ hk']; exact hf
          simp [this]
        · by_cases c1 : k' < k
          · simp [c1, show k' < k + 1 by omega]
          · simp [c1, show ¬ k' < k + 1 by omega]
      · rw [i32_ofInt _ (by omega) (by omega)]; simp
      · simp only [List.length_append, List.length_singleton] at hj
        by_cases e : j = L.length
        · subst e; rw [set!_get_eq _ _ _ (by omega), getElem!_append_eq, hpk]
        · rw [set!_get_ne _ _ _ _ e, getElem!_append_lt (by omega)]; exact hLvj j (by omega)
      · omega
      · rw [histLo_snoc]
        by_cases e : c = frq (tArr t s) k % 256 + 1
        · subst e
          rw [hfk2, set!_get_eq _ _ _ (by rw [hclo]; omega)]
          have := hclov _ hc
          have := hlo (frq (tArr t s) k % 256 + 1)
          simp only [↓reduceIte]
          rw [UInt16.toNat_add, UInt16.toNat_one, Nat.mod_eq_of_lt (by omega)]
          simp; omega
        · rw [hfk2, set!_get_ne _ _ _ _ e, hclov c hc]; simp [Ne.symm e]
      · rw [histHi_snoc]
        by_cases e : c = frq (tArr t s) k / 256 + 1
        · subst e
          rw [hfk2, set!_get_eq _ _ _ (by rw [hchi]; have := (tArr t s)[k]!.fc.toNat_lt; simp only [frq]; omega)]
          have := hchiv _ hc
          have := hhi (frq (tArr t s) k / 256 + 1)
          simp only [↓reduceIte]
          rw [UInt16.toNat_add, UInt16.toNat_one, Nat.mod_eq_of_lt (by omega)]
          simp; omega
        · rw [hfk2, set!_get_ne _ _ _ _ e, hchiv c hc]; simp [Ne.symm e]
  · simp only [decide_eq_false_iff_not] at hc
    have hge : E ≤ n.toInt := by
      refine Int.not_lt.mp fun hh => hc (Int32.lt_iff_toInt_lt.mpr (by omega))
    have hk : n.toInt.toNat = E := by omega
    refine ⟨A, Lv, rfl, ?_⟩
    dsimp only
    have hE' : n.toInt = (E : Int) := by rw [← hk]; exact (Int.toNat_of_nonneg h0).symm
    rw [hk] at hdl hLvj hnl hmc hclov hchiv
    exact ⟨hE', hA, hfc, hdl, hLv, hnl, hLvj, hmc, hclo, hchi, hclov, hchiv⟩

end
end ZlibNgF.Proof.TreesScan
