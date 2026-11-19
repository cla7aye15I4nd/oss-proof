import ZlibNgF.Proof.«inftrees.c.base»

/-!
# `count_lengths` (SSE2 lane model) (`ZlibNgF`)

For at most 288 lengths, each below 16, `count_lengths` does not fault, leaves the heap unchanged and returns, in
lane `i`, the number of lengths equal to `i`. The two byte accumulators `s1`, `s2` each take at most every other
length, so no lane reaches 256 and the wrapping byte additions are exact.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees

/-- The number of `j < n` with `f j = v`. -/
def lcount (f : Nat → Nat) (n v : Nat) : Nat := (List.range n).countP (fun j => f j == v)

@[simp] theorem lcount_zero (f : Nat → Nat) (v : Nat) : lcount f 0 v = 0 := rfl

theorem lcount_succ (f : Nat → Nat) (n v : Nat) :
    lcount f (n + 1) v = lcount f n v + if f n = v then 1 else 0 := by
  unfold lcount
  rw [List.range_succ, List.countP_append]
  simp

theorem lcount_le (f : Nat → Nat) (n v : Nat) : lcount f n v ≤ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [lcount_succ]; split <;> omega

/-- The result of `count_lengths` on the lengths `f 0, ..., f (n - 1)`. -/
def cntArr (f : Nat → Nat) (n : Nat) : Array UInt16 :=
  Array.ofFn (n := 16) fun i => (lcount f n i.val).toUInt16

theorem cntArr_size (f : Nat → Nat) (n : Nat) : (cntArr f n).size = 16 := by simp [cntArr]

theorem cntArr_get (f : Nat → Nat) (n : Nat) (hn : n ≤ 288) (i : Nat) (hi : i < 16) :
    ((cntArr f n)[i]'(by simp [cntArr, hi])).toNat = lcount f n i := by
  simp only [cntArr, Array.getElem_ofFn]
  have := lcount_le f n i
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
  omega

theorem oneRow_ok {k : UInt16} (hk : k.toNat < 16) :
    oneRow k = pure (Array.ofFn (n := 16) fun i => if i.val == k.toNat then 1 else 0) := by
  have : k < 16 := by rw [UInt16.lt_iff_toNat_lt]; exact hk
  simp [oneRow, this]

/-- The lane invariant of the SSE2 loop after `k` lengths. -/
def Lanes (f : Nat → Nat) (k : Nat) (s1 s2 : Array UInt8) : Prop :=
  s1.size = 16 ∧ s2.size = 16 ∧ ∀ i, i < 16 →
    (s1[i]!).toNat + (s2[i]!).toNat = lcount f k i ∧ (s1[i]!).toNat ≤ (k + 1) / 2 ∧ (s2[i]!).toNat ≤ k / 2

theorem lane_add (a : Array UInt8) (k : Nat) (i : Nat) (hi : i < 16) (ha : (a[i]!).toNat < 255) :
    ((addEpi8 a (Array.ofFn (n := 16) fun j => if j.val == k then 1 else 0))[i]!).toNat =
      (a[i]!).toNat + if k = i then 1 else 0 := by
  unfold addEpi8
  rw [getElem!_pos _ i (by simp [hi])]
  simp only [Array.getElem_ofFn, Fin.getElem!_fin]
  rw [getElem!_pos (Array.ofFn (n := 16) fun j => if j.val == k then (1 : UInt8) else 0) i (by simp [hi])]
  simp only [Array.getElem_ofFn]
  by_cases e : k = i
  · subst e
    simp only [BEq.rfl, ite_true, UInt8.toNat_add]
    have : (1 : UInt8).toNat = 1 := rfl
    rw [this]
    omega
  · have : (i == k) = false := by simp; omega
    simp [this, e]

theorem lanes_init_odd (f : Nat → Nat) :
    Lanes f 1 (Array.ofFn (n := 16) fun i => if i.val == f 0 then 1 else 0) (Array.replicate 16 0) := by
  refine ⟨by simp, by simp, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i (by simp [hi])]
  simp only [Array.getElem_ofFn, Array.getElem_replicate, lcount_succ, lcount_zero]
  by_cases e : f 0 = i
  · subst e; simp
  · have : (i == f 0) = false := by simp; omega
    simp [this, e]

theorem lanes_init_even (f : Nat → Nat) : Lanes f 0 (Array.replicate 16 0) (Array.replicate 16 0) := by
  refine ⟨by simp, by simp, fun i hi => ?_⟩
  rw [getElem!_pos _ i (by simp [hi])]
  simp

theorem lanes_step (f : Nat → Nat) (k : Nat) (s1 s2 : Array UInt8) (hk : k + 2 ≤ 288) (hL : Lanes f k s1 s2) :
    Lanes f (k + 2) (addEpi8 s1 (Array.ofFn (n := 16) fun j => if j.val == f k then 1 else 0))
      (addEpi8 s2 (Array.ofFn (n := 16) fun j => if j.val == f (k + 1) then 1 else 0)) := by
  obtain ⟨h1, h2, hl⟩ := hL
  refine ⟨by simp [addEpi8], by simp [addEpi8], fun i hi => ?_⟩
  obtain ⟨e, b1, b2⟩ := hl i hi
  rw [lane_add s1 (f k) i hi (by omega), lane_add s2 (f (k + 1)) i hi (by omega)]
  rw [lcount_succ, lcount_succ]
  refine ⟨?_, ?_, ?_⟩
  · omega
  · split <;> omega
  · split <;> omega

/-- The final lane sums. -/
theorem lanes_final (f : Nat → Nat) (n : Nat) (t1 t2 : Array UInt8) (hL : Lanes f n t1 t2) :
    (Array.ofFn (n := 16) fun i => t1[i]!.toUInt16 + t2[i]!.toUInt16) = cntArr f n := by
  obtain ⟨z1, z2, hl⟩ := hL
  apply Array.ext
  · simp [cntArr]
  · intro i hi1 hi2
    simp only [Array.size_ofFn] at hi1
    simp only [cntArr, Array.getElem_ofFn, Fin.getElem!_fin]
    obtain ⟨e, b1, b2⟩ := hl i hi1
    apply UInt16.toNat_inj.mp
    simp only [UInt16.toNat_add, UInt8.toNat_toUInt16, Nat.toUInt16_eq, UInt16.toNat_ofNat']
    have := lcount_le f n i
    omega

section loop
variable {r : WRef} {lo : Nat} {a : Array UInt16} {h : Heap} {c : UInt32}

theorem count_rd (hg : Space.get h r = some a) (hlo : lo + c.toNat ≤ a.size) (j : Nat) (hj : j < c.toNat) :
    Ptr.index (.ref r lo) (j : Int) h = .ok (a[lo + j]!, h) := by
  rw [index_ok hg (by omega) (by omega) (by omega)]
  congr
  rw [getElem!_pos a (lo + j) (by omega)]
  congr 1

theorem toInt32_eq : c.toInt32 = Int32.ofNat c.toNat := by
  conv => lhs; rw [← UInt32.ofNat_toNat (x := c)]
  rfl

theorem toInt32_par : (c.toInt32 &&& 1) = Int32.ofNat (c.toNat % 2) := by
  have e1 : c.toInt32 &&& 1 = (c &&& 1).toInt32 := by
    apply Int32.toBitVec_inj.mp
    simp
  rw [e1]
  have e2 : (c &&& 1).toNat = c.toNat % 2 := by simp [UInt32.toNat_and]
  conv => lhs; rw [← UInt32.ofNat_toNat (x := c &&& 1), e2]
  rfl

/-- The pair loop of `count_lengths`. -/
theorem count_loop (hg : Space.get h r = some a) (hlo : lo + c.toNat ≤ a.size) (hc : c.toNat ≤ 288)
    (hv : ∀ j, j < c.toNat → (a[lo + j]!).toNat < 16) (s1 : Array UInt8)
    (hL : Lanes (fun j => (a[lo + j]!).toNat) (c.toNat % 2) s1 (Array.replicate 16 0)) :
    Wp (cwhile
      (fun ((s1, s2, sym) : Array UInt8 × Array UInt8 × Int32) => pure (sym < c.toInt32, (s1, s2, sym)))
      (fun ((s1, s2, sym) : Array UInt8 × Array UInt8 × Int32) => do
        let l0 ← Ptr.index (.ref r lo) sym.toInt
        let s1 := addEpi8 s1 (← oneRow l0)
        let l1 ← Ptr.index (.ref r lo) (sym.toInt + 1)
        let s2 := addEpi8 s2 (← oneRow l1)
        pure (s1, s2, ← chkI32 (sym.toInt + 2)))
      (s1, Array.replicate 16 0, c.toInt32 &&& 1)) h
      (fun st h' => h' = h ∧ Lanes (fun j => (a[lo + j]!).toNat) c.toNat st.1 st.2.1) := by
  have hcn : c.toInt32 = Int32.ofNat c.toNat := toInt32_eq
  refine Wp.cwhile (fun m (st : Array UInt8 × Array UInt8 × Int32) h' =>
      h' = h ∧ ∃ k, st.2.2 = Int32.ofNat k ∧ k ≤ c.toNat ∧ k % 2 = c.toNat % 2 ∧ m = c.toNat - k ∧
        Lanes (fun j => (a[lo + j]!).toNat) k st.1 st.2.1)
    _ ?_ ⟨rfl, c.toNat % 2, toInt32_par, by omega, Nat.mod_mod _ _, rfl, hL⟩ (by unfold fuel; omega)
  rintro m ⟨t1, t2, sym⟩ h' ⟨rfl, k, rfl, hk, hkp, rfl, hLk⟩
  simp only [Wp.pure_iff]
  have hki : (Int32.ofNat k).toInt = k := Int32.toInt_ofNat_of_lt (by omega)
  have hni : (Int32.ofNat c.toNat).toInt = c.toNat := Int32.toInt_ofNat_of_lt (by omega)
  refine ⟨fun hlt => ?_, fun hge => ?_⟩
  · have hlt' : k < c.toNat := by
      simp only [decide_eq_true_eq, Int32.lt_iff_toInt_lt, hki, hcn, hni] at hlt
      omega
    rw [Wp.bind_iff, hki]
    refine Wp.of_eq (count_rd hg hlo k hlt') ?_
    have fk := hv k hlt'
    rw [oneRow_ok fk, Wp.bind_iff, Wp.pure_iff, Wp.bind_iff]
    rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega]
    refine Wp.of_eq (count_rd hg hlo (k + 1) (by omega)) ?_
    have fk1 := hv (k + 1) (by omega)
    rw [oneRow_ok fk1, Wp.bind_iff, Wp.pure_iff, Wp.bind_iff,
      chkI32_ok (by omega) (by omega), Wp.pure_iff, Wp.pure_iff]
    refine ⟨c.toNat - (k + 2), by omega, rfl, k + 2, ?_, by omega, by omega, rfl, ?_⟩
    · show Int32.ofInt ((k : Int) + 2) = _
      rw [show ((k : Int) + 2) = ((k + 2 : Nat) : Int) by omega, Int32.ofInt_eq_ofNat]
    · exact lanes_step _ k t1 t2 (by omega) hLk
  · have hge' : c.toNat ≤ k := by
      simp only [decide_eq_false_iff_not, Int32.lt_iff_toInt_lt, hki, hcn, hni] at hge
      omega
    have : k = c.toNat := by omega
    subst this
    exact ⟨by trivial, hLk⟩

end loop

/-- `count_lengths` on `n ≤ 288` lengths below 16 at `lens = r + lo`. -/
theorem count_lengths_wp {r : WRef} {lo : Nat} {a : Array UInt16} {h : Heap} {c : UInt32}
    (hg : Space.get h r = some a) (hlo : lo + c.toNat ≤ a.size) (hc : c.toNat ≤ 288)
    (hv : ∀ j, j < c.toNat → (a[lo + j]!).toNat < 16) :
    Wp (count_lengths (.ref r lo) c.toInt32) h
      (fun v h' => v = cntArr (fun j => (a[lo + j]!).toNat) c.toNat ∧ h' = h) := by
  unfold count_lengths
  dsimp only
  by_cases hodd : c.toNat % 2 = 1
  · rw [ite_eq_left (show (c.toInt32 &&& 1 != 0) = true by rw [toInt32_par, hodd]; decide), Wp.bind_iff]
    have r0 : Ptr.index (.ref r lo) 0 h = .ok (a[lo]!, h) := by simpa using count_rd hg hlo 0 (by omega)
    refine Wp.of_eq r0 ?_
    have hf0 := hv 0 (by omega)
    simp only [Nat.add_zero] at hf0
    rw [oneRow_ok hf0, Wp.bind_iff, Wp.pure_iff]
    have hL := lanes_init_odd (fun j => (a[lo + j]!).toNat)
    rw [← hodd] at hL
    rw [Wp.bind_iff]
    refine Wp.mono (count_loop hg hlo hc hv _ (by simpa using hL)) ?_
    rintro ⟨t1, t2, sym⟩ h' ⟨rfl, hLn⟩
    simp only [Wp.pure_iff]
    exact ⟨lanes_final _ _ t1 t2 hLn, trivial⟩
  · have h0 : c.toNat % 2 = 0 := by omega
    rw [ite_eq_right (show ¬ (c.toInt32 &&& 1 != 0) = true by rw [toInt32_par, h0]; decide), Wp.bind_iff, Wp.pure_iff,
      Wp.bind_iff]
    have hL := lanes_init_even (fun j => (a[lo + j]!).toNat)
    rw [← h0] at hL
    refine Wp.mono (count_loop hg hlo hc hv _ hL) ?_
    rintro ⟨t1, t2, sym⟩ h' ⟨rfl, hLn⟩
    simp only [Wp.pure_iff]
    exact ⟨lanes_final _ _ t1 t2 hLn, trivial⟩

end ZlibNgF.Proof.Inftrees
