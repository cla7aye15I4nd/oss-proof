import ZlibNgF.Proof.«inftrees.c.loopdefs»

/-!
# The replication loops of `zng_inflate_table` (`ZlibNgF`)

With `incr = 2 ^ a` and `fill = 2 ^ cu`, `a ≤ cu ≤ 15`, the unrolled loop and the tail loop store `here` at
`base_ptr[j * incr]` for every `j < 2 ^ (cu - a)` and nowhere else (`Fill`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees

/-- `C'` is `C` with `v` stored at `p + j * d` for `lo ≤ j < hi`. -/
structure Fill (C C' : Array Code) (p d lo hi : Nat) (v : Code) : Prop where
  size : C'.size = C.size
  set : ∀ j, lo ≤ j → j < hi → C'[p + j * d]? = some v
  keep : ∀ i, (∀ j, lo ≤ j → j < hi → i ≠ p + j * d) → C'[i]? = C[i]?

theorem Fill.refl (C : Array Code) (p d m : Nat) (v : Code) : Fill C C p d m m v :=
  ⟨rfl, fun j h1 h2 => by omega, fun _ _ => rfl⟩

theorem Fill.step {C C1 : Array Code} {p d q m : Nat} {v : Code} (hF : Fill C C1 p d q m v) (hq : 1 ≤ q)
    (hqm : q ≤ m) (hlt : p + (q - 1) * d < C1.size) : Fill C (C1.set! (p + (q - 1) * d) v) p d (q - 1) m v := by
  obtain ⟨hs, hset, hkeep⟩ := hF
  refine ⟨by simp [hs], fun j h1 h2 => ?_, fun i hi => ?_⟩
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : p + (q - 1) * d = p + j * d
    · rw [← e]; simp [hlt]
    · rw [ite_eq_right e]
      apply hset j _ h2
      by_cases hj : j = q - 1
      · subst hj; exact absurd rfl e
      · omega
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have : p + (q - 1) * d ≠ i := fun x => hi (q - 1) (by omega) (by omega) x.symm
    rw [ite_eq_right this]
    exact hkeep i (fun j h1 h2 => hi j (by omega) h2)

theorem stCode_ok {h0 : Heap} {b : Nat} {s : InflateState} (hl : LiveSt h0 b s) {C : Array Code}
    {W : Array UInt16} {p i : Nat} (hi : p + i < C.size) (v : Code) :
    stCode (.ref (CodeRef.codes b) p) (Int.ofNat i) v (setCW h0 b s C W) =
      .ok ((), setCW h0 b s (C.set! (p + i) v) W) := by
  unfold stCode
  have e : Int.ofNat i = (i : Int) := rfl
  rw [e, bind_app, add_ok (get_codes hl C W) (by omega) (by omega) (by omega)]
  rw [show ((p : Int) + (i : Int)).toNat = p + i by omega]
  exact store_codes hl hi v

theorem u32_toNat_mul_small {k : Nat} {d : UInt32} (this : k < 2 ^ 32) (hk : k * d.toNat < 2 ^ 32) :
    ((k.toUInt32) * d).toNat = k * d.toNat := by
  rw [UInt32.toNat_mul, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt this]
  exact Nat.mod_eq_of_lt hk

section loops
variable {h0 : Heap} {b : Nat} {s : InflateState} {W : Array UInt16}

/-- The unrolled replication loop. -/
theorem fill4_wp (hl : LiveSt h0 b s) {C : Array Code} {p a m : Nat} (hm1 : 1 ≤ m) (hm : m * 2 ^ a ≤ 2 ^ 15)
    (hp : p + m * 2 ^ a ≤ C.size) (incr : UInt32) (hincr : incr.toNat = 2 ^ a) (u : UInt32)
    (f0 : UInt32) (hf0 : f0.toNat = m * 2 ^ a) :
    Wp (cwhile
      (fun (fill : UInt32) => pure (fill >= incr <<< 2, fill))
      (fun (fill : UInt32) => do
        stCode (.ref (CodeRef.codes b) p) (Int.ofNat (fill - 1 * incr).toNat) (unpackCode u)
        stCode (.ref (CodeRef.codes b) p) (Int.ofNat (fill - 2 * incr).toNat) (unpackCode u)
        stCode (.ref (CodeRef.codes b) p) (Int.ofNat (fill - 3 * incr).toNat) (unpackCode u)
        stCode (.ref (CodeRef.codes b) p) (Int.ofNat (fill - 4 * incr).toNat) (unpackCode u)
        pure (fill - incr <<< 2))
      f0) (setCW h0 b s C W)
      (fun f h' => ∃ q C', f.toNat = q * 2 ^ a ∧ q < 4 ∧ h' = setCW h0 b s C' W ∧
        Fill C C' p (2 ^ a) q m (unpackCode u)) := by
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  have hD : 2 ^ a ≤ 2 ^ 15 := Nat.le_trans (Nat.le_mul_of_pos_left _ hm1) hm
  have h4 : (incr <<< 2).toNat = 4 * 2 ^ a := by
    rw [UInt32.toNat_shiftLeft, hincr]
    have : (2 : UInt32).toNat % 32 = 2 := rfl
    rw [this, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  refine Wp.cwhile (fun n (f : UInt32) h' => ∃ C', f.toNat = n * 2 ^ a ∧ n ≤ m ∧ h' = setCW h0 b s C' W ∧
      C'.size = C.size ∧ Fill C C' p (2 ^ a) n m (unpackCode u)) _ ?_
    (n := m) ⟨C, hf0, Nat.le_refl _, rfl, rfl,
      Fill.refl C p _ m _⟩ (by have := Nat.le_mul_of_pos_right m hpa; unfold fuel; omega)
  rintro n f h' ⟨C1, hf, hn, rfl, hs1, hF⟩
  rw [Wp.pure_iff]
  simp only
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hge : 4 ≤ n := by
      simp only [decide_eq_true_eq, UInt32.le_iff_toNat_le, h4, hf] at hc
      exact Nat.le_of_mul_le_mul_right (by omega) hpa
    have e : ∀ k : Nat, k ≤ 4 → (f - k.toUInt32 * incr).toNat = (n - k) * 2 ^ a := by
      intro k hk
      have hk4 : k * 2 ^ a ≤ 4 * 2 ^ a := Nat.mul_le_mul_right _ hk
      have hnm : n * 2 ^ a ≤ m * 2 ^ a := Nat.mul_le_mul_right _ hn
      have hkm : (k.toUInt32 * incr).toNat = k * 2 ^ a := by
        rw [u32_toNat_mul_small (by omega) (by rw [hincr]; omega), hincr]
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hkm, hf]; exact Nat.mul_le_mul_right _ (by omega)),
        hkm, hf, Nat.sub_mul]
    have e1 := e 1 (by omega)
    have e2 := e 2 (by omega)
    have e3 := e 3 (by omega)
    have e4 := e 4 (by omega)
    simp only [Nat.toUInt32_eq] at e1 e2 e3 e4
    have hlt : ∀ k, 1 ≤ k → k ≤ 4 → p + (n - k) * 2 ^ a < C1.size := by
      intro k hk1 hk4
      rw [hs1]
      have : (n - k) * 2 ^ a < m * 2 ^ a := Nat.mul_lt_mul_of_pos_right (by omega) hpa
      omega
    rw [Wp.bind_iff]
    refine Wp.of_eq (by rw [show ((1 : UInt32)) = UInt32.ofNat 1 from rfl, e1]; exact stCode_ok hl (hlt 1 (Nat.le_refl _) (by omega)) _) ?_
    rw [Wp.bind_iff]
    refine Wp.of_eq (by rw [show ((2 : UInt32)) = UInt32.ofNat 2 from rfl, e2]; exact stCode_ok hl (by simp; exact hlt 2 (by omega) (by omega)) _) ?_
    rw [Wp.bind_iff]
    refine Wp.of_eq (by rw [show ((3 : UInt32)) = UInt32.ofNat 3 from rfl, e3]; exact stCode_ok hl (by simp; exact hlt 3 (by omega) (by omega)) _) ?_
    rw [Wp.bind_iff]
    refine Wp.of_eq (by rw [show ((4 : UInt32)) = UInt32.ofNat 4 from rfl, e4]; exact stCode_ok hl (by simp; exact hlt 4 (by omega) (Nat.le_refl _)) _) ?_
    rw [Wp.pure_iff]
    refine ⟨n - 4, by omega, _, ?_, by omega, rfl, by simp [hs1], ?_⟩
    · rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, h4, hf]; exact Nat.mul_le_mul_right _ hge), h4, hf,
        Nat.sub_mul]
    · have F1 := Fill.step hF (by omega) (by omega) (hlt 1 (Nat.le_refl _) (by omega))
      have F2 := Fill.step F1 (by omega) (by omega) (by rw [F1.size, hs1.symm]; exact (by have := hlt 2 (by omega) (by omega); rw [show n - 1 - 1 = n - 2 by omega]; exact this))
      have F3 := Fill.step F2 (by omega) (by omega) (by rw [F2.size, hs1.symm]; exact (by have := hlt 3 (by omega) (by omega); rw [show n - 1 - 1 - 1 = n - 3 by omega]; exact this))
      have F4 := Fill.step F3 (by omega) (by omega) (by rw [F3.size, hs1.symm]; exact (by have := hlt 4 (by omega) (Nat.le_refl _); rw [show n - 1 - 1 - 1 - 1 = n - 4 by omega]; exact this))
      simp only [show n - 1 - 1 = n - 2 by omega, show n - 2 - 1 = n - 3 by omega,
        show n - 3 - 1 = n - 4 by omega] at F4
      exact F4
  · have hlt4 : n < 4 := by
      simp only [decide_eq_false_iff_not, UInt32.le_iff_toNat_le, h4, hf, Nat.not_le] at hc
      exact Nat.lt_of_mul_lt_mul_right hc
    exact ⟨n, C1, hf, hlt4, rfl, hF⟩

/-- The tail replication loop. -/
theorem fill1_wp (hl : LiveSt h0 b s) {C C1 : Array Code} {p a m q : Nat} (hm : m * 2 ^ a ≤ 2 ^ 15)
    (hp : p + m * 2 ^ a ≤ C.size) (incr : UInt32) (hincr : incr.toNat = 2 ^ a) (u : UInt32)
    (f : UInt32) (hf : f.toNat = q * 2 ^ a) (hq : q ≤ m) (hF : Fill C C1 p (2 ^ a) q m (unpackCode u)) :
    Wp (cwhile
      (fun (fill : UInt32) => pure (fill != 0, fill))
      (fun (fill : UInt32) => do
        let fill := fill - incr
        stCode (.ref (CodeRef.codes b) p) (Int.ofNat fill.toNat) (unpackCode u)
        pure fill)
      f) (setCW h0 b s C1 W)
      (fun _ h' => ∃ C', h' = setCW h0 b s C' W ∧ Fill C C' p (2 ^ a) 0 m (unpackCode u)) := by
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  refine Wp.cwhile (fun n (f : UInt32) h' => ∃ C', f.toNat = n * 2 ^ a ∧ n ≤ m ∧ h' = setCW h0 b s C' W ∧
      Fill C C' p (2 ^ a) n m (unpackCode u)) _ ?_ ⟨C1, hf, hq, rfl, hF⟩ (by have := Nat.le_mul_of_pos_right m hpa; unfold fuel; omega)
  rintro n f h' ⟨C2, hf2, hn, rfl, hF2⟩
  rw [Wp.pure_iff]
  simp only
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hne : f ≠ 0 := by simpa using hc
    have h1 : 1 ≤ n := by
      have : f.toNat ≠ 0 := fun x => hne (UInt32.toNat_inj.mp (by rw [x]; rfl))
      rw [hf2] at this
      rcases Nat.eq_zero_or_pos n with e | e
      · rw [e] at this; simp at this
      · exact e
    have e : (f - incr).toNat = (n - 1) * 2 ^ a := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, hincr, hf2]; exact Nat.le_mul_of_pos_left _ h1),
        hincr, hf2, Nat.sub_mul, Nat.one_mul]
    have hlt : p + (n - 1) * 2 ^ a < C2.size := by
      rw [hF2.size]
      have : (n - 1) * 2 ^ a < m * 2 ^ a := Nat.mul_lt_mul_of_pos_right (by omega) hpa
      omega
    rw [Wp.bind_iff, e]
    refine Wp.of_eq (stCode_ok hl hlt _) ?_
    rw [Wp.pure_iff]
    exact ⟨n - 1, by omega, _, e, by omega, rfl, Fill.step hF2 h1 hn hlt⟩
  · have hz : f = 0 := by simpa using hc
    have : n = 0 := by
      rw [hz] at hf2
      have : n * 2 ^ a = 0 := by simpa using hf2.symm
      rcases Nat.mul_eq_zero.mp this with e | e
      · exact e
      · omega
    subst this
    exact ⟨C2, rfl, hF2⟩

end loops

end ZlibNgF.Proof.Inftrees
