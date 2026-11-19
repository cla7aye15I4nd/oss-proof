import ZlibNgF.Spec.Common.Types
import ZlibNgF.Math.Adler32Swar

/-!
# The Adler-32 kernel `adler32_c` computes the RFC 1950 sums (`ZlibNgF`)

`adler32_c` on a readable buffer terminates without fault, leaves the heap unchanged, and returns the packed
reduced sums of the buffer (`adler32_c_ok`). The proof follows the C: the 8-byte alignment prefix
(`adler32_copy_align`), blocks of at most `NMAX` bytes made of 64-bit SWAR chunks of at most 184 bytes
(`adler32_swar`), and the tail (`adler32_copy_tail`). Every 32-bit accumulator is tracked modulo `2^32`
against the unreduced sums `rawSums`; the `NMAX` bound shows that the reductions see the exact sums.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Adler32Kernel
open C ZlibNg.Zbuild ZlibNg.Adler32P ZlibNg.Adler32C
open ZlibNgF.Math.Adler32 ZlibNgF.Math.Adler32Swar

/-! ## Heap-preserving runs and loop rules -/

/-- `m` terminates on `h` without fault, leaves `h` unchanged, and its value satisfies `Q`. -/
def Ok {α : Type} (h : Heap) (m : M α) (Q : α → Prop) : Prop :=
  ∃ v, C.run m h = .ok (v, h) ∧ Q v

theorem Ok.pure {α : Type} {h : Heap} {Q : α → Prop} {v : α} (hq : Q v) :
    Ok h (Pure.pure v) Q := ⟨v, rfl, hq⟩

theorem Ok.bind {α β : Type} {h : Heap} {m : M α} {f : α → M β} {P : α → Prop} {Q : β → Prop}
    (hm : Ok h m P) (hf : ∀ v, P v → Ok h (f v) Q) : Ok h (m >>= f) Q := by
  obtain ⟨v, hv, hp⟩ := hm
  obtain ⟨w, hw, hq⟩ := hf v hp
  exact ⟨w, by rw [C.run_bind, hv]; exact hw, hq⟩

theorem Ok.mono {α : Type} {h : Heap} {m : M α} {P Q : α → Prop}
    (hm : Ok h m P) (hpq : ∀ v, P v → Q v) : Ok h m Q := by
  obtain ⟨v, hv, hp⟩ := hm
  exact ⟨v, hv, hpq v hp⟩

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

/-- Loop rule for `while (cond) body` with a decreasing measure. -/
theorem cwhile_measure {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop) {s : σ}
    (hstep : ∀ s, I s → Ok h (cond s) (fun cs =>
      (cs.1 = true → Ok h (body cs.2) (fun s2 => I s2 ∧ μ s2 < μ s)) ∧ (cs.1 = false → Q cs.2)))
    (hI : I s) (hμ : μ s < fuel) : Ok h (cwhile cond body s) Q :=
  cwhile_go_measure I μ Q hstep fuel s hI hμ

private theorem cdoWhile_go_measure {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop)
    (hstep : ∀ s, I s → Ok h (body s) (fun s1 => Ok h (cond s1) (fun cs =>
      (cs.1 = true → I cs.2 ∧ μ cs.2 < μ s) ∧ (cs.1 = false → Q cs.2)))) :
    ∀ n s, I s → μ s < n → Ok h (cdoWhile.go body cond n s) Q := by
  intro n
  induction n with
  | zero => intro s _ hlt; omega
  | succ n ih =>
    intro s hI hlt
    obtain ⟨s1, hb, hc⟩ := hstep s hI
    obtain ⟨⟨c, s2⟩, hc', ht, hf⟩ := hc
    cases c with
    | false =>
      refine ⟨s2, ?_, hf rfl⟩
      unfold C.run at *
      simp [cdoWhile.go, hb, hc']
    | true =>
      obtain ⟨hI2, hμ⟩ := ht rfl
      dsimp only at hI2 hμ
      obtain ⟨s', hgo, hq⟩ := ih s2 hI2 (by omega)
      refine ⟨s', ?_, hq⟩
      unfold C.run at *
      simp [cdoWhile.go, hb, hc', hgo]

/-- Loop rule for `do body while (cond)` with a decreasing measure. -/
theorem cdoWhile_measure {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (I : σ → Prop) (μ : σ → Nat) (Q : σ → Prop) {s : σ}
    (hstep : ∀ s, I s → Ok h (body s) (fun s1 => Ok h (cond s1) (fun cs =>
      (cs.1 = true → I cs.2 ∧ μ cs.2 < μ s) ∧ (cs.1 = false → Q cs.2))))
    (hI : I s) (hμ : μ s < fuel) : Ok h (cdoWhile body cond s) Q :=
  cdoWhile_go_measure I μ Q hstep fuel s hI hμ

/-! ## Buffer slices -/

/-- The `len` bytes of `data` from `off`. -/
abbrev slice (data : Array UInt8) (off len : Nat) : List UInt8 :=
  (data.toList.drop off).take len

theorem slice_split (data : Array UInt8) (off m n : Nat) :
    slice data off (m + n) = slice data off m ++ slice data (off + m) n := by
  unfold slice
  rw [List.take_add, List.drop_drop, Nat.add_comm off m]

theorem slice_len {data : Array UInt8} {off len : Nat} (hle : off + len ≤ data.size) :
    (slice data off len).length = len := by
  unfold slice
  rw [List.length_take, List.length_drop, Array.length_toList]
  omega

theorem slice_one {data : Array UInt8} {off : Nat} (hlt : off < data.size) :
    slice data off 1 = [data[off]!] := by
  unfold slice
  have hlt_l : off < data.toList.length := by simpa using hlt
  rw [List.drop_eq_getElem_cons hlt_l, getElem!_pos data off hlt]
  simp

theorem slice_getD {data : Array UInt8} {off n i : Nat} (hi : i < n) (hle : off + n ≤ data.size) :
    (slice data off n).getD i 0 = data[off + i]! := by
  unfold slice
  rw [getElem!_pos data (off + i) (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi, show off + i < data.size by omega]

/-! ## Unreduced sums modulo `2^32` -/

theorem rawSums_congr (M : Nat) (xs : List UInt8) : ∀ (a s a' s' : Nat), a % M = a' % M → s % M = s' % M →
    (rawSums (a, s) xs).1 % M = (rawSums (a', s') xs).1 % M ∧
    (rawSums (a, s) xs).2 % M = (rawSums (a', s') xs).2 % M := by
  induction xs with
  | nil => intro a s a' s' ha hs; exact ⟨ha, hs⟩
  | cons x xs ih =>
    intro a s a' s' ha hs
    simp only [rawSums_cons, rawStep]
    have h1 : (a + x.toNat) % M = (a' + x.toNat) % M := by rw [Nat.add_mod, ha, ← Nat.add_mod]
    have h2 : (s + (a + x.toNat)) % M = (s' + (a' + x.toNat)) % M := by
      rw [Nat.add_mod, hs, h1, ← Nat.add_mod]
    exact ih _ _ _ _ h1 h2

/-- The pair of 32-bit accumulators holds the unreduced sums `p` modulo `2^32`. -/
def R32 (v : UInt32 × UInt32) (p : Nat × Nat) : Prop :=
  v.1.toNat = p.1 % 2 ^ 32 ∧ v.2.toNat = p.2 % 2 ^ 32

theorem R32_chain {v1 v2 : UInt32 × UInt32} {p : Nat × Nat} {xs ys : List UInt8}
    (h1 : R32 v1 (rawSums p xs)) (h2 : R32 v2 (rawSums (v1.1.toNat, v1.2.toNat) ys)) :
    R32 v2 (rawSums p (xs ++ ys)) := by
  obtain ⟨e1, e2⟩ := h1
  obtain ⟨f1, f2⟩ := h2
  have hc := rawSums_congr (2 ^ 32) ys v1.1.toNat v1.2.toNat (rawSums p xs).1 (rawSums p xs).2
    (by rw [e1, Nat.mod_mod]) (by rw [e2, Nat.mod_mod])
  rw [rawSums_append]
  exact ⟨f1.trans hc.1, f2.trans hc.2⟩

theorem R32_nil (a s : UInt32) : R32 (a, s) (rawSums (a.toNat, s.toNat) []) :=
  ⟨(Nat.mod_eq_of_lt a.toNat_lt).symm, (Nat.mod_eq_of_lt s.toNat_lt).symm⟩

/-! ## Read-only primitives -/

theorem ptr_add_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
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

theorem load8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (hlt : o < data.size) : Ok h (load8 (.ref r o)) (fun b => b = data[o]!) := by
  refine ⟨data[o], ?_, (getElem!_pos data o hlt).symm⟩
  dsimp only [C.run, load8, Ptr.load]
  rw [hg]
  dsimp only
  split
  · rfl
  · rename_i hn; exact absurd hlt hn

theorem index8_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (i : Int) (h0 : 0 ≤ i) (hlt : o + i.toNat < data.size) :
    Ok h (index8 (.ref r o) i) (fun b => b = data[o + i.toNat]!) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, i = (n : Int) := ⟨i.toNat, by omega⟩
  rw [Int.toNat_natCast] at hlt ⊢
  unfold index8 Ptr.index
  refine Ok.bind (ptr_add_ok hg n (by omega)) (fun p hp => ?_)
  subst hp
  exact load8_ok hg hlt

/-! ## `ADLER_DO1`, `ADLER_DO2`, `ADLER_DO4` -/

theorem adler_do1_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i) (hle : o + i.toNat + 1 ≤ data.size) :
    Ok h (adler_do1 a s (.ref r o) i) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data (o + i.toNat) 1))) := by
  unfold adler_do1
  refine Ok.bind (index8_ok hg i h0 (by omega)) (fun b hb => Ok.pure ?_)
  subst hb
  rw [slice_one (by omega)]
  simp only [rawSums_cons, rawSums_nil, rawStep, R32]
  have hb : (data[o + i.toNat]!).toUInt32.toNat = (data[o + i.toNat]!).toNat := UInt8.toNat_toUInt32 _
  refine ⟨?_, ?_⟩
  · rw [UInt32.toNat_add, hb]
  · rw [UInt32.toNat_add, UInt32.toNat_add, hb]
    omega

theorem adler_do2_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i) (hle : o + i.toNat + 2 ≤ data.size) :
    Ok h (adler_do2 a s (.ref r o) i) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data (o + i.toNat) 2))) := by
  unfold adler_do2
  refine Ok.bind (adler_do1_ok hg a s i h0 (by omega)) (fun v1 h1 => ?_)
  obtain ⟨a1, s1⟩ := v1
  refine Ok.mono (adler_do1_ok hg a1 s1 (i + 1) (by omega) (by omega)) (fun v2 h2 => ?_)
  rw [show o + (i + 1).toNat = o + i.toNat + 1 by omega] at h2
  rw [show (2 : Nat) = 1 + 1 from rfl, slice_split]
  exact R32_chain h1 h2

theorem adler_do4_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) {o : Nat} (i : Int) (h0 : 0 ≤ i) (hle : o + i.toNat + 4 ≤ data.size) :
    Ok h (adler_do4 a s (.ref r o) i) (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data (o + i.toNat) 4))) := by
  unfold adler_do4
  refine Ok.bind (adler_do2_ok hg a s i h0 (by omega)) (fun v1 h1 => ?_)
  obtain ⟨a1, s1⟩ := v1
  refine Ok.mono (adler_do2_ok hg a1 s1 (i + 2) (by omega) (by omega)) (fun v2 h2 => ?_)
  rw [show o + (i + 2).toNat = o + i.toNat + 2 by omega] at h2
  rw [show (4 : Nat) = 2 + 2 from rfl, slice_split]
  exact R32_chain h1 h2

/-! ## 64-bit words and their 16-bit lanes -/

/-- Four 16-bit lanes as one 64-bit value. -/
def lanes (l0 l1 l2 l3 : Nat) : Nat := l0 + 2 ^ 16 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3

theorem lanes_add (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    lanes a0 a1 a2 a3 + lanes b0 b1 b2 b3 = lanes (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  unfold lanes; omega

theorem lanes_lt (l0 l1 l2 l3 : Nat) (h0 : l0 < 2 ^ 16) (h1 : l1 < 2 ^ 16) (h2 : l2 < 2 ^ 16)
    (h3 : l3 < 2 ^ 16) : lanes l0 l1 l2 l3 < 2 ^ 64 := by
  unfold lanes; omega

theorem or_step (acc : UInt64) (b : UInt8) (k : Nat) (s : UInt64) (hs : s.toNat = k) (hk : k ≤ 56)
    (hacc : acc.toNat < 2 ^ k) : (acc ||| (b.toUInt64 <<< s)).toNat = acc.toNat + 2 ^ k * b.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hs, Nat.mod_eq_of_lt (show k < 64 by omega),
    UInt8.toNat_toUInt64]
  have hb : b.toNat < 256 := b.toNat_lt
  have hpk : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
  have hmul : b.toNat * 2 ^ k ≤ 255 * 2 ^ 56 := Nat.mul_le_mul (by omega) hpk
  have hsh : b.toNat <<< k % 2 ^ 64 = b.toNat <<< k := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  rw [hsh, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq, Nat.mul_comm]
  omega

/-- The little-endian value of eight bytes. -/
theorem or8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)).toNat =
    b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat + 2 ^ 32 * b4.toNat +
      2 ^ 40 * b5.toNat + 2 ^ 48 * b6.toNat + 2 ^ 56 * b7.toNat := by
  have l0 : b0.toNat < 256 := b0.toNat_lt
  have l1 : b1.toNat < 256 := b1.toNat_lt
  have l2 : b2.toNat < 256 := b2.toNat_lt
  have l3 : b3.toNat < 256 := b3.toNat_lt
  have l4 : b4.toNat < 256 := b4.toNat_lt
  have l5 : b5.toNat < 256 := b5.toNat_lt
  have l6 : b6.toNat < 256 := b6.toNat_lt
  have e0 : b0.toUInt64.toNat = b0.toNat := UInt8.toNat_toUInt64 b0
  have e1 := or_step b0.toUInt64 b1 8 8 rfl (by omega) (by rw [e0]; simp only [Nat.reducePow]; omega)
  rw [e0] at e1
  have e2 := or_step _ b2 16 16 rfl (by omega) (by rw [e1]; simp only [Nat.reducePow]; omega)
  rw [e1] at e2
  have e3 := or_step _ b3 24 24 rfl (by omega) (by rw [e2]; simp only [Nat.reducePow]; omega)
  rw [e2] at e3
  have e4 := or_step _ b4 32 32 rfl (by omega) (by rw [e3]; simp only [Nat.reducePow]; omega)
  rw [e3] at e4
  have e5 := or_step _ b5 40 40 rfl (by omega) (by rw [e4]; simp only [Nat.reducePow]; omega)
  rw [e4] at e5
  have e6 := or_step _ b6 48 48 rfl (by omega) (by rw [e5]; simp only [Nat.reducePow]; omega)
  rw [e5] at e6
  have e7 := or_step _ b7 56 56 rfl (by omega) (by rw [e6]; simp only [Nat.reducePow]; omega)
  rw [e6] at e7
  exact e7

theorem loadU64_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o : Nat} (i : Nat) (hle : o + 8 * i + 8 ≤ data.size) :
    Ok h (loadU64 (.ref r o) i) (fun v => v.toNat =
      (data[o + 8 * i]!).toNat + 2 ^ 8 * (data[o + 8 * i + 1]!).toNat + 2 ^ 16 * (data[o + 8 * i + 2]!).toNat +
      2 ^ 24 * (data[o + 8 * i + 3]!).toNat + 2 ^ 32 * (data[o + 8 * i + 4]!).toNat +
      2 ^ 40 * (data[o + 8 * i + 5]!).toNat + 2 ^ 48 * (data[o + 8 * i + 6]!).toNat +
      2 ^ 56 * (data[o + 8 * i + 7]!).toNat) := by
  unfold loadU64
  have q0 : (Int.ofNat (8 * i)).toNat = 8 * i := by simp only [Int.ofNat_eq_natCast]; omega
  have q1 : (Int.ofNat (8 * i) + 1).toNat = 8 * i + 1 := by simp only [Int.ofNat_eq_natCast]; omega
  have q2 : (Int.ofNat (8 * i) + 2).toNat = 8 * i + 2 := by simp only [Int.ofNat_eq_natCast]; omega
  have q3 : (Int.ofNat (8 * i) + 3).toNat = 8 * i + 3 := by simp only [Int.ofNat_eq_natCast]; omega
  have q4 : (Int.ofNat (8 * i) + 4).toNat = 8 * i + 4 := by simp only [Int.ofNat_eq_natCast]; omega
  have q5 : (Int.ofNat (8 * i) + 5).toNat = 8 * i + 5 := by simp only [Int.ofNat_eq_natCast]; omega
  have q6 : (Int.ofNat (8 * i) + 6).toNat = 8 * i + 6 := by simp only [Int.ofNat_eq_natCast]; omega
  have q7 : (Int.ofNat (8 * i) + 7).toNat = 8 * i + 7 := by simp only [Int.ofNat_eq_natCast]; omega
  have p0 : (0 : Int) ≤ Int.ofNat (8 * i) := by simp only [Int.ofNat_eq_natCast]; omega
  refine Ok.bind (index8_ok hg _ p0 (by rw [q0]; omega)) (fun x0 h0 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q1]; omega)) (fun x1 h1 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q2]; omega)) (fun x2 h2 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q3]; omega)) (fun x3 h3 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q4]; omega)) (fun x4 h4 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q5]; omega)) (fun x5 h5 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q6]; omega)) (fun x6 h6 => ?_)
  refine Ok.bind (index8_ok hg _ (by omega) (by rw [q7]; omega)) (fun x7 h7 => Ok.pure ?_)
  rw [q0] at h0
  rw [q1] at h1
  rw [q2] at h2
  rw [q3] at h3
  rw [q4] at h4
  rw [q5] at h5
  rw [q6] at h6
  rw [q7] at h7
  rw [or8, h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Nat.add_assoc]

/-- The even bytes of a 64-bit word, one per 16-bit lane. -/
theorem even_lanes (v : UInt64) (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (l0 : b0 < 256) (l1 : b1 < 256) (l2 : b2 < 256)
    (l3 : b3 < 256) (l4 : b4 < 256) (l5 : b5 < 256) (l6 : b6 < 256) (l7 : b7 < 256)
    (hv : v.toNat = b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3 + 2 ^ 32 * b4 + 2 ^ 40 * b5 + 2 ^ 48 * b6 +
      2 ^ 56 * b7) :
    (v &&& ADLER32_SWAR_EVEN_MASK).toNat = lanes b0 b2 b4 b6 ∧
    ((v >>> 8) &&& ADLER32_SWAR_EVEN_MASK).toNat = lanes b1 b3 b5 b7 := by
  have hm : ADLER32_SWAR_EVEN_MASK.toNat = 0x00FF00FF00FF00FF := rfl
  constructor
  · rw [UInt64.toNat_and, hm, land_even_mask, hv]
    unfold lanes
    simp only [Nat.reducePow] at *
    omega
  · rw [UInt64.toNat_and, hm, UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl,
      Nat.shiftRight_eq_div_pow, land_even_mask, hv]
    unfold lanes
    simp only [Nat.reducePow] at *
    omega

/-! ## `adler32_swar` -/

private theorem sh48 : (48 : UInt64).toNat % 64 = 48 := rfl
private theorem sh32 : (32 : UInt64).toNat % 64 = 32 := rfl
private theorem sh16 : (16 : UInt64).toNat % 64 = 16 := rfl

/-- `(x * c) >>> 48` on lanes, through a heap-free identity `e` on naturals. -/
private theorem mul_shr48 (x : UInt64) (c : UInt64) (n m : Nat) (hx : x.toNat = n) (hc : c.toNat = m)
    {r : Nat} (e : n * m % 2 ^ 64 / 2 ^ 48 = r) : ((x * c) >>> 48).toNat = r := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mul, hx, hc, sh48, Nat.shiftRight_eq_div_pow]
  exact e

/-- The value of the final reduction of `adler32_swar` after `T` groups. -/
theorem swar_final (a s : UInt32) (len : UInt64) (xs : List UInt8) (T : Nat) (hT : T ≤ 23)
    (hlen : len.toNat = 8 * T) (hxs : 8 * T ≤ xs.length) (SE SO PE PO : UInt64)
    (hSE : SE.toNat = lanes (gs xs T 0) (gs xs T 2) (gs xs T 4) (gs xs T 6))
    (hSO : SO.toNat = lanes (gs xs T 1) (gs xs T 3) (gs xs T 5) (gs xs T 7))
    (hPE : PE.toNat = lanes (ps xs T 0) (ps xs T 2) (ps xs T 4) (ps xs T 6))
    (hPO : PO.toNat = lanes (ps xs T 1) (ps xs T 3) (ps xs T 5) (ps xs T 7)) :
    R32 (a + (((SE + SO) * ADLER32_SWAR_HSUM) >>> 48).toUInt32,
      s + a * len.toUInt32 +
        ((((PE &&& (281470681808895 : UInt64)) + (PO &&& (281470681808895 : UInt64)) + (PE >>> 16 &&& (281470681808895 : UInt64)) +
            (PO >>> 16 &&& (281470681808895 : UInt64))) * 34359738376) >>> 32).toUInt32 +
        ((2 : UInt32) * ((SE * 1125912791875585) >>> 48).toUInt32 + ((SO * ADLER32_SWAR_HSUM) >>> 48).toUInt32 +
          (2 : UInt32) * ((SO * 844433520132096) >>> 48).toUInt32))
      (rawSums (a.toNat, s.toNat) (xs.take (8 * T))) := by
  rw [rawSums_groups xs a.toNat s.toNat T hxs]
  have hg : ∀ j, gs xs T j ≤ 5865 := fun j => by have := gs_le xs T j; omega
  have hp : ∀ j, ps xs T j ≤ 64515 := fun j => by have := ps_le xs T j; have := tri_le T hT; omega
  have g0 := hg 0; have g1 := hg 1; have g2 := hg 2; have g3 := hg 3
  have g4 := hg 4; have g5 := hg 5; have g6 := hg 6; have g7 := hg 7
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3
  have p4 := hp 4; have p5 := hp 5; have p6 := hp 6; have p7 := hp 7
  have hHS : ADLER32_SWAR_HSUM.toNat = 0x1000100010001 := rfl
  -- adler
  have hsum : (SE + SO).toNat = lanes (gs xs T 0 + gs xs T 1) (gs xs T 2 + gs xs T 3) (gs xs T 4 + gs xs T 5)
      (gs xs T 6 + gs xs T 7) := by
    rw [UInt64.toNat_add, hSE, hSO, lanes_add]
    exact Nat.mod_eq_of_lt (lanes_lt _ _ _ _ (by omega) (by omega) (by omega) (by omega))
  have hA := mul_shr48 (SE + SO) ADLER32_SWAR_HSUM _ _ hsum hHS
    (hsum_lanes _ _ _ _ (by simp only [Nat.reducePow]; omega))
  have hW4 := mul_shr48 SE 1125912791875585 _ _ hSE rfl
    (w4_lanes (gs xs T 0) (gs xs T 2) (gs xs T 4) (gs xs T 6) (by omega) (by omega) (by omega) (by omega))
  have hHO := mul_shr48 SO ADLER32_SWAR_HSUM _ _ hSO hHS
    (hsum_lanes (gs xs T 1) (gs xs T 3) (gs xs T 5) (gs xs T 7) (by simp only [Nat.reducePow]; omega))
  have hW3 := mul_shr48 SO 844433520132096 _ _ hSO rfl
    (w3_lanes (gs xs T 1) (gs xs T 3) (gs xs T 5) (gs xs T 7) (by omega) (by omega) (by omega))
  -- the prefix sums
  have hm : (281470681808895 : UInt64).toNat = 0xFFFF0000FFFF := rfl
  have lo_e : (PE &&& (281470681808895 : UInt64)).toNat = ps xs T 0 + 2 ^ 32 * ps xs T 4 := by
    rw [UInt64.toNat_and, hm, land_lane02, hPE]; unfold lanes; simp only [Nat.reducePow]; omega
  have lo_o : (PO &&& (281470681808895 : UInt64)).toNat = ps xs T 1 + 2 ^ 32 * ps xs T 5 := by
    rw [UInt64.toNat_and, hm, land_lane02, hPO]; unfold lanes; simp only [Nat.reducePow]; omega
  have hi_e : (PE >>> 16 &&& (281470681808895 : UInt64)).toNat = ps xs T 2 + 2 ^ 32 * ps xs T 6 := by
    rw [UInt64.toNat_and, hm, UInt64.toNat_shiftRight, sh16, Nat.shiftRight_eq_div_pow, land_lane02, hPE]
    unfold lanes; simp only [Nat.reducePow]; omega
  have hi_o : (PO >>> 16 &&& (281470681808895 : UInt64)).toNat = ps xs T 3 + 2 ^ 32 * ps xs T 7 := by
    rw [UInt64.toNat_and, hm, UInt64.toNat_shiftRight, sh16, Nat.shiftRight_eq_div_pow, land_lane02, hPO]
    unfold lanes; simp only [Nat.reducePow]; omega
  have hslots : ((PE &&& (281470681808895 : UInt64)) + (PO &&& (281470681808895 : UInt64)) + (PE >>> 16 &&& (281470681808895 : UInt64)) +
      (PO >>> 16 &&& (281470681808895 : UInt64))).toNat =
      (ps xs T 0 + ps xs T 1 + ps xs T 2 + ps xs T 3) + 2 ^ 32 * (ps xs T 4 + ps xs T 5 + ps xs T 6 + ps xs T 7) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, lo_e, lo_o, hi_e, hi_o]
    simp only [Nat.reducePow]
    omega
  have hX : ((((PE &&& (281470681808895 : UInt64)) + (PO &&& (281470681808895 : UInt64)) + (PE >>> 16 &&& (281470681808895 : UInt64)) +
      (PO >>> 16 &&& (281470681808895 : UInt64))) * 34359738376) >>> 32).toUInt32.toNat =
      8 * ((ps xs T 0 + ps xs T 1 + ps xs T 2 + ps xs T 3) + (ps xs T 4 + ps xs T 5 + ps xs T 6 + ps xs T 7))
        % 2 ^ 32 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_mul, hslots, sh32, Nat.shiftRight_eq_div_pow,
      show (34359738376 : UInt64).toNat = 0x800000008 from rfl]
    exact x8_slots _ _ (by simp only [Nat.reducePow]; omega)
  have hlen32 : len.toUInt32.toNat = 8 * T := by
    rw [UInt64.toNat_toUInt32, hlen]; omega
  have hmul : a.toNat * (8 * T) = 8 * T * a.toNat := Nat.mul_comm _ _
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [UInt32.toNat_add, UInt64.toNat_toUInt32, hA]
    omega
  · dsimp only
    rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, hlen32, hX,
      UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul,
      UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, hW4, hHO, hW3]
    simp only [show (2 : UInt32).toNat = 2 from rfl]
    omega

/-- One group added to a lane accumulator (`sum += v & mask`) and to its prefix (`prefix += sum`). -/
theorem acc_step (xs : List UInt8) (t q : Nat) (S P E : UInt64) (ht : t + 1 ≤ 23)
    (hS : S.toNat = lanes (gs xs t q) (gs xs t (q + 2)) (gs xs t (q + 4)) (gs xs t (q + 6)))
    (hP : P.toNat = lanes (ps xs t q) (ps xs t (q + 2)) (ps xs t (q + 4)) (ps xs t (q + 6)))
    (hE : E.toNat = lanes (xs.getD (8 * t + q) 0).toNat (xs.getD (8 * t + (q + 2)) 0).toNat
      (xs.getD (8 * t + (q + 4)) 0).toNat (xs.getD (8 * t + (q + 6)) 0).toNat) :
    (S + E).toNat = lanes (gs xs (t + 1) q) (gs xs (t + 1) (q + 2)) (gs xs (t + 1) (q + 4)) (gs xs (t + 1) (q + 6)) ∧
    (P + S).toNat = lanes (ps xs (t + 1) q) (ps xs (t + 1) (q + 2)) (ps xs (t + 1) (q + 4)) (ps xs (t + 1) (q + 6)) := by
  have hg : ∀ j, gs xs (t + 1) j ≤ 5865 := fun j => by have := gs_le xs (t + 1) j; omega
  have hp : ∀ j, ps xs (t + 1) j ≤ 64515 := fun j => by
    have := ps_le xs (t + 1) j; have := tri_le (t + 1) ht; omega
  have g0 := hg q; have g1 := hg (q + 2); have g2 := hg (q + 4); have g3 := hg (q + 6)
  have p0 := hp q; have p1 := hp (q + 2); have p2 := hp (q + 4); have p3 := hp (q + 6)
  simp only [gs, ps] at g0 g1 g2 g3 p0 p1 p2 p3 ⊢
  constructor
  · rw [UInt64.toNat_add, hS, hE, lanes_add]
    exact Nat.mod_eq_of_lt (lanes_lt _ _ _ _ (by omega) (by omega) (by omega) (by omega))
  · rw [UInt64.toNat_add, hP, hS, lanes_add]
    exact Nat.mod_eq_of_lt (lanes_lt _ _ _ _ (by omega) (by omega) (by omega) (by omega))

/-- The lanes of the 64-bit word at group `t` of a slice. -/
theorem group_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    {o n : Nat} (hle : o + n ≤ data.size) (t i : Nat) (hti : 8 * (t + i) + 8 ≤ n) :
    Ok h (loadU64 (.ref r (o + 8 * t)) i) (fun v =>
      (v &&& ADLER32_SWAR_EVEN_MASK).toNat =
        lanes ((slice data o n).getD (8 * (t + i) + 0) 0).toNat ((slice data o n).getD (8 * (t + i) + (0 + 2)) 0).toNat
          ((slice data o n).getD (8 * (t + i) + (0 + 4)) 0).toNat ((slice data o n).getD (8 * (t + i) + (0 + 6)) 0).toNat ∧
      ((v >>> 8) &&& ADLER32_SWAR_EVEN_MASK).toNat =
        lanes ((slice data o n).getD (8 * (t + i) + 1) 0).toNat ((slice data o n).getD (8 * (t + i) + (1 + 2)) 0).toNat
          ((slice data o n).getD (8 * (t + i) + (1 + 4)) 0).toNat ((slice data o n).getD (8 * (t + i) + (1 + 6)) 0).toNat) := by
  refine Ok.mono (loadU64_ok hg (o := o + 8 * t) i (by omega)) (fun v hv => ?_)
  have e : ∀ j, j < 8 → (slice data o n).getD (8 * (t + i) + j) 0 = data[o + 8 * t + 8 * i + j]! := by
    intro j hj
    rw [slice_getD (by omega) hle]
    congr 1
    omega
  rw [e 0 (by omega), e (0 + 2) (by omega), e (0 + 4) (by omega), e (0 + 6) (by omega), e 1 (by omega),
    e (1 + 2) (by omega), e (1 + 4) (by omega), e (1 + 6) (by omega)]
  simp only [Nat.add_zero, Nat.zero_add, show (1 : Nat) + 2 = 3 from rfl, show (1 : Nat) + 4 = 5 from rfl,
    show (1 : Nat) + 6 = 7 from rfl]
  exact even_lanes v _ _ _ _ _ _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _)
    (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) hv

/-- The four accumulators of `adler32_swar` after `t` groups. -/
def SwarInv (xs : List UInt8) (t : Nat) (st : SwarState) : Prop :=
  st.sum_even.toNat = lanes (gs xs t 0) (gs xs t (0 + 2)) (gs xs t (0 + 4)) (gs xs t (0 + 6)) ∧
  st.sum_odd.toNat = lanes (gs xs t 1) (gs xs t (1 + 2)) (gs xs t (1 + 4)) (gs xs t (1 + 6)) ∧
  st.prefix_even.toNat = lanes (ps xs t 0) (ps xs t (0 + 2)) (ps xs t (0 + 4)) (ps xs t (0 + 6)) ∧
  st.prefix_odd.toNat = lanes (ps xs t 1) (ps xs t (1 + 2)) (ps xs t (1 + 4)) (ps xs t (1 + 6))

/-- `adler32_swar(&adler, NULL, buf, len, &sum2, 0)` on an aligned buffer of `len` bytes, `len` a multiple of 8
from 8 to 184, adds the unreduced sums of the bytes. -/
theorem swar_ok {h : Heap} {r : BRef} {data : Array UInt8} (hg : Space.get h r = some data)
    (a s : UInt32) (o : Nat) (len : UInt64) (hal : (h.baseAddr r + UInt64.ofNat o).toNat % 8 = 0)
    (h8 : 8 ≤ len.toNat) (h184 : len.toNat ≤ 184) (hm8 : len.toNat % 8 = 0) (hle : o + len.toNat ≤ data.size) :
    Ok h (adler32_swar a .null (.ref r o) len s 0)
      (fun v => R32 v (rawSums (a.toNat, s.toNat) (slice data o len.toNat))) := by
  have hfuel : ∀ l : UInt64, l.toNat < fuel := fun l => by unfold fuel; exact l.toNat_lt
  have hxlen : (slice data o len.toNat).length = len.toNat := slice_len hle
  have htake : ∀ T, 8 * T = len.toNat → (slice data o len.toNat).take (8 * T) = slice data o len.toNat :=
    fun T hT => List.take_of_length_le (by omega)
  unfold adler32_swar
  simp only [show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hcast : C.run (Ptr.castAligned (.ref r o) 8) h = .ok (.ref r o, h) := by
    have hal' : ((h.baseAddr r).toNat + o) % 8 = 0 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat'] at hal
      simp only [Nat.reducePow] at hal
      omega
    simp only [C.run, Ptr.castAligned, bind_app, addrOf]
    simp [hal']
  refine Ok.bind (P := fun p => p = .ref r o) ⟨_, hcast, rfl⟩ (fun src hsrc => ?_)
  subst hsrc
  let I : SwarState → Prop := fun st => ∃ t, st.src64 = .ref r (o + 8 * t) ∧ st.dst = .null ∧
    st.len.toNat + 8 * t = len.toNat ∧ SwarInv (slice data o len.toNat) t st
  refine Ok.bind (P := fun st => I st ∧ st.len.toNat < 16)
    (cwhile_measure (I := I) (μ := fun st => st.len.toNat) (Q := fun st => I st ∧ st.len.toNat < 16) ?_
    ⟨0, by simp, rfl, by simp, by simp [SwarInv, gs, ps, lanes]⟩ (hfuel len)) (fun st hst => ?_)
  · rintro st ⟨t, hsrc, hdst, hlen, hinv⟩
    refine ⟨_, rfl, fun hcnd => ?_, fun hcnd => ⟨⟨t, hsrc, hdst, hlen, hinv⟩, by
      have := of_decide_eq_false hcnd
      show st.len.toNat < 16
      simp only [ge_iff_le, UInt64.le_iff_toNat_le, show (16 : UInt64).toNat = 16 from rfl] at this
      omega⟩⟩
    have h16 : 16 ≤ st.len.toNat := by
      have := of_decide_eq_true hcnd
      simpa [ge_iff_le, UInt64.le_iff_toNat_le] using this
    obtain ⟨iSE, iSO, iPE, iPO⟩ := hinv
    rw [hsrc]
    refine Ok.bind (group_ok hg hle t 0 (by omega)) (fun v0 hv0 => ?_)
    refine Ok.bind (group_ok hg hle t 1 (by omega)) (fun v1 hv1 => ?_)
    refine Ok.bind (ptr_add_ok hg 16 (by omega)) (fun p hp => ?_)
    subst hp
    have hsub : (st.len - 16).toNat = st.len.toNat - 16 :=
      UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact h16)
    simp only [Nat.add_zero] at hv0
    obtain ⟨e0, o0⟩ := hv0
    obtain ⟨e1, o1⟩ := hv1
    have ht : t + 2 ≤ 23 := by omega
    obtain ⟨aSE1, aPE1⟩ := acc_step _ t 0 _ _ _ (by omega) iSE iPE e0
    obtain ⟨aSO1, aPO1⟩ := acc_step _ t 1 _ _ _ (by omega) iSO iPO o0
    obtain ⟨aSE2, aPE2⟩ := acc_step _ (t + 1) 0 _ _ _ (by omega) aSE1 aPE1 e1
    obtain ⟨aSO2, aPO2⟩ := acc_step _ (t + 1) 1 _ _ _ (by omega) aSO1 aPO1 o1
    refine Ok.pure ⟨⟨t + 2, by show Ptr.ref r (o + 8 * t + 16) = Ptr.ref r (o + 8 * (t + 2)); congr 1,
      by show st.dst = .null; exact hdst, by show (st.len - 16).toNat + 8 * (t + 2) = len.toNat; omega, ?_⟩,
      by show (st.len - 16).toNat < st.len.toNat; omega⟩
    exact ⟨aSE2, aSO2, aPE2, aPO2⟩
  · obtain ⟨⟨t, hsrc, hdst, hlen, hinv⟩, hlt16⟩ := hst
    obtain ⟨iSE, iSO, iPE, iPO⟩ := hinv
    split
    · rename_i hge8
      have h8' : 8 ≤ st.len.toNat := hge8
      rw [hsrc]
      refine Ok.bind (group_ok hg hle t 0 (by omega)) (fun v hv => Ok.pure ?_)
      simp only [Nat.add_zero] at hv
      obtain ⟨e0, o0⟩ := hv
      obtain ⟨aSE, aPE⟩ := acc_step _ t 0 _ _ _ (by omega) iSE iPE e0
      obtain ⟨aSO, aPO⟩ := acc_step _ t 1 _ _ _ (by omega) iSO iPO o0
      have hf := swar_final a s len (slice data o len.toNat) (t + 1) (by omega) (by omega) (by omega) _ _ _ _
        aSE aSO aPE aPO
      rw [htake (t + 1) (by omega)] at hf
      exact hf
    · rename_i hlt8
      have h8' : st.len.toNat < 8 := by
        have : ¬ (8 ≤ st.len.toNat) := hlt8
        omega
      have hf := swar_final a s len (slice data o len.toNat) t (by omega) (by omega) (by omega) _ _ _ _
        iSE iSO iPE iPO
      rw [htake t (by omega)] at hf
      exact Ok.pure hf

end ZlibNgF.Proof.Adler32Kernel
