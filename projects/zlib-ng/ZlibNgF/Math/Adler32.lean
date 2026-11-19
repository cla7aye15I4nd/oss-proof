/-!
# RFC 1950 §8.2 Adler-32 pure mathematics and 32-bit `NMAX = 5552` bounds (`ZlibNgF`)

Heap-free mathematical specification of Adler-32, modular shift identity for `adler32_combine`,
and exact 32-bit `UInt32` non-overflow bounds for `zlib-ng`'s `uint32_t` accumulators over `NMAX = 5552`.
-/

set_option autoImplicit false

namespace ZlibNgF.Math.Adler32

def BASE : Nat := 65521
def NMAX : Nat := 5552

/-- Single-byte modular RFC 1950 Adler-32 transition. -/
def step (s : Nat × Nat) (x : UInt8) : Nat × Nat :=
  let a' := (s.1 + x.toNat) % BASE
  (a', (s.2 + a') % BASE)

/-- Multi-byte modular RFC 1950 Adler-32 state over `xs`. -/
def sums (s : Nat × Nat) (xs : List UInt8) : Nat × Nat :=
  xs.foldl step s

/-- Canonical RFC 1950 §8.2 Adler-32 checksum of `xs` (seed `(1, 0)`). -/
def adler32 (xs : List UInt8) : UInt32 :=
  let (a, b) := sums (1, 0) xs
  UInt32.ofNat (a + 65536 * b)

/-- Canonicalize any 64-bit caller seed into reduced `(a, b) ∈ [0, 65521)^2`, then update over `xs`. -/
def adler32Update (seed : UInt64) (xs : List UInt8) : UInt64 :=
  let a0 := (seed.toNat % 65536) % BASE
  let b0 := ((seed.toNat / 65536) % 65536) % BASE
  let (a, b) := sums (a0, b0) xs
  UInt64.ofNat (a + 65536 * b)

@[simp] theorem sums_nil (s : Nat × Nat) : sums s [] = s := rfl

@[simp] theorem sums_cons (s : Nat × Nat) (x : UInt8) (xs : List UInt8) :
    sums s (x :: xs) = sums (step s x) xs := rfl

theorem sums_append (s : Nat × Nat) (xs ys : List UInt8) :
    sums s (xs ++ ys) = sums (sums s xs) ys := by
  simp [sums, List.foldl_append]

theorem step_lt_base (s : Nat × Nat) (x : UInt8) :
    (step s x).1 < BASE ∧ (step s x).2 < BASE := by
  dsimp [step, BASE]
  exact ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩

theorem sums_lt_base (s : Nat × Nat) (xs : List UInt8) (hs : s.1 < BASE ∧ s.2 < BASE) :
    (sums s xs).1 < BASE ∧ (sums s xs).2 < BASE := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    simp only [sums_cons]
    exact ih (step s x) (step_lt_base s x)

/-- Unreduced `Nat` step matching `zlib-ng`'s inner `ADLER_DO1` loop before `% BASE`. -/
def rawStep (s : Nat × Nat) (x : UInt8) : Nat × Nat :=
  let a' := s.1 + x.toNat
  (a', s.2 + a')

/-- Unreduced `Nat` sums over `xs`. -/
def rawSums (s : Nat × Nat) (xs : List UInt8) : Nat × Nat :=
  xs.foldl rawStep s

@[simp] theorem rawSums_nil (s : Nat × Nat) : rawSums s [] = s := rfl

@[simp] theorem rawSums_cons (s : Nat × Nat) (x : UInt8) (xs : List UInt8) :
    rawSums s (x :: xs) = rawSums (rawStep s x) xs := rfl

theorem rawSums_append (s : Nat × Nat) (xs ys : List UInt8) :
    rawSums s (xs ++ ys) = rawSums (rawSums s xs) ys := by
  simp [rawSums, List.foldl_append]

theorem rawStep_mod (s : Nat × Nat) (x : UInt8) :
    ((rawStep s x).1 % BASE, (rawStep s x).2 % BASE) = step (s.1 % BASE, s.2 % BASE) x := by
  dsimp [rawStep, step]
  apply Prod.ext <;> simp [Nat.add_mod]

theorem rawSums_mod (s : Nat × Nat) (xs : List UInt8) :
    ((rawSums s xs).1 % BASE, (rawSums s xs).2 % BASE) = sums (s.1 % BASE, s.2 % BASE) xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [rawSums_cons, sums_cons]
    rw [← rawStep_mod s x]
    exact ih (rawStep s x)

/-- Upper bound on unreduced `rawSums` after `xs.length` bytes (each `≤ 255`). -/
theorem rawSums_le (s : Nat × Nat) (xs : List UInt8) :
    (rawSums s xs).1 ≤ s.1 + 255 * xs.length ∧
    2 * (rawSums s xs).2 ≤ 2 * s.2 + 2 * (xs.length * s.1) + 255 * (xs.length * (xs.length + 1)) := by
  induction xs generalizing s with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [rawSums_cons, List.length_cons]
    have hx : x.toNat ≤ 255 := by
      have := x.toBitVec.isLt
      change x.toNat < 256 at this
      omega
    have ⟨h1, h2⟩ := ih (rawStep s x)
    dsimp [rawStep] at h1 h2 ⊢
    constructor
    · omega
    · have hd1 : xs.length * (s.1 + x.toNat) = xs.length * s.1 + xs.length * x.toNat :=
        Nat.left_distrib xs.length s.1 x.toNat
      have hd2 : (xs.length + 1) * s.1 = xs.length * s.1 + s.1 := by
        rw [Nat.add_mul, Nat.one_mul]
      have hd3 : (xs.length + 1) * (xs.length + 1 + 1) = xs.length * (xs.length + 1) + 2 * xs.length + 2 := by
        have hstep : (xs.length + 1) * (xs.length + 2) = xs.length * (xs.length + 1) + 2 * (xs.length + 1) := by
          rw [Nat.mul_comm (xs.length + 1) (xs.length + 2), Nat.add_mul]
        omega
      have hmulx : xs.length * x.toNat ≤ xs.length * 255 := Nat.mul_le_mul_left xs.length hx
      omega

/-- Exact 32-bit `UInt32` safety bound for `zlib-ng`: even with unreduced 16-bit halves `≤ 65535`,
accumulating up to `NMAX = 5552` bytes never reaches `2^32` (`max = 4,294,773,495 < 4,294,967,296`). -/
theorem rawSums_lt_u32 (s : Nat × Nat) (xs : List UInt8)
    (ha : s.1 ≤ 65535) (hb : s.2 ≤ 65535) (hlen : xs.length ≤ NMAX) :
    (rawSums s xs).1 < 2 ^ 32 ∧ (rawSums s xs).2 < 2 ^ 32 := by
  have ⟨h1, h2⟩ := rawSums_le s xs
  dsimp [NMAX] at hlen
  have hlen1 : xs.length * s.1 ≤ 5552 * 65535 := Nat.mul_le_mul hlen ha
  have hlen2 : xs.length * (xs.length + 1) ≤ 5552 * 5553 :=
    Nat.mul_le_mul hlen (by omega)
  omega

/-- Closed-form shift of `rawSums` from `(1, 0)` to arbitrary `(a1, b1)`:
`(rawSums (a1, b1) ys).1 + 1 = a1 + (rawSums (1, 0) ys).1` and
`(rawSums (a1, b1) ys).2 + ys.length = b1 + (rawSums (1, 0) ys).2 + ys.length * a1`. -/
theorem rawSums_shift (a1 b1 : Nat) (ys : List UInt8) :
    (rawSums (a1, b1) ys).1 + 1 = a1 + (rawSums (1, 0) ys).1 ∧
    (rawSums (a1, b1) ys).2 + ys.length = b1 + (rawSums (1, 0) ys).2 + ys.length * a1 := by
  suffices hgen : ∀ (u1 v1 u0 v0 k : Nat) (zs : List UInt8),
      u1 + 1 = a1 + u0 →
      v1 + k = b1 + v0 + k * a1 →
      (rawSums (u1, v1) zs).1 + 1 = a1 + (rawSums (u0, v0) zs).1 ∧
      (rawSums (u1, v1) zs).2 + (k + zs.length) =
        b1 + (rawSums (u0, v0) zs).2 + (k + zs.length) * a1 by
    simpa using hgen a1 b1 1 0 0 ys (by omega) (by omega)
  intro u1 v1 u0 v0 k zs hu hv
  induction zs generalizing u1 v1 u0 v0 k with
  | nil =>
    simp [hu, hv]
  | cons z zs ih =>
    simp only [rawSums_cons, rawStep, List.length_cons]
    have hu' : u1 + z.toNat + 1 = a1 + (u0 + z.toNat) := by omega
    have hv' : v1 + (u1 + z.toNat) + (k + 1) =
        b1 + (v0 + (u0 + z.toNat)) + (k + 1) * a1 := by
      rw [Nat.add_mul k 1 a1, Nat.one_mul]
      omega
    have ⟨r1, r2⟩ := ih (u1 + z.toNat) (v1 + (u1 + z.toNat)) (u0 + z.toNat) (v0 + (u0 + z.toNat)) (k + 1) hu' hv'
    refine ⟨r1, ?_⟩
    have hk : k + 1 + zs.length = k + (zs.length + 1) := by omega
    simpa [hk] using r2

/-- Modular combination theorem for `adler32_combine`:
given `(a1, b1) = sums (1, 0) xs` and `(a2, b2) = sums (1, 0) ys`,
`sums (1, 0) (xs ++ ys)` equals `((a1 + a2 + BASE - 1) % BASE, (((ys.length % BASE) * a1) % BASE + b1 + b2 + BASE - (ys.length % BASE)) % BASE)`. -/
theorem sums_combine (xs ys : List UInt8) :
    sums (1, 0) (xs ++ ys) =
      (((sums (1, 0) xs).1 + (sums (1, 0) ys).1 + BASE - 1) % BASE,
       ((((ys.length % BASE) * (sums (1, 0) xs).1) % BASE) +
         (sums (1, 0) xs).2 + (sums (1, 0) ys).2 + BASE - (ys.length % BASE)) % BASE) := by
  have ⟨ha1, hb1⟩ := sums_lt_base (1, 0) xs (by dsimp [BASE]; omega)
  have hmod1 : (sums (1, 0) xs).1 % BASE = (sums (1, 0) xs).1 := Nat.mod_eq_of_lt ha1
  have hmod2 : (sums (1, 0) xs).2 % BASE = (sums (1, 0) xs).2 := Nat.mod_eq_of_lt hb1
  let s1 := sums (1, 0) xs
  let s2 := sums (1, 0) ys
  rw [sums_append]
  have hrw1 : sums s1 ys = ((rawSums s1 ys).1 % BASE, (rawSums s1 ys).2 % BASE) := by
    have := rawSums_mod s1 ys
    simpa [s1, hmod1, hmod2] using this.symm
  have hrw0 : s2 = ((rawSums (1, 0) ys).1 % BASE, (rawSums (1, 0) ys).2 % BASE) := by
    have := rawSums_mod (1, 0) ys
    have h1 : 1 % BASE = 1 := rfl
    have h0 : 0 % BASE = 0 := rfl
    simpa [s2, h1, h0] using this.symm
  have ⟨hsh1, hsh2⟩ := rawSums_shift s1.1 s1.2 ys
  have heta : (s1.1, s1.2) = s1 := rfl
  rw [heta] at hsh1 hsh2
  have hrem_lt : ys.length % BASE < BASE := Nat.mod_lt _ (by dsimp [BASE]; omega)
  change sums s1 ys = ((s1.1 + s2.1 + BASE - 1) % BASE,
    ((((ys.length % BASE) * s1.1) % BASE) + s1.2 + s2.2 + BASE - (ys.length % BASE)) % BASE)
  rw [hrw1]
  apply Prod.ext
  · dsimp
    have hbase : BASE = 65521 := rfl
    have eq_mod : ((rawSums s1 ys).1 + BASE) % BASE = (s1.1 + (rawSums (1, 0) ys).1 + BASE - 1) % BASE := by
      congr 1
      omega
    have lhs_simp : ((rawSums s1 ys).1 + BASE) % BASE = (rawSums s1 ys).1 % BASE :=
      Nat.add_mod_right _ _
    rw [← lhs_simp, eq_mod]
    have hsub : s1.1 + (rawSums (1, 0) ys).1 + BASE - 1 = s1.1 + (rawSums (1, 0) ys).1 + (BASE - 1) := by
      omega
    have hsub2 : s1.1 + s2.1 + BASE - 1 = s1.1 + s2.1 + (BASE - 1) := by
      omega
    rw [hsub, hsub2, hrw0]
    simp [Nat.add_mod]
  · dsimp
    let rem := ys.length % BASE
    change (rawSums s1 ys).2 % BASE = (((rem * s1.1) % BASE) + s1.2 + s2.2 + BASE - rem) % BASE
    have hmod_eq :
        ((rawSums s1 ys).2 + ys.length) % BASE =
          (s1.2 + (rawSums (1, 0) ys).2 + ys.length * s1.1) % BASE := by
      rw [hsh2]
    have hadd_mod :
        ((rawSums s1 ys).2 + ys.length + (BASE - rem)) % BASE =
          (s1.2 + (rawSums (1, 0) ys).2 + ys.length * s1.1 + (BASE - rem)) % BASE := by
      calc
        ((rawSums s1 ys).2 + ys.length + (BASE - rem)) % BASE
            = (((rawSums s1 ys).2 + ys.length) % BASE + (BASE - rem) % BASE) % BASE := Nat.add_mod _ _ _
        _ = ((s1.2 + (rawSums (1, 0) ys).2 + ys.length * s1.1) % BASE + (BASE - rem) % BASE) % BASE := by
            rw [hmod_eq]
        _ = (s1.2 + (rawSums (1, 0) ys).2 + ys.length * s1.1 + (BASE - rem)) % BASE := (Nat.add_mod _ _ _).symm
    have hlhs : ((rawSums s1 ys).2 + ys.length + (BASE - rem)) % BASE = (rawSums s1 ys).2 % BASE := by
      have hdiv : ys.length + (BASE - rem) = BASE * (ys.length / BASE + 1) := by
        have hdm := Nat.div_add_mod ys.length BASE
        have hdist := Nat.mul_add BASE (ys.length / BASE) 1
        dsimp [rem] at hrem_lt ⊢
        omega
      rw [Nat.add_assoc, hdiv, Nat.add_mul_mod_self_left]
    rw [← hlhs, hadd_mod, hrw0]
    have hrhs_sub :
        (rem * s1.1) % BASE + s1.2 + (rawSums (1, 0) ys).2 % BASE + BASE - rem =
          s1.2 + (rawSums (1, 0) ys).2 % BASE + (rem * s1.1) % BASE + (BASE - rem) := by
      dsimp [rem] at hrem_lt ⊢
      omega
    rw [hrhs_sub]
    have hmul_mod : (ys.length * s1.1) % BASE = (rem * s1.1) % BASE := by
      dsimp [rem]
      simp [Nat.mul_mod]
    calc
      (s1.2 + (rawSums (1, 0) ys).2 + ys.length * s1.1 + (BASE - rem)) % BASE
          = (((s1.2 + (rawSums (1, 0) ys).2) % BASE + (ys.length * s1.1) % BASE) % BASE + (BASE - rem) % BASE) % BASE := by
            simp [Nat.add_mod]
      _ = (((s1.2 + (rawSums (1, 0) ys).2) % BASE + ((rem * s1.1) % BASE) % BASE) % BASE + (BASE - rem) % BASE) % BASE := by
            rw [hmul_mod, Nat.mod_mod]
      _ = (s1.2 + (rawSums (1, 0) ys).2 % BASE + (rem * s1.1) % BASE + (BASE - rem)) % BASE := by
            simp [Nat.add_mod]

end ZlibNgF.Math.Adler32
