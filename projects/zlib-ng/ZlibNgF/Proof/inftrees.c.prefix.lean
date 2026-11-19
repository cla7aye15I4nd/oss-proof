import ZlibNgF.Proof.«inftrees.c.entry»
import ZlibNgF.Math.BitReverse
import ZlibNgF.Math.InftreesCount

/-!
# The prefix property of a decoding table (`ZlibNgF`)

`Lvl a s k`: the level `a[s, s + 2^k)` of a decoding table is a prefix code: the code bits of an entry that does not
send the decoder to `BAD` are at most `k`, and every index with the same low code-bits bits has the same code bits.
`Rep a o n dist`: the root table and every sub-table it links to are prefix codes. `inflateBack` needs it to hold
fewer than 8 bits after a symbol (`Proof/infback.c.decode.lean`).

For a table built by `zng_inflate_table`, the code bits of a slot are a function of its position in the canonical
code: the slot `x` of a level with `d` dropped bits, `k` index bits and prefix base `Pb` covers the code interval
starting at `Pb + rev k x * 2 ^ (16 - d - k)` (16-bit, left aligned); the codes of length `L` fill
`[wsum c (L - 1), wsum c L)`, so the code bits are `L - d` (`PosCB`, cut at `d + k` for links). `lvl_of_pos` turns
that into `Lvl`: two indices with the same low `L - d` bits lie in one aligned interval of `2 ^ (16 - L)`, inside the
interval of the codes of length `L`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNg.InflateP
open ZlibNgF.Proof.InflateTab (linkTest)
open ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

/-! ## The prefix property -/

/-- An entry that does not send the decoder to `BAD`: not invalid (`op & 64`), or end of block (`op & 32`). -/
def Live (e : Code) : Prop := e.op &&& 64 = 0 ∨ e.op &&& 32 ≠ 0

instance (e : Code) : Decidable (Live e) := inferInstanceAs (Decidable (_ ∨ _))

/-- One level `a[s, s + 2^k)` of a decoding table is a prefix code: the code bits of an entry that does not send the
decoder to `BAD` are at most `k`, and every index with the same low code-bits bits has the same code bits. -/
def Lvl (a : Array Code) (s k : Nat) : Prop :=
  ∀ x x', x < 2 ^ k → x' < 2 ^ k → Live a[s + x']! → (CODE_BITS a[s + x']!).toNat ≤ k ∧
    (x % 2 ^ (CODE_BITS a[s + x']!).toNat = x' % 2 ^ (CODE_BITS a[s + x']!).toNat →
      CODE_BITS a[s + x]! = CODE_BITS a[s + x']!)

/-- `Lvl` for every entry, live or not. -/
def LvlAll (a : Array Code) (s k : Nat) : Prop :=
  ∀ x x', x < 2 ^ k → x' < 2 ^ k → (CODE_BITS a[s + x']!).toNat ≤ k ∧
    (x % 2 ^ (CODE_BITS a[s + x']!).toNat = x' % 2 ^ (CODE_BITS a[s + x']!).toNat →
      CODE_BITS a[s + x]! = CODE_BITS a[s + x']!)

theorem LvlAll.lvl {a : Array Code} {s k : Nat} (h : LvlAll a s k) : Lvl a s k :=
  fun x x' hx hx' _ => h x x' hx hx'

/-- The root table `a[o, o + 2^n)` and every sub-table it links to are prefix codes. -/
def Rep (a : Array Code) (o n : Nat) (dist : Bool) : Prop :=
  Lvl a o n ∧ ∀ j, j < 2 ^ n → linkTest dist a[o + j]! = true →
    Lvl a (o + a[o + j]!.val.toNat) a[o + j]!.op.toNat

/-- A level depends only on its own entries. -/
theorem lvl_congr {a a' : Array Code} {s k : Nat} (h : ∀ x, x < 2 ^ k → a'[s + x]! = a[s + x]!)
    (hl : Lvl a s k) : Lvl a' s k := by
  intro x x' hx hx' hv
  rw [h x' hx'] at hv ⊢
  rw [h x hx]
  exact hl x x' hx hx' hv

/-! ## Code bits from the code position -/

/-- The code bits `cb` of the slot at code position `v` in a level whose entries take at most `m` bits after the
dropped ones: `min L m` for the length `L` of the code whose interval `[wsum c (L - 1), wsum c L)` holds `v`, or `m`
past the last code (the invalid-code marker of an incomplete code). -/
def PosCB (c : Nat → Nat) (v m cb : Nat) : Prop :=
  (∃ L, 1 ≤ L ∧ L ≤ 15 ∧ wsum c (L - 1) ≤ v ∧ v < wsum c L ∧ cb = min L m) ∨ (wsum c 15 ≤ v ∧ cb = m)

theorem len_unique {c : Nat → Nat} {L L' v : Nat} (h1 : 1 ≤ L) (h1' : 1 ≤ L') (a1 : wsum c (L - 1) ≤ v)
    (a2 : v < wsum c L) (b1 : wsum c (L' - 1) ≤ v) (b2 : v < wsum c L') : L = L' := by
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := wsum_mono c (show L ≤ L' - 1 by omega); omega
  · have := wsum_mono c (show L' ≤ L - 1 by omega); omega

/-- A position in the same aligned block of `D` as one in `[w1, w2)` (multiples of `D`) is in `[w1, w2)`. -/
theorem blk_in {D w1 w2 v v' : Nat} (hD : 0 < D) (d1 : D ∣ w1) (d2 : D ∣ w2) (h1 : w1 ≤ v') (h2 : v' < w2)
    (he : v / D = v' / D) : w1 ≤ v ∧ v < w2 := by
  obtain ⟨a1, rfl⟩ := d1
  obtain ⟨a2, rfl⟩ := d2
  have e1 : a1 ≤ v' / D := (Nat.le_div_iff_mul_le hD).2 (by rw [Nat.mul_comm]; exact h1)
  have e2 : v' / D < a2 := (Nat.div_lt_iff_lt_mul hD).2 (by rw [Nat.mul_comm]; exact h2)
  rw [← he] at e1 e2
  constructor
  · have := (Nat.le_div_iff_mul_le hD).1 e1; rw [Nat.mul_comm]; exact this
  · have := (Nat.div_lt_iff_lt_mul hD).1 e2; rw [Nat.mul_comm]; exact this

/-- The position of index `y`, in units of `2 ^ (16 - L)`: the prefix base and the reversed low `L - d` bits. -/
theorem pos_div {Pb d k L y : Nat} (hdk : d + k ≤ 16) (hdL : d ≤ L) (hLk : L ≤ d + k) (hPb : 2 ^ (16 - d) ∣ Pb) :
    (Pb + rev k y * 2 ^ (16 - d - k)) / 2 ^ (16 - L) = Pb / 2 ^ (16 - L) + rev (L - d) (y % 2 ^ (L - d)) := by
  have hy := Nat.mod_lt y (Nat.two_pow_pos (L - d))
  have e := rev_add_mul (L - d) (k - (L - d)) (y % 2 ^ (L - d)) (y / 2 ^ (L - d)) hy
  rw [show L - d + (k - (L - d)) = k by omega, Nat.mod_add_div'] at e
  have hR := rev_lt (k - (L - d)) (y / 2 ^ (L - d))
  generalize rev (L - d) (y % 2 ^ (L - d)) = A at e ⊢
  generalize rev (k - (L - d)) (y / 2 ^ (L - d)) = R at e hR
  have hFE : 2 ^ (k - (L - d)) * 2 ^ (16 - d - k) = 2 ^ (16 - L) := by rw [← Nat.pow_add]; congr 1; omega
  have hRE : R * 2 ^ (16 - d - k) < 2 ^ (16 - L) := by
    rw [← hFE]; exact Nat.mul_lt_mul_of_pos_right hR (Nat.two_pow_pos _)
  have hPb' : 2 ^ (16 - L) ∣ Pb := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hPb
  obtain ⟨Q, rfl⟩ := hPb'
  have hD := Nat.two_pow_pos (16 - L)
  rw [e, Nat.add_mul, Nat.mul_assoc, hFE]
  rw [show 2 ^ (16 - L) * Q + (A * 2 ^ (16 - L) + R * 2 ^ (16 - d - k)) =
    R * 2 ^ (16 - d - k) + (Q + A) * 2 ^ (16 - L) by rw [Nat.add_mul]; ac_rfl]
  rw [Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hRE, Nat.mul_div_cancel_left _ hD]
  omega

/-- A level whose every slot has the code bits of its code position (`PosCB`) is a prefix code. -/
theorem lvlAll_of_pos {a : Array Code} {s k d Pb : Nat} {c : Nat → Nat} (hdk : d + k ≤ 16) (hPb : 2 ^ (16 - d) ∣ Pb)
    (hall : ∀ x, x < 2 ^ k → PosCB c (Pb + rev k x * 2 ^ (16 - d - k)) (d + k) ((CODE_BITS a[s + x]!).toNat + d)) :
    LvlAll a s k := by
  intro x x' hx hx'
  generalize hcb' : (CODE_BITS a[s + x']!).toNat = cb' at *
  have heq : ∀ y, y = x' → CODE_BITS a[s + y]! = CODE_BITS a[s + x']! := fun _ e => by rw [e]
  rcases hall x' hx' with ⟨L, hL1, hL15, h1, h2, hcb⟩ | ⟨h1, hcb⟩
  · refine ⟨by omega, fun hm => ?_⟩
    by_cases hLk : d + k ≤ L
    · have e : cb' = k := by omega
      rw [e, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at hm
      exact heq x hm
    · have hdL : d ≤ L := by omega
      have e : cb' = L - d := by omega
      rw [e] at hm
      have p1 := pos_div (y := x) hdk hdL (by omega) hPb
      have p2 := pos_div (y := x') hdk hdL (by omega) hPb
      rw [hm, ← p2] at p1
      have dv1 : 2 ^ (16 - L) ∣ wsum c (L - 1) :=
        Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (wsum_dvd c (L - 1) (by omega))
      have dv2 : 2 ^ (16 - L) ∣ wsum c L := wsum_dvd c L (by omega)
      obtain ⟨g1, g2⟩ := blk_in (Nat.two_pow_pos _) dv1 dv2 h1 h2 p1
      rcases hall x hx with ⟨L2, hL21, -, k1, k2, hcb2⟩ | ⟨k1, -⟩
      · have := len_unique hL1 hL21 g1 g2 k1 k2
        subst this
        apply UInt32.toNat_inj.mp
        omega
      · have := wsum_mono c (show L ≤ 15 from hL15); omega
  · refine ⟨by omega, fun hm => ?_⟩
    have e : cb' = k := by omega
    rw [e, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at hm
    exact heq x hm

theorem lvl_of_pos {a : Array Code} {s k d Pb : Nat} {c : Nat → Nat} (hdk : d + k ≤ 16) (hPb : 2 ^ (16 - d) ∣ Pb)
    (hall : ∀ x, x < 2 ^ k → PosCB c (Pb + rev k x * 2 ^ (16 - d - k)) (d + k) ((CODE_BITS a[s + x]!).toNat + d)) :
    Lvl a s k :=
  (lvlAll_of_pos hdk hPb hall).lvl

/-- The `j`-th replicated slot of the code `K` of length `L` in a level with `c` index bits after `d` dropped
bits, for the block `P` of the top `d` bits, has its code position in `[K, K + 2 ^ (16 - L))`. -/
theorem pos_of_slot {d c L P K j : Nat} (hdc : d + c ≤ 16) (hdL : d < L) (hLc : L ≤ d + c)
    (hdvd : 2 ^ (16 - L) ∣ K) (hP : K / 2 ^ (16 - d) = P) :
    K ≤ P * 2 ^ (16 - d) + rev c (rev 16 K / 2 ^ d + j * 2 ^ (L - d)) * 2 ^ (16 - d - c) ∧
    P * 2 ^ (16 - d) + rev c (rev 16 K / 2 ^ d + j * 2 ^ (L - d)) * 2 ^ (16 - d - c) < K + 2 ^ (16 - L) := by
  have hG : 2 ^ (16 - d) = 2 ^ (16 - L) * 2 ^ (L - d) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hKd := Nat.div_add_mod K (2 ^ (16 - d))
  rw [hP] at hKd
  have hDG : 2 ^ (16 - L) ∣ 2 ^ (16 - d) := Nat.pow_dvd_pow 2 (by omega)
  have hDR : 2 ^ (16 - L) ∣ K % 2 ^ (16 - d) := (Nat.dvd_mod_iff hDG).2 hdvd
  obtain ⟨x, hx⟩ := hDR
  have hRlt := Nat.mod_lt K (Nat.two_pow_pos (16 - d))
  have hxlt : x < 2 ^ (L - d) := by
    rw [hx, hG] at hRlt
    exact Nat.lt_of_mul_lt_mul_left hRlt
  have hK2 : K = (x + P * 2 ^ (L - d)) * 2 ^ (16 - L) := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ (L - d)), ← hG, Nat.mul_comm x, Nat.mul_comm P]; omega
  have hrev : rev 16 K = rev (L - d) x * 2 ^ d + rev d P := by
    have e := rev_mul_pow (16 - L) L (x + P * 2 ^ (L - d))
    rw [show 16 - L + L = 16 by omega] at e
    rw [hK2, e]
    have e2 := rev_add_mul (L - d) d x P hxlt
    rw [show L - d + d = L by omega] at e2
    exact e2
  have hdiv : rev 16 K / 2 ^ d = rev (L - d) x := by
    rw [hrev, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt (rev_lt d P), Nat.add_zero]
  have e3 := rev_add_mul (L - d) (c - (L - d)) (rev (L - d) x) j (rev_lt _ _)
  rw [show L - d + (c - (L - d)) = c by omega, rev_rev, Nat.mod_eq_of_lt hxlt] at e3
  rw [hdiv, e3]
  have hR := rev_lt (c - (L - d)) j
  generalize rev (c - (L - d)) j = R at hR ⊢
  have hFE : 2 ^ (c - (L - d)) * 2 ^ (16 - d - c) = 2 ^ (16 - L) := by rw [← Nat.pow_add]; congr 1; omega
  have hRE : R * 2 ^ (16 - d - c) < 2 ^ (16 - L) := by
    rw [← hFE]; exact Nat.mul_lt_mul_of_pos_right hR (Nat.two_pow_pos _)
  have hx2 : (x * 2 ^ (c - (L - d)) + R) * 2 ^ (16 - d - c) = x * 2 ^ (16 - L) + R * 2 ^ (16 - d - c) := by
    rw [Nat.add_mul, Nat.mul_assoc, hFE]
  rw [hx2]
  have hK3 : K = P * 2 ^ (16 - d) + x * 2 ^ (16 - L) := by
    rw [Nat.mul_comm P, Nat.mul_comm x]; omega
  omega

end ZlibNgF.Proof.InfbackLoop
