import ZlibNgF.Proof.«inftrees.c.fill»
import ZlibNgF.Proof.«inftrees.c.rev»
import ZlibNgF.Math.InftreesCount

/-!
# The state of the table-filling loop of `zng_inflate_table` (`ZlibNgF`)

`Setup` holds what is fixed during the loop: the caller's heap and state block, the sorted `work` array `W`, the
initial length counts `c0`, the longest length `mx`, the root bits `root` and the table room `bnd`. `St` is the
loop invariant. `K` is the canonical code of the current symbol, left-aligned in 16 bits (the Kraft weight of the
symbols before it, a code of length `L` weighing `2 ^ (16 - L)`); `rhuff = K` and `huff` is `K` reversed. The root
table is `table[0 .. 2 ^ root)`; each sub-table covers the codes whose top `root` bits are one block
`P = K / 2 ^ (16 - root)` and has `2 ^ curr` entries, with `curr` chosen so that every code of that block has
length at most `root + curr` (`Geo`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Math.BitReverse ZlibNgF.Math.InftreesCount

/-! ## Arithmetic of the loop -/

theorem u32_shl_one {k : UInt32} (hk : k.toNat < 32) : ((1 : UInt32) <<< k).toNat = 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
  have : (1 : UInt32).toNat = 1 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)

theorem u32_shr {x k : UInt32} (hk : k.toNat < 32) : (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem u32_and_mask {x m : UInt32} {r : Nat} (hm : m.toNat = 2 ^ r - 1) : (x &&& m).toNat = x.toNat % 2 ^ r := by
  rw [UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem u32_sub {x y : UInt32} (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)

theorem u32_add {x y : UInt32} (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

/-- The low `root` bits of the reversed code are the reversed block number. -/
theorem rev16_mod {K r : Nat} (hr : r ≤ 16) :
    rev 16 K % 2 ^ r = rev r (K / 2 ^ (16 - r)) := by
  have e := rev_add_mul (16 - r) r (K % 2 ^ (16 - r)) (K / 2 ^ (16 - r)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [show 16 - r + r = 16 by omega, Nat.mod_add_div' K (2 ^ (16 - r))] at e
  rw [e, Nat.mul_add_mod_of_lt (rev_lt _ _)]

/-- The reversed code of a length-`len` code is below `2 ^ len`. -/
theorem rev16_lt {K len : Nat} (hlen : len ≤ 16) (hd : 2 ^ (16 - len) ∣ K) : rev 16 K < 2 ^ len := by
  obtain ⟨A, rfl⟩ := hd
  have := rev_mul_pow (16 - len) len A
  rw [show 16 - len + len = 16 by omega, Nat.mul_comm] at this
  rw [this]
  exact rev_lt _ _

/-! ## The setup -/

/-- What is fixed during the table-filling loop. -/
structure Setup where
  h0 : Heap
  b : Nat
  s : InflateState
  W : Array UInt16
  lo : Nat
  codes : Nat
  off : Nat
  type : UInt32
  c0 : Nat → Nat
  mx : Nat
  root : Nat
  bnd : Nat

/-- `lens[j]` as a number. -/
def Setup.lensv (S : Setup) (j : Nat) : Nat := (S.s.lens[S.lo + j]!).toNat

/-- The count of length `L` in a count array. -/
def cnt (a : Array UInt16) (L : Nat) : Nat := (a[L]!).toNat

/-- The facts the table-filling loop relies on. -/
structure Setup.OK (S : Setup) : Prop where
  live : LiveSt S.h0 S.b S.s
  lens_size : S.lo + S.codes ≤ S.s.lens.size
  W_size : S.W.size = S.s.work.size
  n_le : nsum S.c0 15 ≤ S.W.size
  sorted : ∀ L, 1 ≤ L → L ≤ 15 → ∀ j, nsum S.c0 (L - 1) ≤ j → j < nsum S.c0 L →
    (S.W[j]!).toNat < S.codes ∧ S.lensv (S.W[j]!).toNat = L
  mx1 : 1 ≤ S.mx
  mx15 : S.mx ≤ 15
  c0mx : 1 ≤ S.c0 S.mx
  above : ∀ L, S.mx < L → L ≤ 15 → S.c0 L = 0
  root1 : 1 ≤ S.root
  rootmx : S.root ≤ S.mx
  kraft : wsum S.c0 15 ≤ 2 ^ 16
  complete : wsum S.c0 15 = 2 ^ 16 ∨ (S.mx = 1 ∧ S.c0 1 = 1)
  bnd_root : 2 ^ S.root ≤ S.bnd
  bnd_size : S.off + S.bnd ≤ S.s.codes.size
  bnd_lt : S.bnd < 2 ^ 16
  codes_lt : S.s.codes.size < 2 ^ 63
  kind : (S.type = CODES ∧ S.mx ≤ S.root ∧ S.codes ≤ 19) ∨ (S.type = LENS ∧ S.bnd = 1332 ∧ S.codes ≤ 288) ∨
    (S.type = DISTS ∧ S.bnd = 592 ∧ S.codes ≤ 32)

/-- The tables: the root table alone (`drop = 0`), or a sub-table of `2 ^ curr` entries at `next` for the block
`P` of the `root`-bit prefix. `inb`: `K` lies in block `P`. -/
def Geo (S : Setup) (t : TL) (c : Nat → Nat) (K len : Nat) (inb : Bool) : Prop :=
  (t.drop = 0 ∧ t.curr.toNat = S.root ∧ t.next = .ref (.codes S.b) S.off ∧ t.used.toNat = 2 ^ S.root ∧
    t.low = 0xFFFFFFFF ∧ (inb = true → len ≤ S.root)) ∨
  (t.drop.toNat = S.root ∧ S.root < len ∧ 1 ≤ t.curr.toNat ∧ S.root + t.curr.toNat ≤ 15 ∧
    ∃ nx P, t.next = .ref (.codes S.b) (S.off + nx) ∧ 2 ^ S.root ≤ nx ∧ nx + 2 ^ t.curr.toNat = t.used.toNat ∧
      P < 2 ^ S.root ∧ t.low.toNat = rev S.root P ∧
      (K / 2 ^ (16 - S.root) = P → (S.mx ≤ S.root + t.curr.toNat ∨
          (P + 1) * 2 ^ (16 - S.root) ≤ K + wsum c (S.root + t.curr.toNat))) ∧
      (inb = true → K / 2 ^ (16 - S.root) = P))

/-- The invariant of the table-filling loop for the state `t`, the `codes` array `C` and the code `K`. -/
structure St (S : Setup) (t : TL) (C : Array Code) (K : Nat) (inb : Bool) : Prop where
  ret : t.ret = none
  csize : C.size = S.s.codes.size
  frame : ∀ i, ¬ (S.off ≤ i ∧ i < S.off + t.used.toNat) → C[i]? = S.s.codes[i]?
  used_bnd : t.used.toNat ≤ S.bnd
  count_size : t.count.size = 16
  len_lo : 1 ≤ t.len.toNat
  len_hi : t.len.toNat ≤ S.mx
  below : ∀ L, 1 ≤ L → L < t.len.toNat → cnt t.count L = 0
  above : ∀ L, t.len.toNat < L → L ≤ 15 → cnt t.count L = S.c0 L
  cur_pos : 1 ≤ cnt t.count t.len.toNat
  cur_le : cnt t.count t.len.toNat ≤ S.c0 t.len.toNat
  sym : t.sym.toNat + cnt t.count t.len.toNat = nsum S.c0 t.len.toNat
  rhuff : t.rhuff.toNat = K
  kraft : K + wsum (cnt t.count) 15 = wsum S.c0 15
  dvd : 2 ^ (16 - t.len.toNat) ∣ K
  huff : t.huff.toNat = rev 16 K
  geo : Geo S t (cnt t.count) K t.len.toNat inb

/-- The loop state at the start of a trip. -/
def MI (S : Setup) (t : TL) (h : Heap) : Prop := ∃ C K, h = setCW S.h0 S.b S.s C S.W ∧ St S t C K true

/-- The loop state after the last code (`ret = 0`). -/
structure Fin0 (S : Setup) (t : TL) (C : Array Code) : Prop where
  ret : t.ret = some 0
  csize : C.size = S.s.codes.size
  frame : ∀ i, ¬ (S.off ≤ i ∧ i < S.off + t.used.toNat) → C[i]? = S.s.codes[i]?
  used_bnd : t.used.toNat ≤ S.bnd
  geo : (t.drop = 0 ∧ t.next = .ref (.codes S.b) S.off ∧ t.used.toNat = 2 ^ S.root) ∨
    (t.drop.toNat = S.root ∧ ∃ nx, t.next = .ref (.codes S.b) (S.off + nx) ∧ nx + 2 ^ t.curr.toNat = t.used.toNat)
  huff : (wsum S.c0 15 = 2 ^ 16 ∧ t.huff = 0) ∨
    (S.mx = 1 ∧ t.drop = 0 ∧ t.huff.toNat = 1 ∧ S.root = 1 ∧ t.next = .ref (.codes S.b) S.off ∧
      t.used.toNat = 2)

/-- The loop state after the room check failed (`ret = 1`). -/
structure Fin1 (S : Setup) (t : TL) (C : Array Code) : Prop where
  ret : t.ret = some 1
  csize : C.size = S.s.codes.size
  frame : ∀ i, ¬ (S.off ≤ i ∧ i < S.off + S.bnd) → C[i]? = S.s.codes[i]?

/-- The result of one trip. -/
def Trip (S : Setup) (t : TL) (t' : TL) (h' : Heap) : Prop :=
  (MI S t' h' ∧ t.sym.toNat < t'.sym.toNat ∧ t'.sym.toNat ≤ nsum S.c0 15) ∨
  (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin0 S t' C) ∨ (∃ C, h' = setCW S.h0 S.b S.s C S.W ∧ Fin1 S t' C)

/-- In the root table every code is at most `root` long; in a sub-table at most `root + curr`. -/
theorem St.len_le {S : Setup} {t : TL} {C : Array Code} {K : Nat} (hs : St S t C K true) :
    t.len.toNat - t.drop.toNat ≤ t.curr.toNat := by
  rcases hs.geo with ⟨hd, hc, -, -, -, hl⟩ | ⟨hd, hr, -, -, nx, P, -, -, -, -, -, hsub, hin⟩
  · rw [hd, hc]; have := hl rfl; simp; omega
  · rw [hd]
    have hP := hin rfl
    rcases hsub hP with h1 | h1
    · have := hs.len_hi; omega
    · apply Classical.byContradiction
      intro hlt
      have hz : wsum (cnt t.count) (S.root + t.curr.toNat) = 0 :=
        wsum_eq_zero (fun L h1 h2 => hs.below L h1 (by omega))
      rw [hz, Nat.add_zero] at h1
      have := Nat.lt_div_mul_add (a := K) (Nat.two_pow_pos (16 - S.root))
      rw [hP] at this
      have : (P + 1) * 2 ^ (16 - S.root) = P * 2 ^ (16 - S.root) + 2 ^ (16 - S.root) := by
        rw [Nat.add_mul, Nat.one_mul]
      omega

end ZlibNgF.Proof.Inftrees
