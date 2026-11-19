import ZlibNgF.Proof.«inflate_p.h.chunkcopy_safe»

/-!
# `inflate_fast`: tables, bit operations, loops (`ZlibNgF`)

* `FastTableOK`: what `inflate_fast_c` / `inflate_fast_safe_c` need of the decoding tables `lcode` / `dcode` (root
  sizes `lenbits` / `distbits`). It is stated entry by entry for every entry the decoder can reach: a root entry
  (index `< 2 ^ root`), or a second-level entry `here.val + k` (`k < 2 ^ here.op`) of a root link.
* Single-step lemmas for `REFILL`, `DROPBITS`, `BITS`, `EXTRA_BITS` and the table lookups.
* `sat_cdoWhile` (a `do … while` over a changing heap with a measure) and `sat_cwhile_rank` (a `while` whose
  termination is a ghost rank carried by the invariant).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastBase
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)

/-! ## The table predicate -/

/-- `op & 16`: a length or distance base. -/
def Base (e : Code) : Prop := e.op.toUInt32 &&& 16 ≠ 0

/-- A link to a second-level table in the length/literal table (`op != 0`, no base, `(op & 64) == 0`). -/
def LenLink (e : Code) : Prop := e.op ≠ 0 ∧ e.op.toUInt32 &&& 16 = 0 ∧ e.op.toUInt32 &&& 64 = 0

/-- A link to a second-level table in the distance table (no base, `(op & 64) == 0`). -/
def DistLink (e : Code) : Prop := e.op.toUInt32 &&& 16 = 0 ∧ e.op.toUInt32 &&& 64 = 0

/-- A length/literal entry reached after `pre` bits of a root link (`pre = 0` for a root entry): a literal takes at most
15 bits in all, any other entry at most 20 (a code of at most 15 bits and at most 5 extra bits); a length base
`val + extra` lies in `[1, 258]` for every value of its extra bits; every entry takes at least one bit in all. -/
def LenEnt (pre : Nat) (e : Code) : Prop :=
  (e.op = 0 → pre + e.bits.toNat ≤ 15) ∧ (e.op ≠ 0 → pre + e.bits.toNat ≤ 20) ∧
  (Base e → 1 ≤ e.val.toNat ∧ e.val.toNat + 2 ^ (e.bits.toNat - e.op.toNat % 16) ≤ 259) ∧
  1 ≤ pre + e.bits.toNat

/-- A distance entry reached after `pre` bits of a root link: at most 28 bits in all (a code of at most 15 bits and at
most 13 extra bits), and a distance base is at least 1. -/
def DistEnt (pre : Nat) (e : Code) : Prop :=
  pre + e.bits.toNat ≤ 28 ∧ (Base e → 1 ≤ e.val.toNat)

/-- A table at offset `o` of the array `T` with `2 ^ rb` root entries satisfying `Ent 0`; a root `Link` has
`op < 16` and `2 ^ op` second-level entries at `o + val`, each satisfying `Ent bits` and not a link. -/
def Tab (T : Array Code) (o rb : Nat) (Ent : Nat → Code → Prop) (Link : Code → Prop) : Prop :=
  o + 2 ^ rb ≤ T.size ∧ ∀ k, k < 2 ^ rb →
    Ent 0 T[o + k]! ∧ (Link T[o + k]! → T[o + k]!.op.toNat < 16 ∧
      o + T[o + k]!.val.toNat + 2 ^ T[o + k]!.op.toNat ≤ T.size ∧
      ∀ j, j < 2 ^ T[o + k]!.op.toNat →
        Ent T[o + k]!.bits.toNat T[o + T[o + k]!.val.toNat + j]! ∧ ¬ Link T[o + T[o + k]!.val.toNat + j]!)

/-- **What `inflate_fast` needs of its decoding tables.** `lcode` and `dcode` point into code arrays of the heap;
`lenbits`, `distbits < 32` (so the masks `(1U << bits) - 1` are defined); every reachable entry satisfies `LenEnt` /
`DistEnt`, root links lead to in-bounds second-level tables of non-links. -/
def FastTableOK (H : Heap) (lcode : CodePtr) (lenbits : UInt32) (dcode : CodePtr) (distbits : UInt32) : Prop :=
  lenbits.toNat < 32 ∧ distbits.toNat < 32 ∧
  (∃ r o T, lcode = .ref r o ∧ Space.get H r = some T ∧ Tab T o lenbits.toNat LenEnt LenLink) ∧
  (∃ r o T, dcode = .ref r o ∧ Space.get H r = some T ∧ Tab T o distbits.toNat DistEnt DistLink)

/-! ## Arithmetic facts by evaluation -/

theorem or56_tab : ∀ n, n < 64 → ((UInt8.ofNat n) ||| 56).toNat = 56 + n % 8 := by decide
theorem xor63_tab : ∀ n, n < 64 → ((63 ^^^ (UInt8.ofNat n).toUInt32) >>> 3).toNat = 7 - n / 8 := by decide
theorem shl32_tab : ∀ n, n < 32 → (((1 : UInt32) <<< UInt32.ofNat n) - 1).toNat = 2 ^ n - 1 := by decide

theorem or56 (x : UInt8) (h : x.toNat < 64) : (x ||| 56).toNat = 56 + x.toNat % 8 := by
  have := or56_tab x.toNat h; simpa using this

theorem xor63 (x : UInt8) (h : x.toNat < 64) : ((63 ^^^ x.toUInt32) >>> 3).toNat = 7 - x.toNat / 8 := by
  have := xor63_tab x.toNat h; simpa using this

theorem mask32 (n : UInt32) (h : n.toNat < 32) : (((1 : UInt32) <<< n) - 1).toNat = 2 ^ n.toNat - 1 := by
  have := shl32_tab n.toNat h; simpa using this

theorem and_mask_lt (x : UInt64) (n : UInt32) (h : n.toNat < 32) :
    (x &&& (((1 : UInt32) <<< n) - 1).toUInt64).toNat < 2 ^ n.toNat := by
  rw [UInt64.toNat_and, UInt32.toNat_toUInt64, mask32 n h]
  have := Nat.and_le_right (n := x.toNat) (m := 2 ^ n.toNat - 1)
  have := Nat.one_le_two_pow (n := n.toNat)
  omega

/-! ## Generic pointer steps -/

theorem sat_add_g {R T : Type} [Space Heap R T] {H : Heap} {r : R} {a : Array T} {off : Nat}
    (hb : Space.get H r = some a) (ho : off ≤ a.size) (k : Int) (m : Nat) (hm : (off : Int) + k = m)
    (hmN : m ≤ a.size) : Sat H (Ptr.add (.ref r off) k) (fun p H' => p = .ref r m ∧ H' = H) := by
  have hc : off ≤ a.size ∧ 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int) := by omega
  have e : ((off : Int) + k).toNat = m := by omega
  exact ⟨_, _, by simp only [Ptr.add, hb, hc, and_self, ↓reduceIte, e], rfl, rfl⟩

theorem sat_index_code {H : Heap} {r : CodeRef} {T : Array Code} {o : Nat} (hb : Space.get H r = some T)
    (k : Nat) (hk : o + k < T.size) :
    Sat H (Ptr.index (.ref r o) (Int.ofNat k) : M Code) (fun e H' => e = T[o + k]! ∧ H' = H) := by
  unfold Ptr.index
  refine Sat.bind (Sat.mono (sat_add_g hb (by omega) (Int.ofNat k) (o + k) (by simp) (by omega)) ?_)
  rintro p H' ⟨rfl, rfl⟩
  refine ⟨T[o + k]!, H', ?_, rfl, rfl⟩
  simp [Ptr.load, hb, hk]

/-! ## Loops -/

/-- `do body while (cond)` over a changing heap, with a decreasing measure. -/
theorem sat_cdoWhile {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)} (I : σ → Heap → Prop) (μ : σ → Nat)
    (Q : σ → Heap → Prop)
    (hstep : ∀ s H, I s H → Sat H (body s) (fun s1 H1 => Sat H1 (cond s1) (fun cs H2 =>
      (cs.1 = true → I cs.2 H2 ∧ μ cs.2 < μ s) ∧ (cs.1 = false → Q cs.2 H2))))
    {s : σ} {H : Heap} (hI : I s H) (hμ : μ s < fuel) : Sat H (cdoWhile body cond s) Q := by
  unfold cdoWhile
  suffices ∀ n s H, I s H → μ s < n → Sat H (cdoWhile.go body cond n s) Q from this _ s H hI hμ
  intro n
  induction n with
  | zero => intro s _ _ hlt; omega
  | succ n ih =>
    intro s H hI hlt
    obtain ⟨s1, H1, eb, ⟨⟨c, s2⟩, H2, ec, ht, hf⟩⟩ := hstep s H hI
    cases c with
    | false => exact ⟨s2, H2, by simp [cdoWhile.go, bind_app, eb, ec], hf rfl⟩
    | true =>
      obtain ⟨hI2, hμ2⟩ := ht rfl
      simp only at hI2 hμ2
      obtain ⟨s', H', eg, q⟩ := ih s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cdoWhile.go, bind_app, eb, ec, eg], q⟩

/-- `while (cond) body` whose termination is a ghost rank `n` carried by the invariant. -/
theorem sat_cwhile_rank {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ} (I : Nat → σ → Heap → Prop)
    (Q : σ → Heap → Prop)
    (hstep : ∀ n s H, I n s H → Sat H (cond s) (fun cs H1 =>
      (cs.1 = true → Sat H1 (body cs.2) (fun s2 H2 => ∃ m, m < n ∧ I m s2 H2)) ∧ (cs.1 = false → Q cs.2 H1)))
    {n : Nat} {s : σ} {H : Heap} (hI : I n s H) (hn : n < fuel) : Sat H (cwhile cond body s) Q := by
  unfold cwhile
  suffices ∀ k n s H, I n s H → n < k → Sat H (cwhile.go cond body k s) Q from this _ n s H hI hn
  intro k
  induction k with
  | zero => intro n s _ _ hlt; omega
  | succ k ih =>
    intro n s H hI hlt
    obtain ⟨⟨c, s1⟩, H1, ec, ht, hf⟩ := hstep n s H hI
    cases c with
    | false => exact ⟨s1, H1, by simp [cwhile.go, bind_app, ec], hf rfl⟩
    | true =>
      obtain ⟨s2, H2, eb, m, hm, hI2⟩ := ht rfl
      obtain ⟨s', H', eg, q⟩ := ih m s2 H2 hI2 (by omega)
      exact ⟨s', H', by simp [cwhile.go, bind_app, ec, eb, eg], q⟩

/-! ## Bit-buffer steps -/

/-- `REFILL()` with 8 readable input bytes at `in` and `bits < 64`: `in` advances by `7 - bits / 8` bytes and `bits`
becomes `56 + bits % 8`. -/
theorem sat_REFILL {H : Heap} {rin : BRef} {A : Array UInt8} {p : Nat} (hA : Space.get H rin = some A)
    (l : FL) (hin : l.in_ = .ref rin p) (hp : p + 8 ≤ A.size) (hb : l.bits.toNat < 64) :
    Sat H (REFILL l) (fun l' H' => H' = H ∧ ∃ hd : UInt64,
      l' = { l with hold := hd, in_ := Ptr.ref rin (p + (7 - l.bits.toNat / 8)), bits := l.bits ||| 56 }) := by
  have h64 : l.bits.toUInt32 < 64 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hb
  unfold REFILL load_64_bits
  rw [hin]
  refine Sat.bind (Sat.mono (P := fun _ H' => H' = H) (Sat.bind (Sat.mono
    (ZlibNgF.Proof.ChunkMem.sat_memread8 hA hp) fun c H' hH => ⟨c <<< l.bits.toUInt32.toUInt64, H', by simp [shl64, h64], hH⟩)) ?_)
  rintro w H' rfl
  refine Sat.bind (Sat.mono (sat_add_g hA (by omega) _ (p + (7 - l.bits.toNat / 8))
    (by rw [xor63 _ hb]; simp) (by omega)) ?_)
  rintro q H' ⟨rfl, rfl⟩
  exact Sat.pure ⟨rfl, _, rfl⟩

/-- `DROPBITS(n)` for `n < 64`. -/
theorem sat_DROPBITS {H : Heap} (l : FL) (n : UInt32) (hn : n.toNat < 64) :
    Sat H (DROPBITS l n) (fun l' H' => H' = H ∧ ∃ hold, l' = { l with hold := hold, bits := l.bits - n.toUInt8 }) := by
  have h64 : n < 64 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hn
  refine ⟨{ l with hold := l.hold >>> n.toUInt64, bits := l.bits - n.toUInt8 }, H, ?_, rfl, _, rfl⟩
  simp [DROPBITS, shr64, h64]

/-- `BITS(n)` for `n < 32`: a value below `2 ^ n`. -/
theorem sat_BITS {H : Heap} (l : FL) (n : UInt32) (hn : n.toNat < 32) :
    Sat H (BITS l n) (fun v H' => H' = H ∧ v.toNat < 2 ^ n.toNat) := by
  have h32 : n < 32 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hn
  refine ⟨l.hold &&& (((1 : UInt32) <<< n) - 1).toUInt64, H, by simp [BITS, shl32, h32], rfl, ?_⟩
  exact and_mask_lt _ _ hn

theorem shl64_tab : ∀ n, n < 64 → (((1 : UInt64) <<< (UInt8.ofNat n).toUInt32.toUInt64) - 1).toNat = 2 ^ n - 1 := by
  decide

/-- `EXTRA_BITS(old, here, op)` for `here.bits < 64`: a value below `2 ^ (here.bits - (op & 15))`. -/
theorem sat_EXTRA_BITS {H : Heap} (old : UInt64) (here : Code) (op : UInt32) (hb : here.bits.toNat < 64) :
    Sat H (EXTRA_BITS old here op) (fun v H' => H' = H ∧
      v.toNat < 2 ^ (here.bits.toNat - (op &&& MAX_BITS).toNat)) := by
  have h64 : here.bits.toUInt32 < 64 := by rw [UInt32.lt_iff_toNat_lt]; simpa using hb
  have h15 : op &&& MAX_BITS < 64 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_and]; simp [MAX_BITS]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  refine ⟨(old &&& (((1 : UInt64) <<< here.bits.toUInt32.toUInt64) - 1)) >>> (op &&& MAX_BITS).toUInt64, H,
    by simp [EXTRA_BITS, shl64, shr64, h64, h15], rfl, ?_⟩
  have hm : (((1 : UInt64) <<< here.bits.toUInt32.toUInt64) - 1).toNat = 2 ^ here.bits.toNat - 1 := by
    have := shl64_tab here.bits.toNat hb; simpa using this
  rw [UInt64.toNat_shiftRight, UInt64.toNat_and, hm]
  have hk : (op &&& MAX_BITS).toUInt64.toNat % 64 = (op &&& MAX_BITS).toNat := by
    simp only [UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    rw [UInt32.toNat_and]; simp [MAX_BITS]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [hk, Nat.shiftRight_eq_div_pow]
  have h1 : old.toNat &&& (2 ^ here.bits.toNat - 1) < 2 ^ here.bits.toNat := by
    have := Nat.and_le_right (n := old.toNat) (m := 2 ^ here.bits.toNat - 1)
    have := Nat.one_le_two_pow (n := here.bits.toNat)
    omega
  apply Nat.div_lt_of_lt_mul
  calc _ < 2 ^ here.bits.toNat := h1
    _ ≤ 2 ^ (op &&& MAX_BITS).toNat * 2 ^ (here.bits.toNat - (op &&& MAX_BITS).toNat) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)

end ZlibNgF.Proof.InffastBase
