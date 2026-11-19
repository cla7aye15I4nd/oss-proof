import ZlibNgF.Proof.«inftrees.c.base»
import ZlibNgF.Proof.«inflate.c.tables»

/-!
# The entries `zng_inflate_table` stores (`ZlibNgF`)

What each slot of a finished table satisfies, in the terms of `CodeTable` (`Proof/inflate.c.tables.lean`): a root
slot (`RootOK`) is a decoder entry, a literal/length root entry has `LenOK 0`, and a link points to a sub-table of the
used region; a sub-table slot (`SubOK`) is a decoder entry, never a link, fits after the `root` bits of its link, and
has `LenOK root`. The entries the loop makes (literal, end of block, invalid, length/distance base, link, the
invalid-code markers) satisfy these, by the static tables `lbase` / `lext` / `dbase` / `dext` and `COMBINE_OP` /
`COMBINE_BITS`.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP ZlibNgF.Proof.InflateTab

/-- The bit budget of a code type: 25 for the code length code, 28 otherwise. -/
def mOf (type : UInt32) : Nat := if type = CODES then 25 else 28

/-- A distance table. -/
def dOf (type : UInt32) : Bool := type == DISTS

theorem mOf_ge (type : UInt32) : 25 ≤ mOf type := by unfold mOf; split <;> omega

/-- A sub-table entry after a link of `d` bits (or a root entry of a table without links, `d = 0`). -/
structure SubOK (type : UInt32) (d : Nat) (e : Code) : Prop where
  ent : EntryOK e (mOf type) (dOf type)
  nolink : linkTest (dOf type) e = false
  sum : d + e.bits.toNat ≤ mOf type
  len : dOf type = false → LenOK d e

/-- A root entry of a table of `root` index bits whose used region is `u` entries. -/
structure RootOK (type : UInt32) (root u : Nat) (e : Code) : Prop where
  ent : EntryOK e (mOf type) (dOf type)
  len : dOf type = false → LenOK 0 e
  link : linkTest (dOf type) e = true →
    e.bits.toNat = root ∧ 2 ^ root ≤ e.val.toNat ∧ e.val.toNat + 2 ^ e.op.toNat ≤ u

/-- Slot `i` of the table: a root slot below `2 ^ root`, a sub-table slot above. -/
def SlotOK (type : UInt32) (root u i : Nat) (e : Code) : Prop :=
  (i < 2 ^ root → RootOK type root u e) ∧ (2 ^ root ≤ i → SubOK type root e)

theorem RootOK.of_sub {type : UInt32} {root u : Nat} {e : Code} (h : SubOK type 0 e) : RootOK type root u e :=
  ⟨h.ent, h.len, fun hl => by rw [h.nolink] at hl; cases hl⟩

theorem RootOK.mono {type : UInt32} {root u u' : Nat} {e : Code} (h : RootOK type root u e) (hu : u ≤ u') :
    RootOK type root u' e :=
  ⟨h.ent, h.len, fun hl => by obtain ⟨a, b, c⟩ := h.link hl; exact ⟨a, b, by omega⟩⟩

theorem SlotOK.mono {type : UInt32} {root u u' i : Nat} {e : Code} (h : SlotOK type root u i e) (hu : u ≤ u') :
    SlotOK type root u' i e :=
  ⟨fun hi => (h.1 hi).mono hu, h.2⟩

/-! ## Bits of `op` -/

theorem u8_eq0 {a : UInt8} : a = 0 ↔ a.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact UInt8.toNat_inj.mp (by rw [h]; rfl)

theorem u8_and_toNat (a b : UInt8) : (a &&& b).toNat = a.toNat &&& b.toNat := UInt8.toNat_and a b

theorem nat_bits_small : ∀ c, c < 16 → c &&& 16 = 0 ∧ c &&& 240 = 0 ∧ c &&& 64 = 0 := by decide

theorem nat_bits_len : ∀ c, c < 16 → (16 + c) &&& 16 = 16 ∧ (16 + c) &&& 15 = c ∧ (16 + c) &&& 64 = 0 ∧
    (16 + c) &&& 240 = 16 ∧ c ||| 16 = 16 + c := by decide

theorem nat_bits_ext : ∀ n, n < 32 → 16 ≤ n → n &&& 16 = 16 ∧ n &&& 15 = n - 16 := by decide

theorem op_and16 (e : Code) : e.op &&& 16 = 0 ↔ e.op.toNat &&& 16 = 0 := by
  rw [u8_eq0, u8_and_toNat]; rfl

theorem op_and64 (e : Code) : e.op &&& 64 = 0 ↔ e.op.toNat &&& 64 = 0 := by
  rw [u8_eq0, u8_and_toNat]; rfl

theorem op_andf0 (e : Code) : e.op &&& 0xf0 = 0 ↔ e.op.toNat &&& 240 = 0 := by
  rw [u8_eq0, u8_and_toNat]; rfl

theorem codeBits_of {e : Code} (h : e.op.toNat &&& 16 = 0) : (CODE_BITS e).toNat = e.bits.toNat := by
  unfold CODE_BITS
  have : (e.op &&& 16 != 0) = false := by simpa using (op_and16 e).2 h
  rw [this]; simp

theorem codeBits_len {e : Code} (h : e.op.toNat &&& 16 ≠ 0) : (CODE_BITS e).toNat = e.op.toNat &&& 15 := by
  unfold CODE_BITS
  have : (e.op &&& 16 != 0) = true := by simpa using fun x => h ((op_and16 e).1 x)
  rw [this]; simp only [ite_true, UInt8.toNat_toUInt32, u8_and_toNat]; rfl

theorem linkTest_false {dist : Bool} {e : Code} (h : e.op.toNat &&& 240 ≠ 0) : linkTest dist e = false := by
  have : (e.op &&& 0xf0 == 0) = false := by simpa using fun x => h ((op_andf0 e).1 x)
  unfold linkTest; cases dist <;> simp [this]

theorem linkTest_true {dist : Bool} {e : Code} (h1 : e.op.toNat ≠ 0) (h : e.op.toNat &&& 240 = 0) :
    linkTest dist e = true := by
  have h2 : (e.op &&& 0xf0 == 0) = true := by simpa using (op_andf0 e).2 h
  have h3 : (e.op != 0) = true := by simpa [u8_eq0] using h1
  unfold linkTest; cases dist <;> simp [h2, h3]

/-! ## The kinds of entries -/

/-- A literal (`op = 0`) of a literal/length or code length table. -/
theorem sub_lit {type : UInt32} {d : Nat} {e : Code} (hop : e.op = 0) (hb1 : 1 ≤ e.bits.toNat)
    (hb : d + e.bits.toNat ≤ 15) (hd : dOf type = false) : SubOK type d e := by
  have hm := mOf_ge type
  have h0 : e.op.toNat = 0 := by rw [hop]; rfl
  have h16 : e.op.toNat &&& 16 = 0 := by rw [h0]; rfl
  refine ⟨⟨by rw [codeBits_of h16]; exact hb1, by rw [codeBits_of h16]; exact Nat.le_refl _, by omega,
    fun _ _ => by rw [hop]; rfl, fun h _ => by rw [hd] at h; cases h⟩, ?_, by omega,
    fun _ => ⟨fun _ => hb, fun h => absurd hop h, fun h => absurd (by rw [hop]; rfl) h⟩⟩
  rw [hd]; unfold linkTest; simp [hop]

/-- An end-of-block or invalid entry (`op & 64`, not `op & 16`). -/
theorem sub_inv {type : UInt32} {d : Nat} {e : Code} (h16 : e.op.toNat &&& 16 = 0) (h64 : e.op.toNat &&& 64 ≠ 0)
    (hf0 : e.op.toNat &&& 240 ≠ 0) (hb1 : 1 ≤ e.bits.toNat) (hb : d + e.bits.toNat ≤ 20) : SubOK type d e := by
  have hm := mOf_ge type
  refine ⟨⟨by rw [codeBits_of h16]; exact hb1, by rw [codeBits_of h16]; exact Nat.le_refl _, by omega,
    fun _ h => absurd ((op_and64 e).1 h) h64,
    fun _ h => h.elim (fun h => absurd ((op_and64 e).1 h) h64) (fun h => absurd ((op_and16 e).2 h16) h)⟩,
    linkTest_false hf0,
    by omega, fun _ => ⟨fun h => ?_, fun _ => hb, fun h => absurd ((op_and16 e).2 h16) h⟩⟩
  rw [h] at h64; exact absurd rfl h64

/-- A length or distance base: `op = 16 + cb` with `cb` code bits, `cb + x` bits in all with `x` extra bits. -/
theorem sub_len {type : UInt32} {d cb x : Nat} {e : Code} (hop : e.op.toNat = 16 + cb) (hcb1 : 1 ≤ cb)
    (hcb : cb < 16) (hbits : e.bits.toNat = cb + x) (hsum : d + cb + x ≤ mOf type) (hval : 1 ≤ e.val.toNat)
    (hlen : dOf type = false → d + cb + x ≤ 20 ∧ e.val.toNat + 2 ^ x ≤ 259) : SubOK type d e := by
  obtain ⟨b16, b15, b64, bf0, -⟩ := nat_bits_len cb hcb
  have h16 : e.op.toNat &&& 16 ≠ 0 := by rw [hop, b16]; omega
  have hcbv : (CODE_BITS e).toNat = cb := by rw [codeBits_len h16, hop, b15]
  have hne : e.op ≠ 0 := fun h => by rw [h] at hop; simp at hop; omega
  refine ⟨⟨by omega, by omega, by omega, fun h => absurd ((op_and16 e).1 h) h16, fun _ _ => hval⟩,
    linkTest_false (by rw [hop, bf0]; omega), by omega, fun hd => ?_⟩
  obtain ⟨hl1, hl2⟩ := hlen hd
  refine ⟨fun h => absurd h hne, fun _ => by omega, fun _ => ⟨hval, ?_⟩⟩
  rw [hbits, hop, show (16 + cb) % 16 = cb by omega, show cb + x - cb = x by omega]
  exact hl2

/-- A link to a sub-table of `2 ^ c` entries at `val`, inside the used region `u`. -/
theorem root_link {type : UInt32} {root u c : Nat} {e : Code} (hop : e.op.toNat = c) (hc1 : 1 ≤ c) (hc : c < 16)
    (hbits : e.bits.toNat = root) (hr1 : 1 ≤ root) (hr : root ≤ 15) (hv : 2 ^ root ≤ e.val.toNat)
    (hvu : e.val.toNat + 2 ^ c ≤ u) : RootOK type root u e := by
  have hm := mOf_ge type
  obtain ⟨b16, bf0, -⟩ := nat_bits_small c hc
  have h16 : e.op.toNat &&& 16 = 0 := by rw [hop, b16]
  have hne : e.op ≠ 0 := fun h => by rw [h] at hop; simp at hop; omega
  have hpos : 1 ≤ 2 ^ root := Nat.one_le_two_pow
  refine ⟨⟨by rw [codeBits_of h16]; omega, by rw [codeBits_of h16]; exact Nat.le_refl _, by omega,
    fun _ _ => (op_andf0 e).2 (by rw [hop, bf0]), fun _ _ => by omega⟩,
    fun _ => ⟨fun h => absurd h hne, fun _ => by omega, fun h => absurd ((op_and16 e).2 h16) h⟩,
    fun _ => ⟨hbits, hv, by rw [hop]; exact hvu⟩⟩

/-! ## `COMBINE_OP` / `COMBINE_BITS` and the static tables -/

theorem comb_len (ext : UInt32) (cb : UInt8) (h1 : 16 ≤ ext.toNat) (h2 : ext.toNat < 32) (hc : cb.toNat < 16) :
    (COMBINE_OP ext cb).toNat = 16 + cb.toNat ∧ (COMBINE_BITS cb ext).toNat = cb.toNat + (ext.toNat - 16) := by
  obtain ⟨e16, e15⟩ := nat_bits_ext ext.toNat h2 h1
  obtain ⟨-, -, -, -, hor⟩ := nat_bits_len cb.toNat hc
  have ht : (ext &&& 16 != 0) = true := by
    have : (ext &&& 16).toNat = 16 := by rw [UInt32.toNat_and]; exact e16
    have : ext &&& 16 ≠ 0 := fun h => by rw [h] at this; cases this
    simpa using this
  refine ⟨?_, ?_⟩
  · unfold COMBINE_OP; rw [ht]; simp only [ite_true, UInt8.toNat_or]; exact hor
  · unfold COMBINE_BITS
    rw [UInt32.toNat_toUInt8, UInt32.toNat_add, UInt32.toNat_and, UInt8.toNat_toUInt32]
    rw [show (15 : UInt32).toNat = 15 from rfl, e15]
    omega

theorem comb_64 (cb : UInt8) : COMBINE_OP 64 cb = 64 ∧ (COMBINE_BITS cb 64).toNat = cb.toNat := by
  refine ⟨by unfold COMBINE_OP; rw [ite_eq_right (by decide)]; rfl, ?_⟩
  unfold COMBINE_BITS
  rw [UInt32.toNat_toUInt8, UInt32.toNat_add, UInt8.toNat_toUInt32]
  have := cb.toNat_lt
  show (cb.toNat + 0) % 2 ^ 32 % 256 = _
  omega

theorem lext_ok : ∀ i, i < 29 → 16 ≤ (lext[i]!).toNat ∧ (lext[i]!).toNat < 32 ∧ (lext[i]!).toNat - 16 ≤ 5 ∧
    1 ≤ (lbase[i]!).toNat ∧ (lbase[i]!).toNat + 2 ^ ((lext[i]!).toNat - 16) ≤ 259 := by decide

theorem dext_ok : ∀ i, i < 30 → 16 ≤ (dext[i]!).toNat ∧ (dext[i]!).toNat < 32 ∧ (dext[i]!).toNat - 16 ≤ 13 ∧
    1 ≤ (dbase[i]!).toNat := by decide

theorem dext_hi : ∀ i, i < 32 → 30 ≤ i → dext[i]! = 64 := by decide

theorem mOf_lens : mOf LENS = 28 := rfl
theorem mOf_dists : mOf DISTS = 28 := rfl
theorem dOf_dists : dOf DISTS = true := rfl
theorem dOf_lens : dOf LENS = false := rfl
theorem dOf_codes : dOf CODES = false := rfl

/-! ## The packed store -/

theorem packCode_toNat (c : Code) : (packCode c).toNat = c.bits.toNat + 256 * c.op.toNat + 65536 * c.val.toNat := by
  have hb := c.bits.toNat_lt
  have ho := c.op.toNat_lt
  have hv := c.val.toNat_lt
  unfold packCode
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt8.toNat_toUInt32, UInt16.toNat_toUInt32]
  rw [show (8 : UInt32).toNat % 32 = 8 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e1 : c.bits.toNat ||| c.op.toNat * 2 ^ 8 = 2 ^ 8 * c.op.toNat + c.bits.toNat := by
    rw [Nat.or_comm, Nat.mul_comm]
    exact (Nat.two_pow_add_eq_or_of_lt hb _).symm
  have e2 : (2 ^ 8 * c.op.toNat + c.bits.toNat) ||| c.val.toNat * 2 ^ 16 =
      2 ^ 16 * c.val.toNat + (2 ^ 8 * c.op.toNat + c.bits.toNat) := by
    rw [Nat.or_comm, Nat.mul_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (i := 16) (b := 2 ^ 8 * c.op.toNat + c.bits.toNat) (by omega) _).symm
  rw [e1, e2]
  omega

theorem unpack_pack (c : Code) : unpackCode (packCode c) = c := by
  have hb := c.bits.toNat_lt
  have ho := c.op.toNat_lt
  have hv := c.val.toNat_lt
  have hp := packCode_toNat c
  unfold unpackCode
  cases c with
  | mk b o v =>
    simp only at hp hb ho hv
    congr 1
    · apply UInt8.toNat_inj.mp; rw [UInt32.toNat_toUInt8, hp]; omega
    · apply UInt8.toNat_inj.mp
      rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, hp, show (8 : UInt32).toNat % 32 = 8 from rfl,
        Nat.shiftRight_eq_div_pow]; omega
    · apply UInt16.toNat_inj.mp
      rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, hp, show (16 : UInt32).toNat % 32 = 16 from rfl,
        Nat.shiftRight_eq_div_pow]; omega

end ZlibNgF.Proof.Inftrees
