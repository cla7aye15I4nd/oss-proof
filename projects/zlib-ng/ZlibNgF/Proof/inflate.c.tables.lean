import ZlibNgF.Spec.Safety.Inflate

/-!
# Decoding tables as `inflate` reads them (`ZlibNgF`)

`CodeTable a o e n m dist`: the entries `a[o, e)` form a decoding table with `n` root index bits, as the decoders of
`inflate` (the `LEN`, `DIST` and `CODELENS` modes, and `inflate_fast_c` / `inflate_fast_safe_c`) use it. Only what
these readers need is asked:

* the root table `a[o, o + 2^n)` lies in the region, `1 ≤ n ≤ 15` (`BITS(n)` needs `n < 32`);
* every entry of the region has `1 ≤ CODE_BITS ≤ bits ≤ m` (a decode drops at least one bit, `CODE_EXTRA` does not
  wrap, and the bit buffer stays bounded), and an entry that is neither a length/distance (`op & 16`) nor invalid /
  end of block (`op & 64`) has `op < 16` (`BITS(op)` of the fast decoders);
* a link takes the `n` root bits (the slow decoder shifts by `last.bits + last.op` bits);
* a link (the test of the slow decoder: `op != 0 && (op & 0xf0) == 0` for literal/length tables,
  `(op & 0xf0) == 0` for distance tables) points to a sub-table `a[o + val, o + val + 2^op)` inside the region,
  and its `bits` plus the `bits` of every sub-table entry is at most `m`;
* in a distance table, a valid entry (`op & 64 == 0`) and a distance base (`op & 16`, the first test of
  `inflate_fast`) have `val ≥ 1` (a match distance is never zero);
* sub-table entries are not links (a decoder follows at most one link);
* in a literal/length table (`LenOK`, what `inflate_fast` needs: three symbols after one `REFILL` of at least 56
  bits): a literal takes at most 15 bits in all (link bits plus entry bits), any other entry at most 20 (a code of at
  most 15 bits and at most 5 extra bits), and a length base `val + extra` lies in `[1, 258]` for every value of its
  extra bits (`op & 15` code bits and `bits - (op & 15)` extra bits, `COMBINE_OP` / `COMBINE_BITS`).

`zng_inflate_table` establishes this predicate (the hypothesis `TableFacts` of `Proof/inflate.c.facts.lean`); the
static `lenfix` / `distfix` satisfy it. The state invariant carries it through `TabAt` for the tables a mode reads.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateTab
open C ZlibNg.InflateP

/-- The link test of the slow decoder: `LEN` follows an entry with `op != 0 && (op & 0xf0) == 0`, `DIST` one with
`(op & 0xf0) == 0` (the functions passed to `decodeSym`). -/
def linkTest (dist : Bool) (e : Code) : Bool :=
  if dist then (e.op &&& 0xf0) == 0 else e.op != 0 && (e.op &&& 0xf0) == 0

/-- What a decoder needs from one table entry. -/
structure EntryOK (e : Code) (m : Nat) (dist : Bool) : Prop where
  cb_pos : 1 ≤ (CODE_BITS e).toNat
  cb_le : (CODE_BITS e).toNat ≤ e.bits.toNat
  bits_le : e.bits.toNat ≤ m
  op_lt : e.op &&& 16 = 0 → e.op &&& 64 = 0 → e.op &&& 0xf0 = 0
  dval : dist = true → (e.op &&& 64 = 0 ∨ e.op &&& 16 ≠ 0) → 1 ≤ e.val.toNat

/-- A literal/length entry reached after `pre` bits of a root link (`pre = 0` for a root entry): a literal
(`op == 0`) takes at most 15 bits in all, any other entry at most 20, and a length base (`op & 16`) gives a length
`val + extra` in `[1, 258]` for every value of its `bits - (op & 15)` extra bits. -/
def LenOK (pre : Nat) (e : Code) : Prop :=
  (e.op = 0 → pre + e.bits.toNat ≤ 15) ∧ (e.op ≠ 0 → pre + e.bits.toNat ≤ 20) ∧
  (e.op &&& 16 ≠ 0 → 1 ≤ e.val.toNat ∧ e.val.toNat + 2 ^ (e.bits.toNat - e.op.toNat % 16) ≤ 259)

/-- `a[o, e)` is a decoding table with `n` root bits whose entries satisfy `EntryOK _ m dist`; a literal/length table
(`dist = false`) also satisfies `LenOK` on the root entries and on the sub-table entries after their link's bits. -/
structure CodeTable (a : Array Code) (o e n m : Nat) (dist : Bool) : Prop where
  n_pos : 1 ≤ n
  n_le : n ≤ 15
  root : o + 2 ^ n ≤ e
  fits : e ≤ a.size
  ent : ∀ j, o ≤ j → j < e → EntryOK a[j]! m dist
  lit : dist = false → ∀ j, o ≤ j → j < o + 2 ^ n → LenOK 0 a[j]!
  link : ∀ j, o ≤ j → j < e → linkTest dist a[j]! = true →
    o + a[j]!.val.toNat + 2 ^ a[j]!.op.toNat ≤ e ∧
    ∀ k, k < 2 ^ a[j]!.op.toNat → a[j]!.bits.toNat + a[o + a[j]!.val.toNat + k]!.bits.toNat ≤ m ∧
      linkTest dist a[o + a[j]!.val.toNat + k]! = false ∧
      (dist = false → LenOK a[j]!.bits.toNat a[o + a[j]!.val.toNat + k]!)
  /-- a link takes the root bits (so `BITS(last.bits + last.op)` of the slow decoder shifts by less than 32) -/
  link_bits : ∀ j, o ≤ j → j < e → linkTest dist a[j]! = true → a[j]!.bits.toNat = n

/-- The table at `p` with `n` root bits, read by a decoder of the state in block `b` with code array `codes`: in the
state's own `codes` (region `[o, e)`), or a static fixed table. -/
def TabAt (b : Nat) (codes : Array Code) (p : Ival CodePtr) (n : UInt32) (m : Nat) (dist : Bool) : Prop :=
  (∃ o e, p = .val (.ref (.codes b) o) ∧ CodeTable codes o e n.toNat m dist) ∨
  (p = .val (.ref .lenfix 0) ∧ ∃ e, CodeTable lenfix 0 e n.toNat m dist) ∨
  (p = .val (.ref .distfix 0) ∧ ∃ e, CodeTable distfix 0 e n.toNat m dist)

/-- A table depends only on the entries of its region. -/
theorem CodeTable.congr {a a' : Array Code} {o e n m : Nat} {dist : Bool} (t : CodeTable a o e n m dist)
    (hs : e ≤ a'.size) (he : ∀ j, o ≤ j → j < e → a'[j]! = a[j]!) : CodeTable a' o e n m dist := by
  have hr := t.root
  refine ⟨t.n_pos, t.n_le, t.root, hs, fun j h1 h2 => (he j h1 h2) ▸ t.ent j h1 h2,
    fun hd j h1 h2 => (he j h1 (by omega)) ▸ t.lit hd j h1 h2, fun j h1 h2 hl => ?_, fun j h1 h2 hl => ?_⟩
  · rw [he j h1 h2] at hl ⊢
    obtain ⟨hlt, hk⟩ := t.link j h1 h2 hl
    refine ⟨hlt, fun k hk' => ?_⟩
    rw [he (o + a[j]!.val.toNat + k) (by omega) (by omega)]
    exact hk k hk'
  · rw [he j h1 h2] at hl ⊢
    exact t.link_bits j h1 h2 hl

/-- `TabAt` depends only on the region of the table when the code array changes. -/
theorem TabAt.congr {b : Nat} {codes codes' : Array Code} {p : Ival CodePtr} {n : UInt32} {m : Nat} {dist : Bool}
    (t : TabAt b codes p n m dist) (hs : codes'.size = codes.size) (he : ∀ j, j < codes.size → codes'[j]! = codes[j]!) :
    TabAt b codes' p n m dist := by
  rcases t with ⟨o, e, hp, t⟩ | ht | ht
  · exact Or.inl ⟨o, e, hp, t.congr (by rw [hs]; exact t.fits) (fun j _ h2 => he j (by have := t.fits; omega))⟩
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr ht)

/-- `TabAt` of a table in the `codes` of block `b`, seen from block `b'` with the same code array (`inflateCopy`
moves the table pointers to the copy's `codes`). -/
theorem TabAt.rebase {b b' o : Nat} {codes : Array Code} {n : UInt32} {m : Nat} {dist : Bool}
    (t : TabAt b codes (.val (.ref (.codes b) o)) n m dist) :
    TabAt b' codes (.val (.ref (.codes b') o)) n m dist := by
  rcases t with ⟨o', e, hp, t⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain rfl : o = o' := by cases hp; rfl
    exact Or.inl ⟨o, e, rfl, t⟩
  · cases hp
  · cases hp

/-- `TabAt` of a fixed table holds for every block. -/
theorem TabAt.fixed {b b' : Nat} {codes codes' : Array Code} {p : Ival CodePtr} {n : UInt32} {m : Nat} {dist : Bool}
    (t : TabAt b codes p n m dist) (hp : ∀ c o, p ≠ .val (.ref (.codes c) o)) : TabAt b' codes' p n m dist := by
  rcases t with ⟨o, e, rfl, t⟩ | ht | ht
  · exact absurd rfl (hp b o)
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr ht)

end ZlibNgF.Proof.InflateTab
