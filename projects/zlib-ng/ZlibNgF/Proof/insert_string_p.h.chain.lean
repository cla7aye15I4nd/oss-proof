import ZlibNgF.Proof.«insert_string_p.h.safety»

/-!
# The hash chains under one insertion (`ZlibNgF`)

One insertion of position `p` with hash `h` (`insert_knuth`, `insert_knuth_val`, `insert_knuth_one` and the batch,
spread and stepped loops built from them) writes `prev[p & w_mask] = head[h]; head[h] = p`, or nothing when
`head[h] == p`. `ChainSet d ho po w ss lim I` holds the three clauses of `ChainOk` for a set `I` of positions,
with `head` at `ho`, `prev` at `po`, window size `w`, `strstart = ss` and position limit `lim`:

* (C1) every position of `I` is in `(0, lim)`;
* (C2) every nonzero `head` entry is in `I`;
* (C3) for every `p` of `I` still in the window (`ss < p + w`), `prev[p % w]` is 0 or in `I`.

`chain_step`: an insertion of `p` (0, or in `(0, lim)`) keeps the clauses with `I` extended by `p`. The value written
to `prev` is the old `head[h]`, which is 0 or in `I` by (C2), so every `prev` slot it overwrites still satisfies (C3),
whichever positions share that slot. `chain_mono`: the clauses survive a larger `strstart` and a larger limit.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InsertChain

/-- The `Pos` entry `k` of the array of `Pos` at byte offset `o` (little-endian). -/
def posAt (d : Array UInt8) (o k : Nat) : Nat := d[o + 2 * k]!.toNat + 256 * d[o + 2 * k + 1]!.toNat

/-- The clauses (C1)-(C3) of `ChainOk` for the set `I` (see the module comment). -/
structure ChainSet (d : Array UInt8) (ho po w ss lim : Nat) (I : Nat → Prop) : Prop where
  c1 : ∀ p, I p → 0 < p ∧ p < lim
  c2 : ∀ k, k < 65536 → posAt d ho k ≠ 0 → I (posAt d ho k)
  c3 : ∀ p, I p → ss < p + w → posAt d po (p % w) = 0 ∨ I (posAt d po (p % w))

/-- What one insertion of `p` with hash `h` does to the `Pos` entries: `head[h] = p`, `prev[p % w] = ` the old
`head[h]`, every other `head` and `prev` entry kept. -/
structure InsWrite (d d' : Array UInt8) (ho po w h p : Nat) : Prop where
  head_h : posAt d' ho h = p
  head_k : ∀ k, k < 65536 → k ≠ h → posAt d' ho k = posAt d ho k
  prev_p : posAt d' po (p % w) = posAt d ho h
  prev_k : ∀ k, k < w → k ≠ p % w → posAt d' po k = posAt d po k

/-- An insertion of `p` (0, or in `(0, lim)`) keeps (C1)-(C3) with `I` extended by `p`. -/
theorem chain_step {d d' : Array UInt8} {ho po w ss lim h p : Nat} {I : Nat → Prop} (hw : 0 < w) (hh : h < 65536)
    (C : ChainSet d ho po w ss lim I) (W : InsWrite d d' ho po w h p) (hp : p ≠ 0 → p < lim) :
    ChainSet d' ho po w ss lim (fun q => I q ∨ (q = p ∧ p ≠ 0)) := by
  -- the old `head[h]` is 0 or in `I`
  have hold : posAt d ho h = 0 ∨ I (posAt d ho h) := by
    by_cases e : posAt d ho h = 0
    · exact Or.inl e
    · exact Or.inr (C.c2 h hh e)
  refine ⟨fun q hq => ?_, fun k hk hne => ?_, fun q hq hin => ?_⟩
  · rcases hq with hq | ⟨rfl, hq⟩
    · exact C.c1 q hq
    · exact ⟨Nat.pos_of_ne_zero hq, hp hq⟩
  · by_cases e : k = h
    · subst e; rw [W.head_h] at hne ⊢; exact Or.inr ⟨rfl, hne⟩
    · rw [W.head_k k hk e] at hne ⊢; exact Or.inl (C.c2 k hk hne)
  · by_cases e : q % w = p % w
    · rw [e, W.prev_p]
      rcases hold with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
    · rw [W.prev_k _ (Nat.mod_lt _ hw) e]
      rcases hq with hq | ⟨rfl, -⟩
      · -- `q` is old; its `prev` slot was not written
        rcases C.c3 q hq hin with h0 | h1
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
      · exact absurd rfl e

/-- An insertion skipped because `head[h] == p` writes nothing: the clauses hold with the same `I`. -/
theorem chain_skip {d : Array UInt8} {ho po w ss lim : Nat} {I : Nat → Prop} (C : ChainSet d ho po w ss lim I) :
    ChainSet d ho po w ss lim I := C

/-- The clauses survive a larger `strstart` and a larger limit. -/
theorem chain_mono {d : Array UInt8} {ho po w ss lim ss' lim' : Nat} {I : Nat → Prop}
    (C : ChainSet d ho po w ss lim I) (hs : ss ≤ ss') (hl : lim ≤ lim') : ChainSet d ho po w ss' lim' I :=
  ⟨fun p hp => ⟨(C.c1 p hp).1, Nat.lt_of_lt_of_le (C.c1 p hp).2 hl⟩, C.c2,
    fun p hp hin => C.c3 p hp (Nat.lt_of_le_of_lt hs hin)⟩

/-- The clauses for a set equivalent to `I`. -/
theorem chain_congr {d : Array UInt8} {ho po w ss lim : Nat} {I J : Nat → Prop} (C : ChainSet d ho po w ss lim I)
    (e : ∀ q, I q ↔ J q) : ChainSet d ho po w ss lim J :=
  ⟨fun p hp => C.c1 p ((e p).2 hp), fun k hk hne => (e _).1 (C.c2 k hk hne),
    fun p hp hin => by
      rcases C.c3 p ((e p).2 hp) hin with h0 | h1
      · exact Or.inl h0
      · exact Or.inr ((e _).1 h1)⟩

end ZlibNgF.Proof.InsertChain
