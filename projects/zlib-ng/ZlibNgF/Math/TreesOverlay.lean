/-!
# The `sym_buf` overlay of `compress_block` (`ZlibNgF`)

`sym_buf` starts `lit_bufsize + 8` bytes into `pending_buf` (`B = lit_bufsize`), and symbol `k` occupies bytes
`B + 8 + 3k .. B + 8 + 3k + 2`. `compress_block` writes the compressed block from `pending_buf + pending` upward:
before it reads the symbol at `sx = 3k`, `send_bits_flush` stores 8 bytes at `pending`, and `8 * pending` never
exceeds the bits emitted so far (the bits waiting before the block, the 3 header bits, the tree header and the costs
of symbols `0 .. k - 1`). The store leaves symbol `k` intact exactly when `pending + 8 ≤ B + 8 + 3k`.

Each consumed symbol frees 3 bytes (24 bits), so a prefix costs at most 24 bits per symbol plus the positive excess
of the whole block (`bitExcess`): no bound on single symbols and no order of the symbols is needed. The block then
fits when `Budget B t0 costs` holds: the bits before the first symbol (`t0`) and the block's excess fit in
`8 * B + 7` bits.

* `room_before` and `room_header`: the 8-byte stores before each symbol and during the header stay below the
  unread symbols.
* `room_end`: with at most `B - 1` symbols (`sym_end = 3 * (B - 1)`), the end-of-block code and its 8-byte store stay
  inside `pending_buf` (`4 * B + 9` bytes).
* `static_budget`: with static trees every symbol costs at most 31 bits (a match: 8 + 5 + 5 + 13), so the budget
  holds for every `B ≥ 52` with up to 63 waiting bits, whatever the order of the symbols.

For a dynamic block `t0` also counts the tree header, and the budget is the inequality the block choice of
`zng_tr_flush_block` has to provide (header and excess bounded through the code lengths `gen_bitlen` assigns).
Nothing here refers to the heap.
-/

set_option autoImplicit false

namespace ZlibNgF.Math.TreesOverlay

/-- The positive excess of each symbol cost over the 24 bits its three `sym_buf` bytes free. -/
def bitExcess (costs : List Nat) : Nat :=
  (costs.map (fun c => c - 24)).sum

@[simp] theorem bitExcess_nil : bitExcess [] = 0 := rfl

theorem bitExcess_cons (c : Nat) (cs : List Nat) : bitExcess (c :: cs) = (c - 24) + bitExcess cs := by
  simp [bitExcess]

/-- A prefix of `k` symbols costs at most `24 * k` bits plus the whole block's excess. -/
theorem prefix_bits_le (costs : List Nat) : ∀ k, (costs.take k).sum ≤ 24 * k + bitExcess costs := by
  induction costs with
  | nil => intro k; simp
  | cons c cs ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have h := ih k
      simp only [List.take_succ_cons, List.sum_cons, bitExcess_cons]
      omega

/-- The whole block costs at most `24` bits per symbol plus its excess. -/
theorem sum_le (costs : List Nat) : costs.sum ≤ 24 * costs.length + bitExcess costs := by
  have h := prefix_bits_le costs costs.length
  rwa [List.take_length] at h

/-- With every cost at most `24 + e`, the excess is at most `e` per symbol. -/
theorem bitExcess_le (e : Nat) : ∀ costs : List Nat, (∀ c ∈ costs, c ≤ 24 + e) →
    bitExcess costs ≤ e * costs.length
  | [], _ => by simp
  | c :: cs, h => by
    have h1 := h c (by simp)
    have h2 := bitExcess_le e cs (fun x hx => h x (by simp [hx]))
    rw [bitExcess_cons, List.length_cons, Nat.mul_succ]
    omega

/-- The overlay budget of a block with `B = lit_bufsize`: the bits before the first symbol (`t0`) and the excess
of the symbol costs fit in `8 * B + 7` bits. -/
def Budget (B t0 : Nat) (costs : List Nat) : Prop :=
  t0 + bitExcess costs ≤ 8 * B + 7

/-- Before symbol `k` is read, an 8-byte store at `pending = p` (with `8 * p` at most the bits emitted before it)
ends at or before symbol `k` (offset `B + 8 + 3k`). -/
theorem room_before {B t0 : Nat} {costs : List Nat} (hb : Budget B t0 costs) (k p : Nat)
    (hp : 8 * p ≤ t0 + (costs.take k).sum) : p + 8 ≤ B + 8 + 3 * k := by
  have h := prefix_bits_le costs k
  unfold Budget at hb
  omega

/-- During the header (before any symbol is read) an 8-byte store at `p` ends at or before `sym_buf`. -/
theorem room_header {B t0 : Nat} {costs : List Nat} (hb : Budget B t0 costs) (p : Nat) (hp : 8 * p ≤ t0) :
    p + 8 ≤ B + 8 := by
  unfold Budget at hb
  omega

/-- After the last of at most `B - 1` symbols, an 8-byte store at `p` with `8 * p` at most every bit of the block
(the end-of-block code included, at most 15 bits) ends inside `pending_buf` (`4 * B + 9` bytes). -/
theorem room_end {B t0 : Nat} {costs : List Nat} (hb : Budget B t0 costs) (hn : costs.length + 1 ≤ B) (p : Nat)
    (hp : 8 * p ≤ t0 + costs.sum + 15) : p + 8 ≤ 4 * B + 9 := by
  have h := sum_le costs
  unfold Budget at hb
  omega

/-- Static trees: every symbol costs at most 31 bits, so with at most `B - 1` symbols, up to 63 bits waiting
before the block and its 3 header bits, the budget holds for every `B ≥ 52` (`lit_bufsize ≥ 128` in zlib-ng). -/
theorem static_budget {B b0 : Nat} {costs : List Nat} (hB : 52 ≤ B) (hb0 : b0 < 64)
    (hn : costs.length + 1 ≤ B) (h31 : ∀ c ∈ costs, c ≤ 31) : Budget B (b0 + 3) costs := by
  have h := bitExcess_le 7 costs (fun c hc => by have := h31 c hc; omega)
  unfold Budget
  omega

end ZlibNgF.Math.TreesOverlay
