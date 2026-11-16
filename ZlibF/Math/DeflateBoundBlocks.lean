/-!
# The block arithmetic of `deflateBound`

Heap-free. `deflateBound` (`deflate.c`) returns one of three formulas. Each lemma here says that
a stream cut into blocks of at least a given size, with a fixed overhead per block, fits the
formula. The block facts themselves (sizes, overhead per block) are proved about the C elsewhere.

* `tight_blocks`: the bound for `windowBits` 15 and `memLevel` 8. Blocks of `16383` bytes cost at
  most 5 bytes more than their data each (a stored block after any bit offset, counted in whole
  bytes). The final block costs 5 bytes more than its data, or 2 bytes when it is empty.
* `stored_blocks`: the conservative stored bound, for blocks of at least `127` bytes.
* `fixed_blocks`: the conservative fixed bound, in bits: at most 9 bits per byte, 10 bits per
  block (3 header bits and a 7-bit end code), blocks of at least `255` bytes, then the final block.
-/

namespace ZlibF.Math.DeflateBound

theorem tight_blocks (n : Nat) :
    n + 5 * (n / 16383) + (if n % 16383 = 0 then 2 else 5) ≤
      n + n / 4096 + n / 16384 + n / 33554432 + 7 := by
  split <;> omega

theorem stored_blocks (K n : Nat) (hK : 127 ≤ K) :
    n + 5 * (n / K) + 5 ≤ n + n / 32 + n / 128 + n / 2048 + 7 := by
  have : n / K ≤ n / 127 := Nat.div_le_div_left hK (by decide)
  omega

theorem fixed_blocks (K n : Nat) (hK : 255 ≤ K) :
    9 * n + 10 * (n / K) + 10 ≤ 8 * (n + n / 8 + n / 256 + n / 512 + 4) := by
  have : n / K ≤ n / 255 := Nat.div_le_div_left hK (by decide)
  omega

end ZlibF.Math.DeflateBound
