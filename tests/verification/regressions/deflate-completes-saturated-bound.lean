import ZlibF.Spec.Functional.Api.Compress

/-!
# deflate completion: the room was measured against a saturated bound

**What this regression is.** The arithmetic that made the old `Goal.deflate_completes_default`
false. Its room premise was `Api.compressBound (accepted + remaining) ≤ delivered + avail_out`.
`Api.compressBound` saturates at `2^64 - 1`, while a clean default history is an unbounded sequence
of calls and can accept more than `2^64` bytes. With incompressible data the delivered output then
exceeds `2^64 - 1` as well, so the premise holds with `avail_out = 1`, and the goal claimed that
this `deflate(Z_FINISH)` call returns `Z_STREAM_END` although its final block and trailer need more
than one byte. The corrected goal measures the room against `unsaturatedBound`, which keeps growing.
It is not a run of the C (no test can feed `2^64` bytes); `zlib.h` promises nothing once the bound
saturates.

Checked with `lake env lean tests/verification/regressions/deflate-completes-saturated-bound.lean`
(the regressions here are not part of a lake target).
-/

namespace DeflateCompletesSaturatedBoundRegression
open ZlibF.Spec

/-- Past `2^64` accepted bytes, `compressBound` is stuck at `2^64 - 1`. -/
theorem saturated (m : Nat) (big : 18446744073709551616 ≤ m) :
    Api.compressBound m = 18446744073709551615 := by
  have unfolded : Api.compressBound m =
      if m + m / 4096 + m / 16384 + m / 33554432 + 13 ≥ 18446744073709551616 then 18446744073709551615
      else m + m / 4096 + m / 16384 + m / 33554432 + 13 := by
    unfold Api.compressBound
    rfl
  rw [unfolded, if_pos (by omega)]

/-- The old room premise then holds with one byte of room once `2^64 - 2` bytes are delivered. -/
theorem old_premise_one_byte (m delivered : Nat) (big : 18446744073709551616 ≤ m)
    (output : 18446744073709551614 ≤ delivered) : Api.compressBound m ≤ delivered + 1 := by
  rw [saturated m big]
  omega

end DeflateCompletesSaturatedBoundRegression
