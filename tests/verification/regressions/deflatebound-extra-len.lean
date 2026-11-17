import ZlibF.Spec.Common.Streams

/-!
# deflateBound: the gzip extra length is added at 32 bits

**What this regression is.** The arithmetic core of the correction of `WrapperLength`: the C adds
`2 + s->gzhead->extra_len` with `extra_len` an `unsigned int`, so the sum wraps. The old statement
added `2 + extra_len` as a natural number, which is `2^32` larger than what the C returns for
`extra_len = 2^32 - 1` and `2^32 - 2`. It is not a checked run of the translated `deflateBound_z`.

Evidence on the real C: `tests/goals/deflate-bound/bound.c`, mode `extra`, prints bound 126 for
100 input bytes and `extra_len = 2^32 - 1` (a finding, `docs/en/findings.md`).
-/

namespace DeflateBoundExtraLenRegression

/-- The corrected term and the old term differ by `2^32` at `extra_len = 2^32 - 1`. -/
theorem old_term_exceeds_c :
    ((2 : UInt32) + (0xFFFFFFFF : UInt32)).toNat = 1 ∧
    2 + (0xFFFFFFFF : UInt32).toNat = 2 ^ 32 + 1 := by
  decide

/-- Below the wrap the two terms agree. -/
theorem terms_agree (e : UInt32) (small : e.toNat + 2 < 2 ^ 32) :
    ((2 : UInt32) + e).toNat = 2 + e.toNat := by
  rw [UInt32.toNat_add]
  simp only [UInt32.reduceToNat]
  omega

end DeflateBoundExtraLenRegression
