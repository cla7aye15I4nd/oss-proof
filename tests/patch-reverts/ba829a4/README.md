# ba829a4: `crc32_combine` with a negative length does not return

- **Fix:** upstream commit `ba829a458576d1ff0f26fc7230c6de816d1f6a77`, "Check for negative lengths in
  crc32_combine functions", in zlib 1.3.2. `zlib.h` now says that a negative length gives 0.
- **Revert** (`revert.patch`, `lean.patch`): `crc32_combine_gen64` no longer returns 0 for a negative
  length. The commit added the check to two functions that were merged into this one later, so
  the revert is the removal of the one check at the pin.
- **Calls** (`trigger.c`, `model.lean`): `crc32` of "abc" and of "def"; `crc32_combine(crc1, crc2, -1)`,
  which reaches `x2nmodp(-1, 3)`. Its loop `while (n) { ...; n >>= 1; }` keeps `n` at -1.
- **C:** with the revert, the call does not return; the run is stopped after 10 seconds. Without it,
  the call returns 0 at once. This defect is a hang, not a memory error: no sanitizer reports it.
- **Model:** with the revert, the run does not return within the time limit. A loop of the model
  ends in `Fault.outOfFuel` after 2^64 iterations, which no run reaches; the loop here never
  exits. Without it, the line `trigger.c` prints.
- **Domain:** inside `Goal.crc32_combine_gen64_safety`, which concludes that the call returns for
  every length, negative ones included, and `Goal.crc32_combine_safety`. Checked by reading the
  premises.
