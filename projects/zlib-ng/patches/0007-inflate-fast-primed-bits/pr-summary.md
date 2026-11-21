# Keep inflate_fast() from returning primed bits as input

## Problem

On exit, `inflate_fast()` gives every whole byte left in the bit buffer back to `next_in` (`len = bits >> 3; in -= len;`, `inffast_tpl.h:326-327` at the pin). That is right only for bytes the call loaded itself. Bits put in the bit buffer by `inflatePrime()` (up to 32) never came from `next_in`, so when a short fast-path run follows a primed block header, `in` moves before the caller's input buffer (ISO C17 §6.5.6p8), `avail_in` grows past what the caller gave, `total_in` wraps, and the next refill reads 8 bytes starting before the buffer.

Reachable through documented calls only: `inflateInit2(strm, -15)`, `inflatePrime(strm, 16, 3)`, `inflatePrime(strm, 16, 0)`, then `inflate()` with 32 bytes of input returns `avail_in` 34 and `total_in` 4294967294 on the pinned `develop` commit.

## Fix

Files: `inffast_tpl.h` (library), `test/test_inflate_cve.cc` (test). `inflate.c` is unchanged from `develop`.

- At the exit of `INFLATE_FAST`, the number of bytes given back is capped at the number this call loaded: `len = MIN((unsigned)(bits >> 3), (unsigned)(in - strm->next_in));`. `in` therefore never moves below its value on entry. Leftover primed bits stay in the bit buffer for the next symbol, so primed streams keep the fast path.
- The entry assumption in the comment at the top of `inffast_tpl.h` becomes `state->bits <= 32`, the limit `inflatePrime()` enforces.
- `inflate.primed_bits_fast_path`: a raw stream whose first 32 bits (a fixed block with only an end-of-block code, then a last fixed block with only an end-of-block code) come through two `inflatePrime(16, ...)` calls, decoded from a 16-byte input with guard bytes before it; it checks `Z_STREAM_END`, that `next_in` stays inside the input and that `next_in + avail_in` is the end of the input.

The series is the head commit `0c7807f2` of zlib-ng PR #2526 with its author's attribution, rebased onto the pinned commit (only the hunk offset in `inffast_tpl.h` differs). The fix is the form the zlib-ng maintainer proposed in review of that PR; zlib fixed the same defect the other way.

Why the new form is safe and gives the right result (checked on the code, by tests, and in the Lean proofs of this project):

- Refill: `REFILL()` shifts by `bits`, which is below 64 at every refill; with `b` bits held on entry it advances `in` by `(63 - b) >> 3` bytes and leaves `56 + b % 8` bits, so a larger entry count only makes the first refill advance less. Every 8-byte read stays inside the input as before.
- Exit: when the cap binds, every byte the call loaded goes back, `in` equals `next_in`, and the bits left are the entry bits minus the bits consumed, fewer than on entry (at least one bit is consumed). Otherwise fewer than 8 bits are left, as before. `inflate()` enters the fast path with at most 32 bits held, so at most 32 are left: `Assert(bits <= 32)` and the 32-bit store of `hold` stay exact.
- `inflateBack()` never primes; it enters the fast path with fewer than 8 bits held, so the cap never binds there and nothing changes. Both instantiations (`inflate_fast` and the safe variant) share the exit.

## Related Upstream References

- Open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2526 (another contributor; this series is its head commit `0c7807f2`).
- zlib fixed the same defect differently in madler/zlib@e7bb9788, by sending primed streams to the slow path until fewer than 8 bits are held (`bits < 8` in state `LEN` of `inflate()`), so zlib and zlib-ng differ here.

## Review Feedback Addressed

- From the maintainer's review of #2526 (all taken in its head commit): `inflate.c` back to `develop` (no `bits < 8` test in state `LEN`; ordinary streams also reach the fast path with 8 to 13 bits after a call that ran out of input in the middle of a code); the fix at the exit of `inflate_fast()`; the entry assumption updated to `state->bits <= 32`; the test renamed to `primed_bits_fast_path`; the commit message stating that zlib fixed it differently.

## Testing

- GoogleTest under ASan (`detect_invalid_pointer_pairs=2`, pointer-compare and pointer-subtract on C) and UBSan, clang, `-O0`, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `WITH_CRC32_CHORBA=OFF`, `WITH_RUNTIME_CPU_DETECTION=OFF`, all series applied: `inflate.primed_bits_fast_path` passes; without this series' library hunk (the pinned `develop` code) it fails with "invalid distance code" (guard bytes before the input get decoded).
- A priming fuzzer under the same sanitizers and options: 12,000 raw, zlib and gzip streams (every level and strategy, short blocks from partial flushes, 0 to 32 primed bits over bit-shifted streams, input in exact-size pieces of 1 byte up to whole, output from 1 byte up), plus `inflateBack()` with input pieces of every size: no sanitizer report, `next_in` always inside the current input piece, and the return codes, output, `total_in` and `total_out` of every case are identical to those of the `bits < 8` form. On `develop` the same fuzzer stops with an AddressSanitizer report (pointer pair: `next_in` before the input piece) within its first thousand cases.
- Reproduction `inflate-fast-primed-bits` of this project's regression suite: `avail_in` 32 and `total_in` 0 after the call (34 and 4294967294 on `develop`).
