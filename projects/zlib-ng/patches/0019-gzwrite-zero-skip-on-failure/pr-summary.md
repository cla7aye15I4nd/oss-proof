# Take each batch of zeros off skip before writing it in gz_zero()

## Problem

A seek on a writer records the zeros to write in `state->skip`; `gz_zero()` (`gzwrite.c`) writes them in batches of up to the buffer size. It added each batch to `x.pos` before writing it, but took it off `skip` only after the write succeeded. A failed write left the batch counted in both, so `x.pos + skip` passed the position `gzseek()` had returned:

1. After `gzseek(file, GZ_OFF_MAX, SEEK_SET)` and one failed write, `gztell()` computed `x.pos + skip` with signed overflow (ISO C17 §6.5p5).
2. With a smaller seek, after `gzclearerr()` the retry wrote the batch left in the input buffer and then the same zeros again: the file and `gztell()` were longer than the seek asked for (14099 bytes for a seek to 10000 and a 3-byte write, with a 4096-byte buffer).

## Fix

`gz_zero()` takes each batch off `skip` when it adds the batch to `x.pos`, before `gz_comp()` writes it. When the write fails, the batch stays in the input buffer (`avail_in`), and the next `gz_zero()` (after `gzclearerr()`) or `gz_comp()` writes it first, so the file gets exactly the zeros the seek asked for. On every path without a failure nothing changes.

madler/zlib fixed the repeated zeros with `51c7cd2c` ("Discard unconsumed zero fill in gz_zero() on a write error."): in madler's non-blocking `gz_zero()` (from `81cc0be`), which calls `gz_comp()` first and then counts only the consumed part (`n -= strm->avail_in`), it discards the unconsumed zeros on error so that the retry generates them again. That commit is not cherry-picked: it depends on that loop, which zlib-ng does not have, and does not apply to zlib-ng's `gzwrite.c`. Both forms keep `x.pos + skip` equal to the position sought.

Add two tests in `test/test_gzio.cc`:

- `gzip.seek_zeros_write_error_position`: a transparent writer on a descriptor that rejects every write (`/dev/null` opened read-only) seeks to the largest position; after the failed `gzwrite()` and after a failed `gzputc()`, `gztell()` must still return that position. Skipped where `gzseek()` does not take a `z_off64_t` offset.
- `gzip.seek_zeros_write_retry`: a transparent writer with a 4096-byte buffer on a full non-blocking pipe seeks to 10000 and writes `"abc"`, which fails with `Z_ERRNO` and leaves `gztell()` at 10000; after the pipe is drained and the error cleared, the same write succeeds, `gztell()` is 10003, and the pipe holds exactly 10000 zeros and `"abc"`.

## Related Upstream References

- madler/zlib `51c7cd2c` (in zlib 1.4): the same defect, fixed in madler's restructured `gz_zero()`.
- Not yet submitted to zlib-ng.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer:
  - Before the fix: `seek_zeros_write_error_position` aborts with "runtime error: signed integer overflow: 131072 + 9223372036854775807" in `gztell64()`; `seek_zeros_write_retry` fails (`gztell()` 14096 after the failed write, 14099 after the retry, 14099 bytes in the pipe).
  - After the fix: both pass.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: both pass.
