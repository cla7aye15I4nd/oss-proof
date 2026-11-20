# Skip buffered output covered by a pending seek in gzdirect()

## Problem

`gzseek()` on a reader that has not read yet only records the skip (`state->skip`), with nothing buffered. `gzdirect()` (`gzread.c`) then calls `gz_look()`, which, for input that is not gzip, copies what it read into the output buffer: `x.have` becomes nonzero while the skip is still pending. `gzgetc()` (the function and the `gzgetc()` macro of `zlib.h`, which cannot be changed) takes bytes from the output buffer without checking for a skip request, which is only right while a pending skip implies an empty output buffer. So after `gzseek()` and `gzdirect()`, `gzgetc()` returned the first byte of the file instead of the byte at the position sought, and added it to `x.pos`; after a seek to the largest position, `gztell()` then computed `x.pos + skip` with signed overflow (ISO C17 §6.5p5).

## Fix

When `gzdirect()` has called `gz_look()` and a skip is pending while output is buffered, skip the buffered bytes the seek covers, as `gzseek()` and `gz_skip()` do: `n = min(x.have, skip)`, then `x.have -= n`, `x.next += n`, `x.pos += n`, `skip -= n`. Afterwards a pending skip again means an empty output buffer. `gzdirect()` does no input or output of its own; the rest of the skip is done by the next read, as before.

madler/zlib fixed the same case with `b2596bde` ("Apply a pending skip in gzdirect() after gz_look()."), with the same statements moved into a new function `gz_skip_have()` that `gz_skip()` and `gzdirect()` call. That commit is not cherry-picked: it does not apply to zlib-ng's `gzread.c`, and its refactor of `gz_skip()` is not needed for the fix; the behaviour is the same.

Add `gzip.seek_then_direct` in `test/test_gzseek.cc`: on a plain file "abcde", `gzseek(file, 3, SEEK_SET)`, `gzdirect()`, then `gzgetc()` must return `'d'` and `gztell()` 4; with a seek to the largest position, `gzgetc()` must return -1 and `gztell()` 5 (the end of the file).

## Related Upstream References

- madler/zlib `b2596bde` (in zlib 1.4): the same fix, through a helper `gz_skip_have()`.
- Not yet submitted to zlib-ng.

## Review Feedback Addressed

- None yet (not submitted).

## Testing

- Clang, `ZLIB_COMPAT=ON`, `WITH_OPTIM=OFF`, `-O0`, AddressSanitizer + UndefinedBehaviorSanitizer:
  - Before the fix: `gzgetc()` returns `'a'` instead of `'d'`, and the test aborts with "runtime error: signed integer overflow: 1 + 9223372036854775807" in `gztell64()`.
  - After the fix: passes.
- Clang, `ZLIB_COMPAT=OFF`, `WITH_OPTIM=ON`, same sanitizers: passes.
