# Bound the read position of the gz readers at GZ_OFF_MAX

Status: tests and upstream-style commit message pending

## Problem

The readers added the bytes they delivered to the signed 64-bit `x.pos` without a bound: after `gzseek` to near `2^63` on a descriptor whose `lseek` succeeds and which keeps delivering data, `x.pos += n` overflowed in `gz_read` (ISO C17 §6.5p5); the `gzgetc()` macro does the same in the caller with buffered bytes.

## Fix

Files: `gzread.c`.

The readers stop at the largest position, and the output buffer never holds bytes past it: `gz_fetch` asks for at most `GZ_OFF_MAX - x.pos` bytes of output (`gz_load` length, `avail_out`) when `x.pos > 0`, and fails with `Z_DATA_ERROR` ("read position does not fit in z_off64_t") at `x.pos == GZ_OFF_MAX`; `gz_read` limits each step to `GZ_OFF_MAX - x.pos` bytes (its direct reads into the caller's buffer bypass the output buffer) and, when that is 0, sets the same error and returns what it has. So `x.pos + x.have <= GZ_OFF_MAX` holds whenever a call returns, and the `gzgetc()` macro of `zlib.h`, which takes bytes from the output buffer in the caller, reaches at most `GZ_OFF_MAX` and then calls `gzgetc()`, which returns -1; `gzgetc`'s and `gzgets`' own copies need no bound (they take at most `x.have` bytes). `gz_look`'s copy of the first input needs none either: it runs only before any data is delivered (`x.pos + x.have <= 0`). Both tests compare in `uint64_t`, which holds every `unsigned` and every non-negative `z_off64_t`. Below `GZ_OFF_MAX - 2 * size` nothing changes; above it `gz_fetch` reads or inflates less per call. The writers report the same error past `GZ_OFF_MAX` (patch 0014).

## Related Upstream References

- Related madler/zlib PR: https://github.com/madler/zlib/pull/1405 (open; a different design with a `gz_room()` helper).

## Review Feedback Addressed

- None yet.

## Testing

- Reproductions in the project's regression suite: `gzread-position-overflow`, `gzgetc-macro-position`, `gzread-position-32bit`.
- Confirmed on real C: yes (UndefinedBehaviorSanitizer, `gzread.c:356`; the macro: in the caller, `tests/regression/gzgetc-macro-position`).
- No GoogleTest case in this series yet.
