# Refuse gzseek64() seeks whose offset arithmetic would overflow

Status: tests and upstream-style commit message pending

## Problem

Signed 64-bit overflow in `gzseek64` (ISO C17 §6.5p5): `SEEK_CUR` adds the pending skip without a bound (`gzlib.c:412`); `SEEK_SET` computes `offset - x.pos`, which overflows when `gzungetc` at position 0 left `x.pos` negative (`gzlib.c:410`); the test of the raw area computes `x.pos + offset` (`gzlib.c:417`); in copy mode with output buffered at a position near `2^63` (a descriptor whose `lseek` succeeds without moving, as Linux `/dev/zero`), a seek back computes the `lseek` offset `offset - x.have` below `INT64_MIN` (`gzlib.c:418`). Also `state->x.next += 0` on a never-set `x.next` when `gzseek` is called before the first read (wild pointer `+ 0`, ISO C17 §6.5.6p8).

## Fix

Files: `gzguts.h`, `gzlib.c`.

`gzseek64` refuses (returns -1) a seek whose arithmetic would overflow, at the point where upstream's would, and otherwise runs upstream's statements. `SEEK_SET` refuses an `offset` whose distance `offset - x.pos` does not fit in `z_off64_t` (`x.pos` is negative after `gzungetc` at position 0). `SEEK_CUR` refuses, before it clears the pending skip, when `offset + skip` (unless `past`) or the target `x.pos + offset` does not fit. A copy-mode reader seeks inside the raw data only when the `lseek` offset `offset - x.have` fits (and `x.have` fits in `z_off64_t`: `GT_OFF`, as upstream tests it two lines below); otherwise the seek rewinds and skips, as for a gzip stream. The buffer update is skipped when `n == 0`. The refusals the patch adds change nothing; on every input on which upstream's arithmetic does not overflow, the results and the state afterwards are upstream's (a refused `SEEK_CUR` before the start clears the pending skip, as upstream does; after `gzungetc` at position 0 a negative target is sought). One exception, on builds whose `z_off64_t` is 32 bits (`zconf.h` makes it `off_t` or `long` when there are no large-file functions: `-D_LARGEFILE64_SOURCE=0` on a 32-bit system, or MinGW without `_FILE_OFFSET_BITS=64`): with more than `INT_MAX` bytes of output buffered, upstream converts `x.have` to `z_off64_t` (implementation-defined) for the `lseek` offset; the patch rewinds instead. That case has no reproduction: it needs a buffer of `3 * 2^30` bytes in a 32-bit process.

## Related Upstream References

- Open zlib-ng PR https://github.com/zlib-ng/zlib-ng/pull/2525 proposes a different form of this fix (it keeps the pending skip on a refused seek and drops pushback before position 0); the form in this directory refuses only where the arithmetic would overflow and otherwise keeps the existing results.
- Related madler/zlib PR: https://github.com/madler/zlib/pull/1361 (open).

## Review Feedback Addressed

- None yet.

## Testing

- Reproductions in the project's regression suite: `gzseek-offset-overflow`, `gzseek-refusal-state`.
- Confirmed on real C: overflows yes (UndefinedBehaviorSanitizer at all four lines, through documented calls; `gzlib.c:418` on upstream and with the first version of patch 0013, as the current 0013 keeps `x.pos + x.have <= GZ_OFF_MAX`, under which it cannot occur; 0002 keeps the test so that it does not depend on 0013); `x.next + 0` by the letter of the standard.
- No GoogleTest case in this series yet.
