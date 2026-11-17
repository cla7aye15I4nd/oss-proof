# Patches

The verified source is zlib 1.4 (upstream commit `99623ef7`) with the seven patches of this
directory applied in name order. Every theorem is about that patched source.

Each patch fixes one issue of zlib without whose fix a safety statement cannot be proved, or a
promise of `zlib.h` does not hold. Each is as small as the fix allows. A patch that was submitted
upstream is the submitted fix. Each applies to the pinned source on its own, except 0004, which
changes the lines that 0003 moves and so applies after 0003.
[Findings](https://www.dataisland.org/zlib-f/en/findings.html) lists the issues in one table, with
the calls that reach each issue and the evidence. Each patch has one reproduction under
`tests/regression/`, which the differential test runs: it builds the source with every patch but its
own (for 0003, also without 0004) and shows the defect on the real C, and builds the verified source
and shows none. `gzseek64` and `gz_skip_have` compute `x.next += 0` on a pointer that may never have
been written or may point into a freed caller buffer; that needs no patch, because the model accepts
adding zero to any pointer, a stated limit of the model.

## 0001-inflate-copy-pointer-equality.patch

`inflateCopy` compares a pointer into the static fixed-code table with a pointer into the state's
own code array using `>=` and `<=`, which C defines only for pointers into one object. The patch
tests the same condition with pointer equality.

Covered by: `Goal.inflateCopy_safety`.

Upstream: the patch is the commit of [PR #1369](https://github.com/madler/zlib/pull/1369), which
the maintainer answered with "Applied". zlib 1.4 does not contain it.

## 0002-gzseek-negative-position-overflow.patch

An initial `gzungetc` sets `state->x.pos` to -1. Calls: `gzopen`, `gzungetc`, then `gzseek` with
`SEEK_CUR`, or with `SEEK_SET` to a target near `GZ_OFF_MAX`. The `SEEK_CUR` range check evaluates
`GZ_OFF_MAX - pos` with a negative `pos`, and the `SEEK_SET` displacement `pos - state->x.pos`
overflows signed arithmetic. The
patch evaluates the range check only for a positive `pos`, and refuses a seek whose displacement
from a negative position does not fit in `z_off64_t`. These are the only two subtractions of a
negative position in `gzseek64`.

Covered by: `Goal.gzseek64_safety`, `Goal.gzseek_safety`, and `Goal.gz_sequence_safety`.

Upstream: the patch is the `gzlib.c` part of
[PR #1361](https://github.com/madler/zlib/pull/1361), which is open.

## 0003-gzread-partial-copy-read-error.patch

In transparent (`COPY`) mode, when `read` supplies some bytes and then fails, `gz_load` leaves
the partial count in `x.have` and returns -1, and `gz_fetch` returns before its assignment of
`x.next`. Calls: `gzread` (or `gzgetc`, `gzgets`) on input that is not gzip, when the descriptor
fails after partial data. The readers then take the partial bytes through a stale `x.next`, which
can be outside the output buffer. The patch sets
`state->x.next = state->out` before `gz_load`, so the pointer matches the bytes on every return.

Covered by: `Goal.gzread_safety`, `Goal.gzfread_safety`, `Goal.gzgetc_safety`,
`Goal.gzgetc__safety`, `Goal.gzgets_safety`, `Goal.gzungetc_safety`, and `Goal.gz_sequence_safety`.

Upstream: the patch is the change of [PR #1363](https://github.com/madler/zlib/pull/1363), which
is open.

## 0004-gzread-position-overflow.patch

The gz readers add to the signed position `state->x.pos` without a bound, so a read at a position
near `GZ_OFF_MAX` overflows it: in `gz_read`, `gzgets`, `gzgetc`, and the `gzgetc()` macro of
`zlib.h`. Calls: `gzseek` to near
`2^63` on a device whose `lseek` succeeds without moving (Linux `/dev/zero`), then `gzread` or
`gzgetc`. The patch keeps `x.pos + x.have` at most `GZ_OFF_MAX`, which the `gzgetc()` macro needs
(it does `pos++` on any buffered byte). A helper `gz_room(state, max)` bounds what the transparent
branch of `gz_look` buffers, what `gz_fetch` loads (at least one byte, to tell the end of the input
from data past the limit) and what `gz_read` and `gzgets` deliver. Data past `GZ_OFF_MAX` gives
`Z_DATA_ERROR` "position overflow". Every addition to `x.pos` in `gzread.c` then adds a count
bounded by `gz_room`.

Covered by: the goals of 0003, `Goal.gzdirect_safety` (`gz_look`), and the clause of
`Goal.gzgetc_safety` for the `gzgetc()` macro.

Upstream: local patch, not submitted.

## 0005-gzwrite-position-overflow.patch

The gz writers add to `state->x.pos` without a bound: signed overflow in `gz_write`, `gzputc` and
`gzprintf` at a position near `GZ_OFF_MAX`. Calls: `gzseek` forward to near
`2^63` on a transparent writer to a sink that accepts the zeros (`/dev/null`), then `gzwrite` or
`gzputc`. The patch makes `gz_write` and `gzvprintf` refuse a write that would carry the position
past `GZ_OFF_MAX`, with `Z_DATA_ERROR` "position overflow", and stops the fast path of `gzputc` at
`GZ_OFF_MAX`, so that it falls to `gz_write`. These are the only additions to `x.pos` in
`gzwrite.c` besides `gz_zero`, whose count `gzseek64` already bounds. One hunk changes the
`gzprintf` of the `!STDC` build in the same way; that code is outside the default build and so
outside the verified source.

Covered by: `Goal.gzwrite_safety`, `Goal.gzfwrite_safety`, `Goal.gzputc_safety`,
`Goal.gzputs_safety`, `Goal.gzprintf_safety`, `Goal.gzvprintf_safety`, and
`Goal.gz_sequence_safety`.

Upstream: local patch, not submitted.

## 0006-gzoffset-negative-lseek.patch

`gzoffset64` takes `LSEEK(fd, 0, SEEK_CUR)`, refuses only -1, and when reading subtracts the
buffered input `state->strm.avail_in`. On Linux, `lseek` on a file with unsigned offsets
(`/proc/<pid>/mem`, `/dev/mem`) returns any 64-bit offset, negative ones included, and POSIX
allows negative offsets for some devices. Calls: `gzdopen` on such a descriptor, `gzread`, the
caller moves the descriptor to a large negative offset, then `gzoffset64`: the subtraction
overflows `z_off64_t` (reproduction under `tests/regression/gzoffset-negative-lseek/`). The patch
returns -1 for every negative result of `lseek`, as for a failure: a negative value is not a file
offset. With a result of at least 0 the subtraction cannot overflow, and no other result of
`lseek` in the gz code enters arithmetic.

Covered by: `Goal.gzoffset64_safety`, `Goal.gzoffset_safety`, and `Goal.gz_sequence_safety`.

Upstream: local patch, not submitted.

## 0007-deflatebound-fixed-conservative.patch

With `windowBits` 15, `memLevel` 8 and strategy `Z_FIXED`, `deflateBound` returns the tight default
bound, which counts on a stored block as the fallback of every block. A block that crosses a window
slide has none, and `deflate_fast` (levels 1 to 3) takes 3-byte matches at any distance, which cost
25 bits with fixed codes. The output then exceeds the bound, and one `deflate(Z_FINISH)` call with
that room returns `Z_OK`, against the promise of `zlib.h`. The patch makes `deflateBound_z` return a
conservative bound also when the strategy is `Z_FIXED` (`fixedlen` for levels 1 to 9, `storelen` for
level 0, as for the other parameter sets), which allows 9 bits per byte. No other strategy and no
other parameter set changes. It fixes a broken promise, not a memory error: no safety goal depends
on the value of the bound.

Covered by: `Goal.deflate_bound_default` and `Goal.deflate_completes_default`, which use the bound.

Upstream: local patch, not submitted.
