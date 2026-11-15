# `gzread`: signed overflow of the position after a seek on a device

The gz readers add the bytes they deliver to the signed position `state->x.pos` without a bound.
On Linux a transparent `gzseek` on a character device such as `/dev/zero` can set the position to
`INT64_MAX`, and the next read overflows it. This page lets a zlib maintainer reproduce the report
and judge it without reading anything else. The write-side twin is
[gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md). The test files are in
[`tests/regression/gzread-pos-overflow`](../../../tests/regression/gzread-pos-overflow/README.md).

## Status

- Undefined behaviour: signed integer overflow of `x.pos`, in `gz_read`, in the `gzgetc` function
  and in the `gzgetc()` macro of zlib.h, which runs in the caller's code. Inside the documented
  use.
- Reported by UndefinedBehaviorSanitizer on x86_64 Linux (kernel 7.0, GCC 15.2), on the pinned
  source `757f0527154291bcf6bfbd6396ecde6bedd2db95` with the patches of this repository except
  0004. It did not reproduce in a run on arm64 macOS with Apple clang. There `lseek` on
  `/dev/zero` accepted the offset and returned it, the reads delivered no byte past position
  `INT64_MAX`, and the sanitizers reported nothing. No other system was tried.
- Not submitted upstream. The verified source applies the local
  [patch 0004](../../../patches/README.md), approved by the project owner on 2026-11-12. A pull
  request text is drafted in [upstream-description.md](upstream-description.md).

## Call sequence

```c
int fd = open("/dev/zero", O_RDONLY);
gzFile f = gzdopen(fd, "r");
gzread(f, buf, 1);                       /* not gzip: transparent mode (how == COPY) */
gzseek(f, INT64_MAX, SEEK_SET);          /* lseek on the device returns 0: x.pos = INT64_MAX */
gzread(f, buf, 16);                      /* gz_read: state->x.pos += n overflows */
```

A second sequence overflows in the caller's code:

```c
gzseek(f, INT64_MAX - 4, SEEK_SET);
gzread(f, buf, 1);                       /* gz_fetch fills the whole output buffer */
gzgetc(f); gzgetc(f); gzgetc(f);         /* the macro: x.pos reaches INT64_MAX */
gzgetc(f);                               /* the macro's (g)->pos++ overflows */
```

Why the seek is accepted: `gzseek64` checks only that the target fits in `z_off64_t`. In
transparent mode it then calls `lseek` on the descriptor. On Linux, `lseek` on `/dev/zero` returns
0 and does not fail, and the device keeps delivering bytes: the retained report shows the call
with the offset `INT64_MAX - 1`. No other device was run.

The complete program is [`devzero.c`](../../../tests/regression/gzread-pos-overflow/devzero.c).

## Run

On Linux, from the repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-pos-overflow/run.sh
```

The script builds the pinned source twice with
`-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1`: with `patches/*.patch`
except 0004, and with all of them. It runs `devzero.c` in three modes on each build. Without 0004
every run must report a signed overflow of the position. With 0004 nothing may be reported, and
the reads must end with `Z_DATA_ERROR` "position overflow". The script exits with status 0 when
all six checks hold; each passing check prints a line that starts with `ok:`. On another system
the script prints `skip: needs Linux (/dev/zero with a succeeding lseek)` and checks nothing.

## Sanitizer verdict

From [`report.txt`](../../../tests/regression/gzread-pos-overflow/report.txt), x86_64 Linux,
source without patch 0004:

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:73:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
gzread.c:539:21: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

The first line is `state->x.pos += n` in `gz_read`, which is line 413 of the unpatched pinned
file. The second is the `gzgetc()` macro, expanded in `devzero.c`. The third is the `gzgetc`
function. This report was not rerun for this page: it needs Linux.

The fault-injection harness of the project gave the same report in one history in 2 000 with a
device-like `lseek`. That run is not retained here.

## Scope and severity

- **Who reaches it.** A transparent reader of a descriptor whose `lseek` succeeds without
  bounding the offset and which then delivers data. `/dev/zero` on Linux is such a descriptor,
  and the only one that was run. The program must
  seek to a position near `INT64_MAX`. For a gzip stream the same overflow needs about
  2^63 bytes of decompressed output, which is not practical.
- **Effect.** Undefined behaviour on a signed counter. With the usual wrapping, `gztell` becomes
  negative and later seeks are computed from a wrong position.
- **Memory safety.** No memory error is known to follow from the overflow. That is a reading of
  the unpatched C and it is **to confirm**. No proof of this project will confirm it: the
  registered gz safety theorem (`gz_sequence_safety_public`, which proves
  `Goal.gz_sequence_safety`) is about the source with patch 0004, in which the overflow does not
  occur.
- **Severity.** Low: it needs a position near 2^63 on a device.

## What `zlib.h` says

Every call is documented use: zlib.h allows `gzdopen` on any descriptor, a seek to any position
that fits the offset type, and reads after it. About the limit it says only that `gzseek` returns
-1 if the resulting position "would not be representable in the offset type" (`zlib.h:1687`). It
says nothing about reads that move the position past that limit, or about devices.

## Fix

[0004-gz-position-overflow.patch](../../../patches/0004-gz-position-overflow.patch), read side:
a helper `gz_room(state, max)` returns `max`, or less if delivering `max` more bytes would carry
`x.pos` past `GZ_OFF_MAX`. `gz_fetch` fills the output buffer with at most that many bytes (and at
least one, so that the end of the input is still found), so that `x.pos + x.have` never exceeds
`GZ_OFF_MAX` and the `gzgetc()` macro stays defined. `gz_read` and `gzgets` deliver at most that
many bytes; if data remains that cannot be delivered, they discard it and set `Z_DATA_ERROR`
"position overflow". Below `GZ_OFF_MAX - 2 * size` nothing changes. Near the limit the same bytes
are delivered, in smaller fills. At the limit, the end of the input is still reported as before;
only data that would have overflowed the position becomes an error.

The invariant the patch keeps is `x.pos + x.have <= GZ_OFF_MAX` whenever a call returns. Every
producer of `x.have` keeps it:

- `gz_fetch` loads at most `GZ_OFF_MAX - x.pos` bytes;
- `gz_look` buffers at most `gz_room(state, avail_in)` bytes in transparent mode and records the
  same error when its input goes past that. The first version of the patch lacked this bound:
  see [gz-position-copy-overflow](../gz-position-copy-overflow.md);
- the direct paths of `gz_read` deliver at most that many bytes;
- `gzungetc` lowers `x.pos` by the byte it adds;
- a seek in transparent mode empties the buffer.

The single byte that `gz_fetch` loads at `GZ_OFF_MAX` to find the end of the input is discarded
by its only callers there, `gz_read` and `gzgets`, before they return (`gz_skip` never fetches at
`GZ_OFF_MAX`, since `x.pos + skip` is at most `GZ_OFF_MAX`). So the fast paths that take buffered
bytes one at a time (the `gzgetc` function, the `gzgetc()` macro) and `gz_skip_have` need no
check. The reproduction's `fast` run exercises these paths at `INT64_MAX - 2`.

Checks of the patch: [upstream-description.md](upstream-description.md), section Testing.

## Relation to the proofs

The [gz proof notes](../../proof/gzip.md) call this report F-1. The proofs are about the patched
source.
