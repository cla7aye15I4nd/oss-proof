# `gzread`: signed overflow of the position after a seek on a device

The gz readers add the bytes they deliver to the signed position `state->x.pos` without a bound.
On Linux a transparent `gzseek` on a character device such as `/dev/zero` can set the position to
`INT64_MAX`, and the next read overflows it: in `gz_read`, in the `gzgetc` function, and in the
`gzgetc()` macro of `zlib.h`, which runs in the caller's code. Signed overflow is undefined
behaviour. The write side is [gzwrite-pos-overflow](../gzwrite-pos-overflow/README.md).

## Calls that reach it

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

`gzseek64` checks only that the target fits in `z_off64_t`. In transparent mode it then calls
`lseek` on the descriptor. On Linux, `lseek` on `/dev/zero` returns 0 and does not fail, and the
device keeps delivering bytes.

A transparent reader reaches the overflow on a descriptor whose `lseek` succeeds without bounding
the offset and which then delivers data, after a seek to a position near `INT64_MAX`. Linux
`/dev/zero` is the descriptor that was run. A gzip stream reaches the same overflow only after
about 2^63 bytes of decompressed output.

Every call is documented use: `zlib.h` allows `gzdopen` on any descriptor, a seek to any position
that fits the offset type, and reads after it. About the limit it says only that `gzseek` returns
-1 if the resulting position "would not be representable in the offset type" (`zlib.h:1687`).

The complete program is [`devzero.c`](../../../tests/regression/gzread-pos-overflow/devzero.c).

## Evidence

UndefinedBehaviorSanitizer reports the overflow on x86_64 Linux, on the C with every patch except
0004. On Linux, from the repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-pos-overflow/run.sh
```

The script builds the zlib source twice with
`-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1`: with `patches/*.patch`
except 0004, and with all of them. It runs `devzero.c` in three modes on each build. Without 0004
every run must report a signed overflow of the position. With 0004 nothing may be reported, and
the reads must end with `Z_DATA_ERROR` "position overflow". The script exits with status 0 when
all six checks hold. On another system the script prints
`skip: needs Linux (/dev/zero with a succeeding lseek)` and checks nothing.

From [`report.txt`](../../../tests/regression/gzread-pos-overflow/report.txt), x86_64 Linux,
source without patch 0004:

```
gzread.c:414:22: runtime error: signed integer overflow: 9223372036854775807 + 16 cannot be represented in type 'long int'
devzero.c:73:17: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
gzread.c:539:21: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

The first line is `state->x.pos += n` in `gz_read` (line 413 of the unpatched file). The second
is the `gzgetc()` macro, expanded in `devzero.c`. The third is the `gzgetc` function.

## Effect

Undefined behaviour on a signed counter. With the usual wrapping, `gztell` becomes negative and
later seeks are computed from a wrong position. No memory error is known to follow from the
overflow. That is a reading of the unpatched C and it is **to confirm**; the theorems do not
confirm it, because they are about the source with patch 0004, in which the overflow does not
occur.

## Fix

[Patch 0004](../../../patches/README.md), read side. A helper `gz_room(state, max)` returns
`max`, or less if delivering `max` more bytes would carry `x.pos` past `GZ_OFF_MAX`. The patch
keeps `x.pos + x.have <= GZ_OFF_MAX` whenever a reading call returns, which is what the
`gzgetc()` macro needs. Every producer of `x.have` keeps it:

- `gz_fetch` fills the output buffer with at most `gz_room` bytes, and at least one, so that the
  end of the input is still found;
- `gz_look` buffers at most `gz_room(state, avail_in)` bytes in transparent mode and records
  `Z_DATA_ERROR` "position overflow" when its input goes past that;
- `gz_read` and `gzgets` deliver at most `gz_room` bytes; if data remains that cannot be
  delivered, they discard it and set the same error;
- `gzungetc` lowers `x.pos` by the byte it adds;
- a seek in transparent mode empties the buffer.

The single byte that `gz_fetch` loads at `GZ_OFF_MAX` to find the end of the input is discarded
by its only callers there, `gz_read` and `gzgets`, before they return. So the paths that take
buffered bytes one at a time (the `gzgetc` function, the `gzgetc()` macro) and `gz_skip_have`
need no check.

Below `GZ_OFF_MAX - 2 * size` nothing changes. Near the limit the same bytes are delivered, in
smaller fills. At the limit, the end of the input is reported as before; only data that would
have overflowed the position becomes an error.

Upstream: the patch is local and has not been submitted.

## Relation to the proofs

The [gzip proofs](../../proof/gzip.md) are about the patched source.
