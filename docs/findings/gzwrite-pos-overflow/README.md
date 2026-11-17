# `gzwrite`: signed overflow of the position after a forward seek

The gz writers add the bytes they accept to the signed position `state->x.pos` without a bound. A
transparent writer that seeks forward to near `INT64_MAX` overflows the position on the next
write, once the sink has accepted the zeros of the seek: in `gz_write` and in the fast path of
`gzputc`. Signed overflow is undefined behaviour. The read side is
[gzread-pos-overflow](../gzread-pos-overflow/README.md).

## Calls that reach it

```c
int fd = open("/dev/null", O_WRONLY);
gzFile f = gzdopen(fd, "wT");            /* transparent writer */
gzbuffer(f, 1 << 29);
gzseek(f, INT64_MAX - 10, SEEK_SET);     /* accepted: kept as a pending skip */
gzwrite(f, buf, 100);                    /* gz_zero writes INT64_MAX - 10 zeros, then
                                            gzwrite.c:230: state->x.pos += copy overflows */
```

A second sequence:

```c
gzseek(f, INT64_MAX, SEEK_SET);
gzputc(f, 'a');                          /* gzwrite.c:352: state->x.pos++ overflows */
```

`gzseek64` checks only that its target fits in `z_off64_t`. A forward seek of a writer is kept as
a pending skip, and the next write first writes that many zeros (`gz_zero`), which moves `x.pos`
to the target. `gz_write` (`x.pos += copy` and `x.pos += n`), the fast path of `gzputc`
(`x.pos++`) and `gzprintf` (`x.pos += len`) then add to it with no bound. The zero fill is 2^34
writes of 2^29 bytes; `/dev/null` accepts them.

A transparent writer reaches the overflow on a sink that accepts unbounded output: `/dev/null`,
or a pipe to a consumer that discards. For a regular file the write fails long before (`EFBIG`).
A compressing writer must compress the zeros first, about 2^63 bytes of work.

Every call is documented use. About the limit `zlib.h` says only that `gzseek` returns -1 if the
resulting position "would not be representable in the offset type" (`zlib.h:1687`).

The complete program is [`wpos.c`](../../../tests/regression/gzwrite-pos-overflow/wpos.c).

## Evidence

UndefinedBehaviorSanitizer reports the overflow on the C with every patch except 0004. From the
repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzwrite-pos-overflow/run.sh
```

The script builds the zlib source twice with
`-fsanitize=undefined -fno-sanitize-recover=undefined -g -O2`: with `patches/*.patch` except 0004,
and with all of them. It runs both sequences on each build. Without 0004 each run must report a
signed overflow of the position. With 0004 nothing may be reported, and the write must fail with
`Z_DATA_ERROR` "position overflow". The script exits with status 0 when all four checks hold, and
its last line is:

```
ok: with the fix: Z_DATA_ERROR position overflow, no report
```

By default the program is linked with `fastwrite.c`, a `write()` that accepts every byte for the
`/dev/null` descriptor without a system call: about a minute per run. `FULL=1` before the command
uses the real `/dev/null`: about 17 minutes per run on x86_64 Linux.

From [`report.txt`](../../../tests/regression/gzwrite-pos-overflow/report.txt), x86_64 Linux,
source without patch 0004, default mode:

```
gzwrite.c:230:26: runtime error: signed integer overflow: 9223372036854775797 + 100 cannot be represented in type 'long int'
gzwrite.c:352:25: runtime error: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long int'
```

The same file holds the first line from a run with the real `/dev/null`. arm64 macOS gives both
reports at the same lines in the default mode.

## Effect

Undefined behaviour on a signed counter. With the usual wrapping, `gztell` becomes negative.

## Fix

[Patch 0004](../../../patches/README.md), write side: `gz_write` refuses a write of `len` bytes
when `GZ_OFF_MAX - x.pos < len`, `gzputc` leaves its fast path at `GZ_OFF_MAX` (and `gz_write`
then refuses), and `gzprintf` refuses formatted output that would pass the limit. Each sets
`Z_DATA_ERROR` "position overflow". Writes that stay within the limit are unchanged. A write that
crosses the limit is refused as a whole, so a crossing write that an I/O error or a stall would
have stopped before the limit reports "position overflow" in place of the I/O error.

Upstream: the patch is local and has not been submitted.

## Relation to the proofs

The [gzip proofs](../../proof/gzip.md) are about the patched source.
