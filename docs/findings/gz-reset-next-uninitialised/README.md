# `gz_reset` never writes `x.next`; `gzseek` and `gzdirect` read it

Neither `gz_open` nor `gz_reset` writes the pointer `x.next` of a new reader's state. `gzseek` and
`gzdirect`, called before any output exists, add zero to that never-written pointer. That is
undefined by the letter of C: the value read is the indeterminate content of the allocation
(C11 6.2.6.1p5, J.2), and pointer arithmetic is defined only for a pointer to an object or one
past it (6.5.6p8). No sanitizer reports it, and on x86_64 with the usual compilers `p + 0` leaves
`p` unchanged.

`gz_open` allocates the `gz_state` record with `malloc` and writes some of its fields:

| Written by | Fields |
| --- | --- |
| `gz_open` | `size`, `want`, `err`, `msg`, `mode`, `level`, `strategy`, `direct`, `path`, `fd`; for a reader also `start` |
| `gz_reset`, which `gz_open` calls last | `x.have`, `x.pos`, `past`, `again`, `skip`, the error (`err`, `msg`), `strm.avail_in`; for a reader also `eof`, `how`, `junk`; for a writer also `reset` |
| neither | `x.next`, the buffer pointers `in` and `out`, every field of `strm` except `avail_in`; for a reader also `reset`; for a writer also `eof`, `how`, `junk`, `start` |

On a reader, `x.next` is first written when output is produced (`gz_look` in transparent mode,
`gz_decomp`, `gz_fetch`, `gzungetc`). Two functions evaluate it before that:

- `gzseek64`, when not in transparent mode: `n` is the part of the target that lies in the
  output buffer, 0 when the buffer is empty, and the code does `state->x.next += n` anyway.
- `gz_skip_have`, called by `gzdirect` after `gz_look`: on a gzip file `gz_look` does not
  write `x.next`, and `gz_skip_have` does `state->x.next += n` with `n == 0`.

## Calls that reach it

```c
f = gzopen("data.gz", "rb");      /* a gzip file */
gzseek(f, 3, SEEK_SET);           /* x.next += 0 on the never-written field */

f = gzopen("data.gz", "rb");
gzdirect(f);                      /* gz_look (gzip), then gz_skip_have: x.next += 0 */
```

Every reader reaches it with the first `gzseek` that is not in transparent mode with an empty
output buffer, or with `gzdirect` on a gzip file, right after `gzopen` or `gzdopen`, and after
`gzrewind`, where `x.next` keeps whatever it held before. Both are documented uses; `zlib.h`
describes `gzdirect` "used immediately after gzopen() or gzdopen()" (`zlib.h:1743`).

## Evidence

Undefined by the letter of C, and shown with a probe. No sanitizer reports the evaluation:
`p + 0` on an arbitrary value is neither an out-of-bounds access nor a pointer overflow, and
MemorySanitizer does not report an uninitialised value that is only copied. The reproduction
therefore routes every `x.next += n` of `gzlib.c` and `gzread.c` through a probe (`probe.h`; the
value computed is unchanged) and prints each evaluation with `n == 0`. From the repository root,
with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-reset-next-uninitialised/run.sh
```

The script builds the zlib source under AddressSanitizer and UndefinedBehaviorSanitizer twice:
with `patches/*.patch` except 0005, and with all of them. Its last line on success is
`ok: after the fix: x.next is never evaluated with n == 0`. Before the fix the probe prints two
lines. From [report.txt](report.txt), x86_64 Linux; under AddressSanitizer fresh allocations are
filled with `0xbe`:

```
x.next + 0 at gzlib.c:435, x.next = 0xbebebebebebebebe
x.next + 0 at gzread.c:313, x.next = 0xbebebebebebebebe
```

In the source with patches 0001 to 0004 the statement of `gz_skip_have` is at `gzread.c:315`.
After the fix the probe sees no evaluation, and neither build gets a sanitizer report.

The Lean model does not see this case: a pointer field in fresh memory is `NULL` there, and
`NULL + 0` passes. The source review that a pointer field is written before it is read
([safety](../../spec/safety.md), section 3) is what exposes it.

## Fix

[Patch 0005](../../../patches/README.md): in `gzseek64` and `gz_skip_have`, `x.next` advances
only when `n` is not zero. When `n` is not zero, `x.have` is not zero, so the field was written
when that output was produced. Initialising `x.next` to `NULL` in `gz_reset` would not do:
`NULL + 0` is itself undefined in C, and clang's `-fsanitize=pointer-overflow` reports it. No
result, return value or state changes on any path. The same patch fixes
[gz-next-dangling-after-direct-read](../gz-next-dangling-after-direct-read/README.md).

Upstream: the patch is local and has not been submitted.

## Relation to the proofs

The [gzip proofs](../../proof/gzip.md) are about the patched source.
