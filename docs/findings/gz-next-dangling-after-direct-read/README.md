# `x.next` left in the caller's buffer after a direct read

After a large `gzread` that decompresses straight into the caller's buffer, the gz state keeps a
pointer into that buffer. If the caller frees the buffer, a later `gzseek` or `gzdirect` adds zero
to the dangling pointer. That is undefined by the letter of C: the value of a pointer becomes
indeterminate when the object it points to reaches the end of its lifetime (C11 6.2.4p2), and
pointer arithmetic needs a pointer to an object (6.5.6p8). No sanitizer reports it. On x86_64
with the usual compilers `p + 0` leaves `p` unchanged, and the pointer is never dereferenced.

For a large request on a gzip file, `gz_read` decompresses directly into the caller's buffer:
it sets `strm.next_out` to the buffer and calls `gz_decomp`, which ends with
`state->x.next = strm->next_out - state->x.have`. `gz_read` then sets `x.have` to 0 but leaves
`x.next` pointing into the caller's buffer. Later:

- `gzseek64` (not transparent, output buffer empty) does `state->x.next += n` with `n == 0`;
- `gzdirect`, when the member has ended (`how == LOOK`), calls `gz_skip_have`, which does the
  same.

## Calls that reach it

```c
f = gzopen("data.gz", "rb");             /* holds 100000 bytes of data */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* direct decompression: x.next into buf */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* x.next += 0 on the dangling pointer */
                                         /* or: gzdirect(f) */
```

A reader of a gzip file reaches it when it reads with requests of at least twice the buffer size
into memory that it frees before a later `gzseek` or `gzdirect` on the same file. `zlib.h` gives
the library no claim on the `gzread` buffer after the call returns: a caller may free it.

## Evidence

Undefined by the letter of C, and shown with a probe. No sanitizer reports the evaluation: there
is no access, and `p + 0` does not overflow. The reproduction routes every `x.next += n` of
`gzlib.c` and `gzread.c` through a probe
([probe.h](../gz-reset-next-uninitialised/probe.h); the value computed is unchanged) and prints
each evaluation with `n == 0`. From the repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-next-dangling-after-direct-read/run.sh
```

The script builds the zlib source under AddressSanitizer and UndefinedBehaviorSanitizer twice:
with `patches/*.patch` except 0005, and with all of them. Its last line on success is
`ok: after the fix: x.next is never evaluated with n == 0`. Before the fix the probe prints two
lines. From [report.txt](report.txt), x86_64 Linux:

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

In the source with patches 0001 to 0004 the statement of `gz_skip_have` is at `gzread.c:315`.
After the fix the probe sees no evaluation, and neither build gets a sanitizer report.

The Lean model does report this case: arithmetic on a pointer into a freed block is a fault
there. With the patch, the theorem `gzseek64_dangling_next_ok` proves that a forward seek with
nothing buffered does not fault, whatever `x.next` holds.

## Fix

[Patch 0005](../../../patches/README.md) advances `x.next` only when `n` is not zero. When `n` is
not zero, the output was just produced in the library's own buffer, where `x.next` points. No
result, return value or state changes on any path. The same patch fixes
[gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md).

Upstream: the patch is local and has not been submitted.

## Relation to the proofs

The [gzip proofs](../../proof/gzip.md) are about the patched source.
