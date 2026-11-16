# x.next left in the caller's buffer after a direct read

After a large `gzread` that decompresses straight into the caller's buffer, the gz state keeps a
pointer into that buffer. If the caller frees the buffer, a later `gzseek` or `gzdirect` adds zero
to the dangling pointer. That is undefined by the letter of C, and nothing else is known to go
wrong.

Status: undefined by the letter of C. No sanitizer reports it, and no misbehaviour has been
observed, so this is not listed as a confirmed issue. Fixed in the verified source by the local
patch [0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch),
which has not been submitted upstream. The same patch fixes
[gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md).

Source: upstream `develop` at commit `757f0527154291bcf6bfbd6396ecde6bedd2db95`, with patches 0001 to 0004.
`gzlib.c` and `gzread.c` are byte-identical in zlib 1.4 (commit `99623ef7097352da7993ba614161fd6a311e046e`), the revision this project verifies;
no run on that revision is recorded here.
The [gzip proof page](../../proof/gzip.md) is about the source with all patches.

## What goes wrong

For a large request on a gzip file, `gz_read` decompresses directly into the caller's buffer:
it sets `strm.next_out` to the buffer and calls `gz_decomp`, which ends with
`state->x.next = strm->next_out - state->x.have`. `gz_read` then sets `x.have` to 0 but leaves
`x.next` pointing into the caller's buffer. The caller may free that buffer: zlib.h gives the
library no claim on it after `gzread` returns. Later:

- `gzseek64` (not transparent, output buffer empty) does `state->x.next += n` with `n == 0`;
- `gzdirect`, when the member has ended (`how == LOOK`), calls `gz_skip_have`, which does the
  same.

C11 6.2.4p2: the value of a pointer becomes indeterminate when the object it points to reaches
the end of its lifetime; 6.5.6p8: pointer arithmetic needs a pointer to an object. So the
evaluation is undefined. On x86_64 with the usual compilers, `p + 0` leaves `p` unchanged, and
the pointer is never dereferenced.

## Call sequence

```c
f = gzopen("data.gz", "rb");             /* holds 100000 bytes of data */
buf = malloc(100000);
gzread(f, buf, 100000);                  /* direct decompression: x.next into buf */
free(buf);
gzseek(f, 1, SEEK_CUR);                  /* x.next += 0 on the dangling pointer */
                                         /* or: gzdirect(f) */
```

## Evidence

Strength: by the letter of C only. No sanitizer reports it: there is no access, and `p + 0` does
not overflow. The Lean model does report it: arithmetic on a pointer into a freed block is a fault
there. With the patch, the theorem `gzseek64_dangling_next_ok` proves that a
forward seek with nothing buffered does not fault, whatever `x.next` holds.

Because no sanitizer sees it, the reproduction routes every `x.next += n` of `gzlib.c` and
`gzread.c` through a probe
([../gz-reset-next-uninitialised/probe.h](../gz-reset-next-uninitialised/probe.h); the value
computed is unchanged) and prints each evaluation with `n == 0`. Run it from the repository root,
with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash docs/findings/gz-next-dangling-after-direct-read/run.sh
```

The script builds the zlib source under AddressSanitizer and UndefinedBehaviorSanitizer twice:
with `patches/*.patch` except 0005, and with all of them. Its last line on success is
`ok: after the fix: x.next is never evaluated with n == 0`. Before the fix the probe prints two
lines. The retained [report.txt](report.txt) (x86_64 Linux, GCC 15.2) has them as follows:

```
x.next + 0 at gzread.c:313, x.next = inside the freed caller buffer
x.next + 0 at gzlib.c:435, x.next = inside the freed caller buffer
```

The retained output was produced with a `gzread.c` whose `gz_look` was two lines shorter. In the
source that `run.sh` builds, the same statement of `gz_skip_have` is line 315. A run on arm64 macOS
with Apple clang printed `gzread.c:315` and `gzlib.c:435`, and was otherwise the same.

Files: `dangling.c`, `run.sh`, `report.txt`. Before the fix the probe sees both evaluations,
after it none, and neither build gets a sanitizer report.

## Scope

Readers of gzip files that read with requests of at least twice the buffer size into memory they
free before a later `gzseek` or `gzdirect` on the same file. No observable effect on common
platforms.

## What zlib.h says

Nothing about the lifetime of the `gzread` buffer after the call returns: a caller may free it.

## Fix

The same as for [gz-reset-next-uninitialised](../gz-reset-next-uninitialised/README.md):
[0005-gz-next-zero-advance.patch](../../../patches/0005-gz-next-zero-advance.patch) advances
`x.next` only when `n` is not zero. When `n` is not zero, the output was just produced in the
library's own buffer, where `x.next` points. No result, return value or state changes on any path.

Pull request draft (one pull request for both):
[../gz-reset-next-uninitialised/upstream-description.md](../gz-reset-next-uninitialised/upstream-description.md).
