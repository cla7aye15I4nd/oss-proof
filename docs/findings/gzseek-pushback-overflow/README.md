# `gzseek` after an initial `gzungetc`: signed overflow in `gzseek64`

`gzungetc` right after `gzopen` makes the position `state->x.pos` equal to -1. A following `gzseek`
then overflows signed 64-bit arithmetic in `gzseek64`, in a range check or in the displacement it
computes. This page lets a zlib maintainer reproduce the reports and judge them without reading
anything else. The test files are in
[`tests/regression/gzseek-pushback-overflow`](../../../tests/regression/gzseek-pushback-overflow/README.md).

## Status

- Undefined behaviour: signed integer overflow, at three statements of `gzlib.c`. Inside the
  documented use.
- Reported by UndefinedBehaviorSanitizer on the unmodified pinned source
  (`757f0527154291bcf6bfbd6396ecde6bedd2db95`, upstream `develop`), on x86_64 Linux (GCC 15.2) and
  on arm64 macOS (Apple clang 21).
- Fix submitted upstream as [PR #1361](https://github.com/madler/zlib/pull/1361). The pull request
  is open, and the maintainer had not answered when its state was read on 2026-11-14. The verified
  source applies the `gzlib.c` part as [patch 0002](../../../patches/README.md).

## Call sequence

Two sequences, each on a fresh handle. The file may be a gzip file or any other file
(transparent mode).

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* allowed at position 0: x.pos becomes -1 */
gzseek(f, 1, SEEK_CUR);             /* gzlib.c:395: GZ_OFF_MAX - pos, with pos == -1 */
```

```c
gzFile f = gzopen(path, "rb");
gzungetc('Q', f);                   /* x.pos becomes -1 */
gzseek(f, LONG_MAX, SEEK_SET);      /* the range checks pass (pos is 0, then LONG_MAX);
                                       pos - state->x.pos is LONG_MAX + 1:
                                       gzlib.c:403 (transparent), gzlib.c:424 (gzip) */
```

The statements, in the pinned `gzlib.c`:

```c
    if (offset > GZ_OFF_MAX - pos)                                           /* 395 */
        ret = LSEEK(state->fd, pos - state->x.pos - (z_off64_t)state->x.have, /* 403 */
    offset = pos - state->x.pos;                                             /* 424 */
```

The complete program is [`seek.c`](../../../tests/regression/gzseek-pushback-overflow/seek.c).

## Run

From the repository root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzseek-pushback-overflow/run.sh
```

The script builds the pinned source twice with
`-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1`: once without any patch, and
once with `patches/*.patch`. It runs `seek.c` four times on each build (transparent and gzip input,
`SEEK_CUR` and `SEEK_SET`). The unpatched build must report a signed overflow in every run. The
patched build must report nothing; `SEEK_CUR` then returns 0 and `SEEK_SET` returns -1. The script
exits with status 0 when all eight checks hold, and its last line is:

```
ok: patched: seek set LONG_MAX = -1, no report
```

## Sanitizer verdict

From [`report.txt`](../../../tests/regression/gzseek-pushback-overflow/report.txt), x86_64 Linux,
unpatched source, one line per statement:

```
gzlib.c:395:29: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:403:36: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:424:12: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
```

A run on arm64 macOS for this page gave the same three reports at the same lines; there the type
is printed as `off_t` and the third report is at column 18.

## Scope and severity

- **Who reaches it.** A reader that calls `gzungetc` before reading anything and then calls
  `gzseek` or `gzseek64`, in either mode. With `SEEK_CUR` any offset reaches line 395. With
  `SEEK_SET` it needs a target above `GZ_OFF_MAX + x.pos`, which is `GZ_OFF_MAX` itself after one
  pushed character.
- **Effect.** The overflowed value is a file offset or a displacement. At line 403 it is passed to
  `lseek`; at line 424 it becomes the pending skip. What the unpatched code does after the
  overflow, with wrapping arithmetic, was not measured. AddressSanitizer was active in the same
  runs and the first report is the overflow.
- **Severity.** Low: undefined arithmetic on a position, reachable only by an unusual call order;
  no memory error is known to follow.

## What `zlib.h` says

The sequence is documented use: "If gzungetc is used immediately after gzopen or gzdopen"
(`zlib.h:1643`), pushed characters are allowed up to the output buffer size. For `gzseek`, zlib.h
says it returns -1 if the resulting position "would not be representable in the offset type"
(`zlib.h:1687`), and that a pushed character is discarded when the stream is repositioned.

## Fix

[PR #1361](https://github.com/madler/zlib/pull/1361) at head `ce2248ee9750`, `gzlib.c` part:

- the upper range check is evaluated only when `pos > 0`, so `GZ_OFF_MAX - pos` cannot overflow;
- after `pos += offset`, a seek from a negative position is refused when the displacement
  `pos - state->x.pos` would not fit: `state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos`
  returns -1.

[Patch 0002](../../../patches/README.md) is that change. The `test/example.c` part of the pull
request is not part of the verified source. The patch is removed when upstream contains the fix
and the pin moves past it.

## Relation to the proofs

The [gz proof notes](../../proof/gzip.md) call this report R-1. The safety proofs of `gzseek64`
and `gzseek` are about the patched source.
