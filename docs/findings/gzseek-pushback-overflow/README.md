# `gzseek` after an initial `gzungetc`: signed overflow in `gzseek64`

`gzungetc` right after `gzopen` makes the position `state->x.pos` equal to -1. A following
`gzseek` then overflows signed 64-bit arithmetic in `gzseek64`, in a range check or in the
displacement it computes. Signed overflow is undefined behaviour.

The statements, in the unpatched `gzlib.c`:

```c
    if (offset > GZ_OFF_MAX - pos)                                           /* 395 */
        ret = LSEEK(state->fd, pos - state->x.pos - (z_off64_t)state->x.have, /* 403 */
    offset = pos - state->x.pos;                                             /* 424 */
```

## Calls that reach it

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

With `SEEK_CUR` any offset reaches line 395. With `SEEK_SET` it needs a target above
`GZ_OFF_MAX + x.pos`, which is `GZ_OFF_MAX` itself after one pushed character. The complete
program is [`seek.c`](../../../tests/regression/gzseek-pushback-overflow/seek.c).

`zlib.h` allows the sequence: "If gzungetc is used immediately after gzopen or gzdopen"
(`zlib.h:1643`), pushed characters are allowed up to the output buffer size. For `gzseek` it says
that the call returns -1 if the resulting position "would not be representable in the offset
type" (`zlib.h:1687`).

## Evidence

UndefinedBehaviorSanitizer reports all three statements on the unpatched C. From the repository
root, with the `zlib/` submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzseek-pushback-overflow/run.sh
```

The script builds the zlib source twice with
`-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1`: once without any patch, and
once with `patches/*.patch`. It runs `seek.c` four times on each build (transparent and gzip input,
`SEEK_CUR` and `SEEK_SET`). The unpatched build must report a signed overflow in every run. The
patched build must report nothing; `SEEK_CUR` then returns 0 and `SEEK_SET` returns -1. The script
exits with status 0 when all eight checks hold, and its last line is:

```
ok: patched: seek set LONG_MAX = -1, no report
```

From [`report.txt`](../../../tests/regression/gzseek-pushback-overflow/report.txt), x86_64 Linux,
unpatched source, one line per statement:

```
gzlib.c:395:29: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:403:36: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
gzlib.c:424:12: runtime error: signed integer overflow: 9223372036854775807 - -1 cannot be represented in type 'long int'
```

arm64 macOS gives the same three reports at the same lines.

## Effect

The overflowed value is a file offset or a displacement. At line 403 it is passed to `lseek`; at
line 424 it becomes the pending skip. No memory error is known to follow.

## Fix

[Patch 0002](../../../patches/README.md) changes `gzseek64` in two places:

- the upper range check is evaluated only when `pos > 0`, so `GZ_OFF_MAX - pos` cannot overflow;
- after `pos += offset`, a seek from a negative position is refused when the displacement
  `pos - state->x.pos` would not fit: `state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos`
  returns -1.

Upstream: the patch is the `gzlib.c` part of
[PR #1361](https://github.com/madler/zlib/pull/1361), which is open.

## Relation to the proofs

The [safety proofs of `gzseek64` and `gzseek`](../../proof/gzip.md) are about the patched source.
