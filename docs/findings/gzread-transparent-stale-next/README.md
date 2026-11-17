# `gzread` copies from a stale `x.next` after a partial read that then fails

In transparent mode (the input is not gzip), when `read()` returns some bytes and the next
`read()` fails, `gz_fetch` returns before it sets `state->x.next`. The reader then copies the
partial bytes from the old pointer, which can be one past the end of the output buffer: a heap
read out of bounds.

## Calls that reach it

```c
gzFile f = gzopen("raw.dat", "rb");     /* 128 bytes, not gzip: transparent mode */
gzbuffer(f, 16);                         /* the output buffer is 32 bytes */
for (int i = 0; i < 48; i++)
    gzgetc(f);                           /* x.have == 0; x.next == out + 32, one past the buffer */
/* from here on, read() on the descriptor returns 1 byte, then fails with EIO */
gzread(f, buf, 1);                       /* gzread.c:369: memcpy(buf, state->x.next, n) */
```

What happens in the last call, in the unpatched `gzread.c`:

1. `gz_read` finds no buffered output and calls `gz_fetch`.
2. In `gz_fetch`, `case COPY`, `gz_load` stores the one byte it got, sets `x.have = 1`, and
   returns -1 because the next `read()` failed with an error other than `EAGAIN`.
3. `gz_fetch` returns -1 at once. The assignment `state->x.next = state->out` after the `gz_load`
   call is skipped.
4. `gz_read` sees `x.have != 0` and copies one byte from `x.next`, which still is `out + 32`.

A transparent reader reaches it when its descriptor delivers part of a request and then fails
with an error other than `EAGAIN`: a failing disk, a network file system, a socket or pipe that
is reset. The compressed-data path (`case GZIP`) is not affected.

`zlib.h` describes the situation as handled: "If some data was read before an error, then that
data is returned until exhausted" (`zlib.h:1492`). The unpatched code returns the right count but
the wrong bytes.

The complete program is [`stale.c`](../../../tests/regression/gzread-transparent-stale-next/stale.c).
It defines its own `read()`, which the statically linked library calls, to make the second
`read()` fail.

## Evidence

AddressSanitizer reports the read on the unpatched C. From the repository root, with the `zlib/`
submodule checked out:

```sh
ZLIB_SRC=$PWD/zlib bash tests/regression/gzread-transparent-stale-next/run.sh
```

The script builds the zlib source twice with
`-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1`:
once without any patch, and once with `patches/*.patch`. The unpatched build must report the
read. The patched build must report nothing, and `gzread` must return 1 and keep the error
`Z_ERRNO`. The script exits with status 0 when both hold, and its last line is:

```
ok: patched: gzread returns the byte and keeps Z_ERRNO, no report
```

From [`report.txt`](../../../tests/regression/gzread-transparent-stale-next/report.txt), x86_64
Linux, unpatched source:

```
==PID==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x7926271e0060 at pc 0x7cf628f2901f bp 0x7fff02a49d20 sp 0x7fff02a494c8
READ of size 1 at 0x7926271e0060 thread T0
    #2 0x64c563f4acad in gz_read unpatched/gzread.c:369
    #3 0x64c563f4b208 in gzread unpatched/gzread.c:454
0x7926271e0060 is located 0 bytes after 32-byte region [0x7926271e0040,0x7926271e0060)
```

The 32-byte region is the output buffer allocated in `gz_look`. arm64 macOS gives the same
report.

## Effect

The bytes returned to the caller as file data are read through the stale pointer, not from where
`gz_load` stored them. The count is the partial count, at most twice the buffer size. The stale
pointer is where the previous output ended, so the read can start at the end of the output
buffer and run past the allocation, as in the reproduction, or lie inside the buffer and return
old data. It is triggered by an I/O error, not by the bytes of the file.

## Fix

[Patch 0003](../../../patches/README.md): in `gz_fetch`, `case COPY`, the assignment
`state->x.next = state->out;` moves before the `gz_load` call, so that it also holds when
`gz_load` returns -1 with a partial count.

Upstream: the patch is the change of [PR #1363](https://github.com/madler/zlib/pull/1363), which
is open.

## Relation to the proofs

The [safety proofs of the gz readers](../../proof/gzip.md) are about the patched source.
