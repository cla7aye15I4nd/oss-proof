# `deflateBound` with a gzip extra field of length 2^32 − 2 or 2^32 − 1

For a gzip stream whose header was set by `deflateSetHeader` with `extra_len` equal to 2^32 − 2
or 2^32 − 1, `deflateBound` returns a bound about 64 KiB too small. One `deflate(Z_FINISH)` call
with that room then returns `Z_OK`, against the promise of `zlib.h` that such a call returns
`Z_STREAM_END`. It is a broken promise, not a memory error.

`deflateBound` adds `2 + s->gzhead->extra_len` to the wrapper length. `extra_len` is `uInt`, so
the sum is computed at 32 bits and wraps to 0 or 1 for the two lengths. `deflate` writes
`extra_len & 0xffff` bytes of the field (65534 or 65535).

For `extra_len` from 2^16 up to 2^32 − 3 the bound counts `extra_len` bytes and `deflate` writes
fewer: the bound is conservative, not wrong.

## Calls that reach it

`zlib.h` asks that `extra_len` bytes are available at `extra` and puts no upper limit on
`extra_len`. A gzip header holds at most 65535 bytes of extra field, so the two lengths are
ones the format cannot store.

```c
deflateInit2(&s, level, Z_DEFLATED, 31, 8, Z_DEFAULT_STRATEGY);   /* gzip */
head.extra = extra;
head.extra_len = 0xffffffffu;        /* or 0xfffffffeu */
deflateSetHeader(&s, &head);
bound = deflateBound(&s, n);         /* 2 + extra_len wraps */
deflate(&s, Z_FINISH);               /* with bound bytes of room: returns Z_OK */
```

## Evidence

A C driver on the real C (`tests/goals/deflate-bound/bound.c`, mode `extra`) sets five lengths,
calls `deflateBound` and then `deflate` with `Z_FINISH` and that much room. Exactly the two
lengths above fail: for 100 input bytes the bound is 125 and 126.
`tests/goals/deflate-bound/run.sh` passes only if exactly these two fail.

## Fix

None. No patch changes the sum. Upstream knows the case
([discussion in PR 1360](https://github.com/madler/zlib/pull/1360)).

## Relation to the proofs

No safety goal depends on the value of the bound. The specification of the value
(`WrapperLength`) computes `2 + extra_len` at 32 bits, as the C and the translation do. A
statement of the promise of `zlib.h` for a stream whose header was set by `deflateSetHeader`
needs a premise that excludes the two lengths.
