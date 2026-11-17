# `deflateBound` is too small for `Z_FIXED` at levels 1 to 3

With `windowBits` 15, `memLevel` 8, strategy `Z_FIXED` and level 1, 2 or 3, the unpatched
`deflateBound` returns a bound smaller than the stream `deflate` produces. One
`deflate(Z_FINISH)` call with that room then returns `Z_OK`, against the promise of `zlib.h`. It
is a broken promise, not a memory error: no behaviour is undefined, and the sanitizers report
nothing.

`zlib.h`, `deflateBound`: "If that first deflate() call is provided the sourceLen input bytes, an
output buffer allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then
deflate() is guaranteed to return Z_STREAM_END."

With `windowBits` 15 and `memLevel` 8, `deflateBound` returns the tight bound
`n + (n >> 12) + (n >> 14) + (n >> 25) + 7 + wraplen`. That bound counts on a stored block as the
fallback of every block: about 5 bytes for each block of at most 16383 symbols. Two facts break it:

1. `FLUSH_BLOCK_ONLY` passes `buf = NULL` to `_tr_flush_block` when `block_start` is negative,
   that is when a window slide happened inside the block. Then no stored block is possible.
2. `deflate_fast` (levels 1 to 3) accepts a match of length 3 at any distance (only `deflate_slow`
   has the `TOO_FAR` test). With fixed codes a match of length 3 at a distance above 16384 costs
   7 + 5 + 13 = 25 bits, more than the 24 bits of its bytes. `Z_FIXED` forces the fixed codes.

An input made of 3-byte copies from distances in (16384, 32000] gives blocks of 16383 such matches,
about 49 KB each. They cross a slide, have no stored fallback, and grow by 1/24.

## Calls that reach it

```c
deflateInit2(&s, level, Z_DEFLATED, 15, 8, Z_FIXED);   /* level 1, 2 or 3 */
bound = deflateBound(&s, n);
s.next_in = in;   s.avail_in = n;                      /* 3-byte copies from far distances */
s.next_out = out; s.avail_out = bound;
deflate(&s, Z_FINISH);                                 /* returns Z_OK, not Z_STREAM_END */
```

Only `windowBits` 15 with `memLevel` 8 (the tight bound), `Z_FIXED` and levels 1 to 3 are
affected. The other parameter sets use the conservative bounds, which allow 9 bits per byte. With
the default strategy, dynamic codes give a far 3-byte match a short code. `compress`, `compress2`
and `compressBound` use the default strategy and are not affected.

## Evidence

The reproduction [`repro.c`](repro.c) on the C without patch 0006, with and without
AddressSanitizer and UndefinedBehaviorSanitizer. From [`report.txt`](report.txt), for
n = 1,000,000:

```
level 1: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1007343
level 2: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1008565
level 3: deflateBound 1000318, deflate(Z_FINISH) with that room returns 0 (not Z_STREAM_END), stream needs 1008570
```

Levels 4 to 9 end with `Z_STREAM_END`.

The scope comes from a search on the real C (`tests/goals/deflate-bound`) over every `windowBits`
9 to 15, `memLevel` 1 to 9, level 1 to 9, strategy default and `Z_FIXED`, copy lengths 3 to 5 and
literal rates 0 to 50%. Without patch 0006 it fails only for `windowBits` 15, `memLevel` 8,
`Z_FIXED`, levels 1 to 3, copy length 3. With the patch it fails in no case.

## Fix

[Patch 0006](../../../patches/README.md): in `deflateBound_z` the conservative bounds apply also
when the strategy is `Z_FIXED`: `fixedlen` at levels 1 to 9, `storelen` at level 0, as for the
other parameter sets. Fixed codes cost at most 9 bits per byte, which `fixedlen` covers. No other
strategy and no other parameter set changes.

With the patch, for n = 1,000,000 the bound is 1,130,869, and one `deflate(Z_FINISH)` with that
room returns `Z_STREAM_END` at every level 1 to 9, with and without the sanitizers. The stream
sizes are unchanged.

Upstream: the patch is local and has not been submitted.

## Relation to the proofs

No safety goal depends on the value of the bound. The translation of `deflateBound_z` and the
specification of its value follow the patched C. Without the patch, a statement that `deflate`
with `Z_FINISH` and `deflateBound` bytes of room ends the stream, for every strategy
(`DeflateCompletes`), is false.
