# deflateBound is too small for Z_FIXED at levels 1 to 3

Status: reproduced on the pinned C (upstream `develop` 757f052, unpatched; the local patches do not
touch `deflate.c` or `trees.c`), with and without AddressSanitizer and UndefinedBehaviorSanitizer,
and on a system zlib 1.2.12. Not yet reported upstream; whether upstream knows it is **to confirm**.
It is a broken API promise, not a memory error: the sanitizers report nothing.

zlib.h, `deflateBound`: "If that first deflate() call is provided the sourceLen input bytes, an
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

Reproduction: `repro.c` (no clock, no input). Output on the pinned C under the sanitizers:
`report.txt`. For n = 1,000,000 the bound is 1,000,318; at levels 1, 2 and 3 one
`deflate(Z_FINISH)` with that room returns `Z_OK`, and the stream needs 1,007,343, 1,008,565 and
1,008,570 bytes. Levels 4 to 9 end.

Older releases fail more widely. On a system zlib 1.2.12 the same input fails at every level 1 to
9 (for n = 1,000,000 the stream needs up to 1,031,475 bytes). There `Z_FIXED` forced a fixed block
even when a stored block was smaller. Upstream commit 7fabcb5 ("Fix bug in block type selection when
Z_FIXED used", zlib 1.2.13) lets the smaller stored block win again. That leaves only the blocks
without a stored fallback (`buf == NULL`), and only `deflate_fast` takes far 3-byte matches. No
entry of `ChangeLog` up to 1.3.2.1 addresses this case (checked: every `deflateBound` and `Z_FIXED`
entry); a web search found no upstream issue. Whether upstream knows it stays **to confirm**.

Scope, from the statement test (`tests/goals/deflate-bound`, a targeted search over every
`windowBits` 9 to 15, `memLevel` 1 to 9, level 1 to 9, strategy default and `Z_FIXED`, copy
lengths 3 to 5, literal rates 0 to 50%): only `windowBits` 15 with `memLevel` 8 (the tight bound),
`Z_FIXED`, levels 1 to 3. The other parameter sets use the conservative bounds, which allow 9 bits
per byte. The default strategy is not affected in these tests: dynamic codes give a far 3-byte match
a short code. `compress`, `compress2` and `compressBound` use the default strategy and are not
affected.

Effect on the proof: `DeflateCompletes` (`ZlibF/Spec/Functional/Sequences.lean`) quantifies over
every strategy, so it is false as stated for this case. A correction needs a decision: a premise
that excludes `Z_FIXED` at levels 1 to 3 with the tight bound (listed in `docs/deviations.md`), or
a local patch. A minimal fix in `deflateBound` would use the conservative bound for `Z_FIXED`
(fixed codes cost at most 9 bits per byte, which the `fixedlen` bound covers).
