# deflateBound is too small for Z_FIXED at levels 1 to 3

Status: patched locally. Local patch 0006 (`patches/0006-deflatebound-fixed-conservative.patch`,
approved by the owner on 2026-11-15) is pending upstream: not submitted. Reproduced on the pinned
C without that patch (upstream `develop` 757f052; patches 0001 to 0005 do not touch `deflate.c` or
`trees.c`), with and without AddressSanitizer and UndefinedBehaviorSanitizer, and on a system zlib
1.2.12. Not yet reported upstream; whether upstream knows it is not yet checked with upstream.
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

Reproduction: `repro.c` (no clock, no input). Output on the pinned C without patch 0006, under the
sanitizers: `report.txt`. For n = 1,000,000 the bound is 1,000,318; at levels 1, 2 and 3 one
`deflate(Z_FINISH)` with that room returns `Z_OK`, and the stream needs 1,007,343, 1,008,565 and
1,008,570 bytes. Levels 4 to 9 end.

Older releases fail more widely. On a system zlib 1.2.12 the same input fails at every level 1 to
9 (for n = 1,000,000 the stream needs up to 1,031,475 bytes). There `Z_FIXED` forced a fixed block
even when a stored block was smaller. Upstream commit 7fabcb5 ("Fix bug in block type selection when
Z_FIXED used", zlib 1.2.13) lets the smaller stored block win again. That leaves only the blocks
without a stored fallback (`buf == NULL`), and only `deflate_fast` takes far 3-byte matches. No
entry of `ChangeLog` up to 1.3.2.1 addresses this case (checked: every `deflateBound` and `Z_FIXED`
entry); a web search found no upstream issue. Whether upstream knows it is not yet checked with
upstream.

Scope, from the statement test (`tests/goals/deflate-bound`, a targeted search over every
`windowBits` 9 to 15, `memLevel` 1 to 9, level 1 to 9, strategy default and `Z_FIXED`, copy
lengths 3 to 5, literal rates 0 to 50%): only `windowBits` 15 with `memLevel` 8 (the tight bound),
`Z_FIXED`, levels 1 to 3. The other parameter sets use the conservative bounds, which allow 9 bits
per byte. The default strategy is not affected in these tests: dynamic codes give a far 3-byte match
a short code. `compress`, `compress2` and `compressBound` use the default strategy and are not
affected.

## Fix: patch 0006

The owner chose a local patch over a premise. In `deflateBound_z` the conservative bounds now
apply also when the strategy is `Z_FIXED`: `fixedlen` at levels 1 to 9, `storelen` at level 0,
as for the other parameter sets. Fixed codes cost at most 9 bits per byte, which `fixedlen`
covers. No other strategy and no other parameter set changes.

Measured with the patch (pinned C with patches 0001 to 0006):

- `repro.c`, n = 1,000,000: the bound is 1,130,869, and one `deflate(Z_FINISH)` with that room
  returns `Z_STREAM_END` at every level 1 to 9, with and without the sanitizers. The stream sizes
  are unchanged (1,007,343 to 1,008,570 at levels 1 to 3).
- The far-match search, mode `far` of `tests/goals/deflate-bound/bound.c`: copy lengths 3 to 5,
  literal rates 0, 10, 25 and 50%, every `windowBits` 9 to 15, `memLevel` 1 to 9, level 1 to 9
  and strategy, n = 200,000. Without patch 0006 it fails in 6 cases, all `windowBits` 15,
  `memLevel` 8, `Z_FIXED`, levels 1 to 3, copy length 3, literal rates 0 and 10%. With the patch it
  fails in none. Under the sanitizers (`windowBits` 15, n = 150,000) it fails in none and the
  sanitizers report nothing.
- `tests/goals/deflate-bound/run.sh` passes with the patch; it now runs the far-match search.

Effect on the proof: with the patch, `DeflateCompletes` (`ZlibF/Spec/Functional/Sequences.lean`)
needs no premise for this case. The translation of `deflateBound_z` and the value specifications
(`deflateBoundValue`, `Api.DeflState.bound`) follow the patched C.
