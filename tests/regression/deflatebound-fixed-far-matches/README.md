# deflateBound is too small under Z_FIXED (patch 0007)

With `windowBits` 15, `memLevel` 8 and strategy `Z_FIXED`, `deflateBound` returns the tight default
bound, but `deflate_fast` (levels 1 to 3) codes far 3-byte matches at 25 bits each with fixed codes,
and a block that crosses a window slide has no stored fallback. `repro.c` compresses 1,000,000
such bytes at levels 1 to 9 in one `deflate(Z_FINISH)` call with exactly the bound as room; `zlib.h`
promises `Z_STREAM_END`. `run.sh` builds the source with every patch but 0007 and the verified
source: in the first some level returns `Z_OK`, in the second every level ends (`report.txt`).

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/deflatebound-fixed-far-matches/run.sh`.
