# deflateBound is too small for a gzip extra length of 2^32 - 2 or 2^32 - 1 (patch 0007)

With a gzip header from `deflateSetHeader` whose `extra` is not `Z_NULL`, `deflateBound` adds
`2 + extra_len` in 32-bit unsigned arithmetic, which wraps to 0 or 1 for `extra_len` 2^32 - 2 and
2^32 - 1. `deflate` writes only the low 16 bits of the length and that many bytes of `extra`, so the
stream is about 64 KiB longer than the bound. `repro.c` compresses 100 bytes with each of the two
lengths and a 65535-byte `extra` buffer in one `deflate(Z_FINISH)` call with exactly the bound as
room; `zlib.h` promises `Z_STREAM_END`. `run.sh` builds the source with every patch but 0007 and the
verified source: in the first both calls return `Z_OK`, in the second both end (`report.txt`).

Run: `ZLIB_SRC=$PWD/zlib bash tests/regression/deflatebound-gzip-extra-length/run.sh`.
