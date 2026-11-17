# deflateResetKeep: stale hash entries can produce a wrong match

`repro.c` compresses data A as raw deflate with `Z_NO_FLUSH`, calls `deflateResetKeep` directly,
compresses data B with `Z_FINISH`, and decodes the second stream with the kept window as the
preset dictionary. `deflateResetKeep` keeps the hash and drops the lookahead, so the hash entries
of the positions `strstart - 2` and `strstart - 1` have keys that reach into dropped bytes, and
`longest_match` can accept such a candidate with a wrong third byte: `inflate` returns
`Z_STREAM_END` with the right length and a byte that differs from B. It is a data error, not a
memory error, and no sanitizer reports it. `run.sh` builds `repro.c` with the unpatched zlib
sources and passes when the program prints three such histories; the seeds it finds depend on the
`rand` of the C library. `report.txt` is the output of one run on arm64 macOS. The history is
outside the proved domain: `zlib.h` lists `deflateResetKeep` as undocumented, and a direct call
is not a deflate stream operation ([deviations](https://www.dataisland.org/zlib-f/en/deviations.html)).
