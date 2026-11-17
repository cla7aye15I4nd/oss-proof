#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflate-resetkeep-stale-hash/run.sh
# Builds repro.c with the unpatched zlib sources and runs it: raw deflate of data A with Z_NO_FLUSH,
# a direct deflateResetKeep, then data B with Z_FINISH. The second stream is decoded with the kept
# window as the dictionary. The program must print three histories whose decoding differs from B.
# The history is outside the proved domain: a direct deflateResetKeep is not a deflate stream
# operation (docs/en/deviations.md).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflate-resetkeep-stale-hash}
mkdir -p "$work"
cc -O1 -I"$src" "$here/repro.c" "$src"/{adler32,crc32,deflate,inflate,inftrees,inffast,trees,zutil}.c \
  -o "$work/stale-hash" || exit 2
out=$("$work/stale-hash" 2>&1)
printf '%s\n' "$out"
if [ "$(printf '%s\n' "$out" | grep -c '^MISMATCH ')" = 3 ]; then
  echo "ok: after a direct deflateResetKeep, three streams decode to data different from the input"
else
  echo "MISSING: no mismatch found"; exit 1
fi
