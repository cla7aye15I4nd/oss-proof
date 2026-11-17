#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/deflate-bound/run.sh [COUNT] [SEED]
# Statement test of the deflate completion goals (DeflateCompletes, the deflateBound promise of
# zlib.h, the compressBound promise of compress and compress2) on the patched real C: random
# parameter grids, an exhaustive length sweep, compress at every level, the far-match search and the
# gzip extra-length cases. Once plainly, once under ASan and UBSan. Exit 0: no failure except the two expected
# extra-length cases (a finding, docs/en/findings.md), which `extra` must still report.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
n=${1:-4}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-deflate-bound}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
CFLAGS="-fsanitize=address,undefined -fno-sanitize-recover=all -g -O1" \
  bash "$here/../../build-zlib.sh" "$src" "$work/zs" >/dev/null
cc -O2 -Wall -Wextra -I"$work/z" "$here/bound.c" "$work/z/libz.a" -o "$work/bound"
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -I"$work/zs" "$here/bound.c" \
  "$work/zs/libz.a" -o "$work/bound-san"
"$work/bound" grid "$seed" "$n" | grep -v '^MIN\|^INFO'
for slice in $(seq 0 23); do "$work/bound" sweep "$slice" 300 | grep '^FAIL \|^FAILURES [1-9]' && exit 1; done
"$work/bound" compress "$seed" $((n * 500)) | grep -v '^MIN\|^INFO'
# The far-match search (the `Z_FIXED` finding of docs/en/findings.md): no failure with patch 0006.
for wb in 9 10 11 12 13 14 15; do "$work/bound" far "$wb" 120000 | grep '^FAIL \|^FAILURES [1-9]' && exit 1; done
"$work/bound-san" far 15 120000 | grep '^FAIL \|^FAILURES [1-9]' && exit 1
"$work/bound-san" grid "$((seed + 1))" 1 | grep -v '^MIN\|^INFO'
"$work/bound-san" compress "$((seed + 2))" $((n * 100)) | grep -v '^MIN\|^INFO'
# The extra-length finding: exactly the two lengths 2^32-1 and 2^32-2 must fail.
out=$("$work/bound-san" extra "$seed" 1 || true)
echo "$out"
[ "$(echo "$out" | grep -c '^FAIL ')" = 2 ] || { echo "extra: expected exactly two failures"; exit 1; }
