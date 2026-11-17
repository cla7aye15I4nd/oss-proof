#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/goals/roundtrip-default/run.sh [COUNT] [SEED]
# Statement test of the default-stream completion and round-trip goals (ZlibF/Spec/Functional/RoundTrip.lean)
# on the patched real C: one call with deflateBound room, a Z_FINISH call with the remaining bound after a
# random clean history, repeated small Z_FINISH calls, inflate of the stream with the remaining room, and
# compress/uncompress. Once plainly with four seeds, once under ASan and UBSan. Exit 0: no failure.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
n=${1:-300}
seed=${2:-1}
work=${WORK:-$here/../../build/goals-roundtrip-default}
mkdir -p "$work"
bash "$here/../../build-zlib.sh" "$src" "$work/z" >/dev/null
CFLAGS="-fsanitize=address,undefined -fno-sanitize-recover=all -g -O1" \
  bash "$here/../../build-zlib.sh" "$src" "$work/zs" >/dev/null
cc -O2 -Wall -Wextra -I"$work/z" "$here/rt.c" "$work/z/libz.a" -o "$work/rt"
cc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -I"$work/zs" "$here/rt.c" \
  "$work/zs/libz.a" -o "$work/rt-san"
for s in $seed $((seed + 1)) $((seed + 2)) $((seed + 3)); do "$work/rt" "$s" "$n" | grep '^FAIL \|^CHECKED\|^FAILURES'; done
"$work/rt-san" "$((seed + 4))" "$((n / 10))" | grep '^FAIL \|^CHECKED\|^FAILURES'
cc -O2 -Wall -Wextra -I"$work/z" "$here/fdict.c" "$work/z/libz.a" -o "$work/fdict"
"$work/fdict"
