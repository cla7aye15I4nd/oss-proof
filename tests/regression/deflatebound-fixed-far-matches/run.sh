#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflatebound-fixed-far-matches/run.sh
# Builds the pinned zlib twice: with patches/*.patch except 0006 (the source before the fix), and
# with all of patches/*.patch. Runs repro.c on each: 1,000,000 bytes that deflate_fast codes as far
# 3-byte matches, compressed with windowBits 15, memLevel 8 and Z_FIXED at levels 1 to 9, in one
# deflate(Z_FINISH) call with exactly deflateBound bytes of room. zlib.h promises Z_STREAM_END.
# Without 0006 some level must return Z_OK (repro.c exits 1); with 0006 every level must end.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflatebound-fixed-far-matches}
rm -rf "$work/without"
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0006-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
bash "$here/../../build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  ${CC:-cc} -O2 -I"$work/$b" "$here/repro.c" "$work/$b/libz.a" -o "$work/repro-$b" || exit 2
  echo "== $b"
  out=$("$work/repro-$b" 2>&1); rc=$?
  printf '%s\n' "$out"
  if [ $b = before ]; then
    if [ $rc -eq 1 ] && printf '%s\n' "$out" | grep -q "(not Z_STREAM_END)"; then
      echo "ok: before the fix: deflate(Z_FINISH) with deflateBound bytes of room does not end"
    else
      echo "MISSING: every level ended within the bound"; fail=1
    fi
  else
    if [ $rc -eq 0 ] && ! printf '%s\n' "$out" | grep -q "(not Z_STREAM_END)"; then
      echo "ok: with the fix: every level ends within deflateBound"
    else
      echo "UNEXPECTED: some level does not end with the fix"; fail=1
    fi
  fi
done
exit $fail
