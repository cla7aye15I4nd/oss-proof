#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/deflatebound-gzip-extra-length/run.sh
# Builds the pinned zlib twice: with patches/*.patch except 0007 (the source before the fix), and
# with all of patches/*.patch. Runs repro.c on each: a gzip stream whose header has an extra field
# with extra_len 2^32 - 2 and 2^32 - 1, compressed in one deflate(Z_FINISH) call with exactly
# deflateBound bytes of room. zlib.h promises Z_STREAM_END. Without 0007 both calls must return
# Z_OK (repro.c exits 1); with 0007 both must end.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/deflatebound-gzip-extra-length}
rm -rf "$work/without"
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0007-*) ;; *) cp "$p" "$work/without/patches/";; esac
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
    if [ $rc -eq 1 ] && [ "$(printf '%s\n' "$out" | grep -c "that room Z_OK")" -eq 2 ]; then
      echo "ok: before the fix: deflate(Z_FINISH) with deflateBound bytes of room does not end"
    else
      echo "MISSING: a call ended within the bound"; fail=1
    fi
  else
    if [ $rc -eq 0 ] && [ "$(printf '%s\n' "$out" | grep -c "that room Z_STREAM_END")" -eq 2 ]; then
      echo "ok: with the fix: both calls end within deflateBound"
    else
      echo "UNEXPECTED: a call does not end with the fix"; fail=1
    fi
  fi
done
exit $fail
