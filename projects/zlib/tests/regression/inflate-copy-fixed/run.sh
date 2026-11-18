#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/inflate-copy-fixed/run.sh
# Builds the pinned zlib twice with the pointer-pair check of AddressSanitizer: with patches/*.patch
# except 0001 (the source before the fix), and with all of patches/*.patch. Runs repro.c on each:
# inflateCopy of a stream that has decoded a fixed block. Without 0001 AddressSanitizer must report
# an invalid pointer pair in inflateCopy (a pointer into the static table lenfix compared with a
# pointer into the heap state); with 0001 nothing may be reported, and inflateCopy returns Z_OK.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/inflate-copy-fixed}
san="-O1 -g -fsanitize=address,pointer-compare,pointer-subtract -fno-omit-frame-pointer"
rm -rf "$work/without"
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0001-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
CFLAGS="$san" bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  ${CC:-cc} $san -I"$work/$b" "$here/repro.c" "$work/$b/libz.a" -o "$work/repro-$b" || exit 2
  echo "== $b"
  out=$(cd "$work" && ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0 "./repro-$b" 2>&1); rc=$?
  printf '%s\n' "$out" | sed "s#$work/##g; s#$here/#tests/regression/inflate-copy-fixed/#g"
  if [ $b = before ]; then
    if [ $rc -ne 0 ] && printf '%s\n' "$out" | grep -q "invalid-pointer-pair" &&
       printf '%s\n' "$out" | grep -q "inflateCopy"; then
      echo "ok: before the fix: inflateCopy compares pointers into different objects"
    else
      echo "MISSING: no invalid pointer pair in inflateCopy"; fail=1
    fi
  else
    if [ $rc -eq 0 ] && printf '%s\n' "$out" | grep -qx "inflateCopy=0" &&
       ! printf '%s\n' "$out" | grep -q "ERROR: AddressSanitizer"; then
      echo "ok: with the fix: inflateCopy returns Z_OK, no report"
    else
      echo "UNEXPECTED: result with the fix"; fail=1
    fi
  fi
done
exit $fail
