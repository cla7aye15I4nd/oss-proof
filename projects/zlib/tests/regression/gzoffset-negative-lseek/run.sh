#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gzoffset-negative-lseek/run.sh
# Linux only: it needs /proc/self/mem, whose lseek accepts and returns any 64-bit offset. Builds the
# pinned zlib twice under ASan and UBSan: with patches/*.patch except 0005 (the source before the
# fix), and with all of patches/*.patch. Runs negative.c on each: a gzip stream read through
# /proc/self/mem with gzdopen and gzread, then the caller moves the descriptor to INT64_MIN + 1 and
# calls gzoffset64. Without 0005 the run must show lseek returning INT64_MIN + 1 and UBSan reporting
# a signed overflow in gzoffset64; with 0005 nothing may be reported, and gzoffset64 returns -1.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$here/../../build/gzoffset-negative-lseek}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1"
[ "$(uname -s)" = Linux ] || { echo "skip: needs Linux (/proc/self/mem)"; exit 0; }
rm -rf "$work/without"
mkdir -p "$work/without/tests" "$work/without/patches"
cp "$here/../../build-zlib.sh" "$work/without/tests/"
for p in "$here"/../../../patches/*.patch; do
  case "$(basename "$p")" in 0005-*) ;; *) cp "$p" "$work/without/patches/";; esac
done
CFLAGS="$san" bash "$work/without/tests/build-zlib.sh" "$src" "$work/before" >/dev/null || exit 2
CFLAGS="$san" bash "$here/../../build-zlib.sh" "$src" "$work/after" >/dev/null || exit 2
fail=0
for b in before after; do
  ${CC:-cc} $san -I"$work/$b" "$here/negative.c" "$work/$b/libz.a" -o "$work/negative-$b" || exit 2
  echo "== $b"
  out=$(cd "$work" && UBSAN_OPTIONS=print_stacktrace=1 "./negative-$b" 2>&1)
  printf '%s\n' "$out" | sed "s#$work/##g; s#$here/#tests/regression/gzoffset-negative-lseek/#g"
  if ! printf '%s\n' "$out" | grep -q "lseek(fd, INT64_MIN + 1, SEEK_SET) = -9223372036854775807"; then
    echo "MISSING: lseek did not return INT64_MIN + 1"; fail=1
  elif [ $b = before ]; then
    if printf '%s\n' "$out" | grep -q "runtime error: signed integer overflow" &&
       printf '%s\n' "$out" | grep -q "in gzoffset64"; then
      echo "ok: before the fix: gzoffset64 overflows subtracting the buffered input"
    else
      echo "MISSING: no signed overflow in gzoffset64"; fail=1
    fi
  else
    if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
      echo "UNEXPECTED: a sanitizer report with the fix"; fail=1
    elif printf '%s\n' "$out" | grep -qx "gzoffset64 = -1"; then
      echo "ok: with the fix: gzoffset64 returns -1, no report"
    else
      echo "UNEXPECTED: result with the fix"; fail=1
    fi
  fi
done
exit $fail
