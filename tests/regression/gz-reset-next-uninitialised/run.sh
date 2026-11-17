#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gz-reset-next-uninitialised/run.sh
# Builds the verified source (the pinned zlib with patches/*.patch) under ASan and UBSan, with the
# "x.next += n" statements of gzlib.c and gzread.c routed through the probe of probe.h (the value
# is unchanged), and runs unset.c. The probe must see x.next evaluated with n == 0 on the
# never-written field (gzseek in gzlib.c, gz_skip_have in gzread.c), and no sanitizer may report:
# no sanitizer detects this, which is why the probe is used. C17 leaves this arithmetic undefined;
# the model accepts adding zero to any pointer (see README.md).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$here/../../..
src=${ZLIB_SRC:?set ZLIB_SRC to the pinned zlib checkout}
work=${WORK:-$root/tests/build/gz-reset-next-uninitialised}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -O1"
prog=${PROG:-unset}
progdir=${PROGDIR:-$here}
rm -rf "$work/verified"
CFLAGS="$san" bash "$root/tests/build-zlib.sh" "$src" "$work/verified" >/dev/null || exit 2
fail=0
d=$work/verified
sed -i.orig 's/state->x\.next += n;/state->x.next += ZPROBE_NEXT(state->x.next, n);/' "$d/gzlib.c" "$d/gzread.c"
[ "$(grep -c ZPROBE_NEXT "$d/gzlib.c" "$d/gzread.c" | awk -F: '{s += $2} END {print s}')" -ge 2 ] ||
  { echo "probe not inserted"; exit 2; }
(cd "$d" && make -B libz.a CFLAGS="$san -include $here/probe.h" >/dev/null) || exit 2
cc $san -I"$d" "$progdir/$prog.c" "$d/libz.a" -o "$work/$prog" || exit 2
out=$(cd "$work" && "$work/$prog" 2>&1)
printf '%s\n' "$out"
if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
  echo "UNEXPECTED: a sanitizer report"; fail=1
elif printf '%s\n' "$out" | grep -q "^x.next + 0 at gzlib.c" && printf '%s\n' "$out" | grep -q "^x.next + 0 at gzread.c"; then
  echo "ok: the C evaluates x.next + 0 in gzseek64 and gz_skip_have, with no sanitizer report"
else
  echo "MISSING: no evaluation of x.next with n == 0"; fail=1
fi
exit $fail
