#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/c-check.sh <case directory>
# The C side of one case, called by the case's run.sh. It builds the pinned zlib twice under ASan and
# UBSan: the verified source (patches/*.patch applied in name order) and the same source with the
# case's revert.patch applied on top. It compiles the case's trigger.c against each and runs it in an
# empty directory. With the revert the output must contain the sanitizer finding of the case's row in
# cases.tsv (TIMEOUT for a hang: the run is stopped after 10 seconds); without it there must be no
# sanitizer report, and trigger.c must exit 0 within that time. The standard
# output of each run is kept in $WORK/<case>/run-{reverted,fixed}/stdout.
# The case's run.sh may set SAN_EXTRA (more compiler flags, for example -fsanitize=pointer-compare),
# ASAN_OPTIONS, UBSAN_OPTIONS and LDLIBS. CC is the compiler (default cc). WORK is the build directory
# (default tests/build/patch-reverts).
# Exit status: 0 the case is confirmed, 1 it is not, 2 a setup error.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
case=$(cd "${1:?usage: c-check.sh <case directory>}" && pwd)
id=$(basename "$case")
src=${ZLIB_SRC:-$root/zlib}
[ -f "$src/zlib.h" ] || { echo "c-check: $src is not a zlib checkout (set ZLIB_SRC)" >&2; exit 2; }
work=${WORK:-$root/tests/build/patch-reverts}
mkdir -p "$work"
work=$(cd "$work" && pwd)
expect=$(awk -F'\t' -v id="$id" '$1 == id { print $6 }' "$here/cases.tsv")
[ -n "$expect" ] || { echo "c-check: no row for $id in cases.tsv" >&2; exit 2; }
cc=${CC:-cc}
san="-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer -g -O1 ${SAN_EXTRA:-}"
export ASAN_OPTIONS=${ASAN_OPTIONS:-detect_leaks=0}
export UBSAN_OPTIONS=${UBSAN_OPTIONS:-print_stacktrace=1}

# contains <text> <expectation>: every part of the expectation (parts are joined by " && ") occurs.
contains() {
  local rest=$2 part
  while :; do
    part=${rest%% && *}
    printf '%s\n' "$1" | grep -qF -- "$part" || return 1
    [ "$part" = "$rest" ] && return 0
    rest=${rest#* && }
  done
}

# limit <seconds> <command...>: run the command, kill it after that many seconds and exit 142.
limit() {
  perl -e '$t = shift @ARGV; $p = fork; if (!$p) { exec @ARGV or exit 127 }
    $SIG{ALRM} = sub { kill "KILL", $p; waitpid($p, 0); exit 142 }; alarm $t; waitpid($p, 0);
    exit($? & 127 ? 128 + ($? & 127) : $? >> 8)' "$@"
}

# build <dir> <revert patch or empty>: the pinned source, the patches, the revert; libz.a under $san.
build() {
  local dir=$1 revert=$2 p
  rm -rf "$dir"; mkdir -p "$dir"
  (cd "$src" && tar --exclude=.git -cf - .) | tar -C "$dir" -xf -
  for p in $(ls "$root"/patches/*.patch | LC_ALL=C sort); do
    (cd "$dir" && patch -p1 --batch --forward --quiet < "$p") || { echo "c-check: $(basename "$p") does not apply" >&2; return 2; }
  done
  if [ -n "$revert" ]; then
    (cd "$dir" && patch -p1 --batch --forward < "$revert") || { echo "c-check: revert.patch does not apply" >&2; return 2; }
  fi
  (cd "$dir" && CC="$cc" CFLAGS="$san" ./configure --static >configure.log 2>&1 && make libz.a >make.log 2>&1) ||
    { cat "$dir/configure.log" "$dir/make.log" 2>/dev/null | tail -20; return 2; }
}

key=$(printf '%s' "$cc $san" | cksum | cut -d' ' -f1)
fixed="$work/fixed-$key"
if [ ! -f "$fixed/libz.a" ]; then build "$fixed" "" || exit 2; fi
reverted="$work/$id/reverted"
build "$reverted" "$case/revert.patch" || exit 2

fail=0
for b in reverted fixed; do
  lib=$reverted; [ $b = fixed ] && lib=$fixed
  bin="$work/$id/trigger-$b"
  $cc $san -I"$lib" "$case/trigger.c" "$lib/libz.a" ${LDLIBS:-} -o "$bin" || exit 2
  run="$work/$id/run-$b"; rm -rf "$run"; mkdir -p "$run"
  echo "== $b"
  # A case whose defect is a hang expects TIMEOUT: the run is stopped after 10 seconds.
  (cd "$run" && limit 10 "$bin" >stdout 2>stderr); status=$?
  [ $status -eq 142 ] && echo "TIMEOUT: no return within 10 seconds" >>"$run/stderr"
  out=$(cat "$run/stdout" "$run/stderr")
  printf '%s\n' "$out" | sed "s#$work/##g; s#$root/##g"
  echo "exit status $status"
  if [ $b = reverted ]; then
    if contains "$out" "$expect"; then
      echo "ok: with the revert: $expect"
    else
      echo "MISSING with the revert: $expect"; fail=1
    fi
  else
    if printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer\|ERROR: LeakSanitizer"; then
      echo "UNEXPECTED: a sanitizer report on the verified source"; fail=1
    elif [ $status -ne 0 ]; then
      echo "UNEXPECTED: trigger.c failed on the verified source"; fail=1
    else
      echo "ok: verified source: no report"
    fi
  fi
done
exit $fail
