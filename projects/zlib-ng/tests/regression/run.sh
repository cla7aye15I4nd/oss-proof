#!/usr/bin/env bash
# Usage: ZLIB_NG_SRC=<zlib-ng checkout> bash tests/regression/run.sh [case...]
# The patch reproductions. For each case below, builds the pinned zlib-ng in the verified configuration
# under AddressSanitizer (with pointer-pair checks) and UndefinedBehaviorSanitizer twice: once with every
# patch but the case's own ("unpatched" below), once with every patch (the verified source). The unpatched
# build must show the defect (a sanitizer report, or no return within the timeout); the patched build must
# exit 0 without a report and print the expected result. A case that stops reproducing, or whose patched
# build still fails, fails the run. Exit status: 0 all cases behave, 1 a case does not, 2 a setup error.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tests=$(cd "$here/.." && pwd)
src=${ZLIB_NG_SRC:-${UPSTREAM_DIR:-$tests/../zlib-ng}}
[ -f "$src/zlib.h.in" ] || { echo "regression: set ZLIB_NG_SRC to the pinned zlib-ng checkout" >&2; exit 2; }
work=${WORK:-$tests/build/regression}
# -O0: at higher levels the compiler adds pointer comparisons of its own (loop overlap checks) that the
# pointer-pair check reports although the source has none.
san="-fsanitize=address,pointer-compare,pointer-subtract,undefined -fno-sanitize-recover=undefined -g -O0"
export ASAN_OPTIONS="detect_invalid_pointer_pairs=2:detect_leaks=0:abort_on_error=0"
export UBSAN_OPTIONS="print_stacktrace=1"
timeout_s=${TIMEOUT:-10}
mkdir -p "$work"

# case | patch prefix | arguments (comma-separated runs) | unpatched defect: "timeout", or an extended
# regular expression that the sanitizer report must match | patched output line (one per run, ';')
cases=(
  "gzbuffer-aligned-alloc-overflow|0001||runtime error: signed integer overflow|gzbuffer -1"
  "crc32-combine-negative-len-hang|0002|g,o,c|timeout|gen 0;op 0;comb 0"
  "inflate-copy-pointer-equality|0003||invalid-pointer-pair|inflateCopy 0"
  "gzseek-offset-overflow|0004||runtime error: signed integer overflow|seek2 -1"
  "adler32-null-len-1|0007|1|runtime error: load of null pointer|adler 1"
)

build() { # build <dir> [exclude-prefix]
  local dir=$1 ex=${2:-}
  if CFLAGS="$san" EXCLUDE="$ex" bash "$tests/zlib-ng-build-current.sh" "$dir"; then return 0; fi
  CFLAGS="$san" EXCLUDE="$ex" bash "$tests/build-zlib-ng.sh" "$src" "$dir" >/dev/null || exit 2
}

build "$work/patched"
fail=0
for entry in "${cases[@]}"; do
  IFS='|' read -r name patch args defect want <<<"$entry"
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  build "$work/without-$patch" "$patch"
  for b in "without-$patch" patched; do
    cc $san -I"$work/$b" "$here/$name/repro.c" "$work/$b/libz.a" -o "$work/$name-$b" || exit 2
  done
  IFS=',' read -r -a runs <<<"${args:-}"
  [ ${#runs[@]} -gt 0 ] || runs=("")
  IFS=';' read -r -a wants <<<"$want"
  i=0
  for arg in "${runs[@]}"; do
    echo "== $name ${arg:+($arg)}"
    # unpatched: every patch but $patch
    out=$(cd "$work" && timeout "$timeout_s" "$work/$name-without-$patch" $arg 2>&1); rc=$?
    if [ "$defect" = timeout ]; then
      if [ $rc -eq 124 ]; then echo "ok: without $patch: no return within ${timeout_s}s"
      else echo "MISSING: without $patch the call returned (status $rc): $out"; fail=1; fi
    else
      if printf '%s\n' "$out" | grep -qE "$defect"; then
        echo "ok: without $patch: $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g")"
        printf '%s\n' "$out" | grep -m1 -E "^ +#[0-9]+ .* in [a-zA-Z_]" | sed "s#$work/##g; s#$src/##g; s#^ *#   at: #" || true
      else echo "MISSING: without $patch no report matching '$defect' (status $rc): $out"; fail=1; fi
    fi
    # patched: every patch
    out=$(cd "$work" && timeout "$timeout_s" "$work/$name-patched" $arg 2>&1); rc=$?
    w=${wants[$i]}
    if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|AddressSanitizer"; then
      echo "UNEXPECTED: with every patch: status $rc: $out"; fail=1
    elif printf '%s\n' "$out" | grep -qx "$w"; then
      echo "ok: with every patch: $w, no report"
    else
      echo "UNEXPECTED: with every patch, no line '$w' in: $out"; fail=1
    fi
    i=$((i + 1))
  done
done
if [ $fail -eq 0 ]; then
  echo "PASS: every patch reproduction shows its defect without its patch and none with all of them"
fi
exit $fail
