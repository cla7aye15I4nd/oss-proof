#!/usr/bin/env bash
# Usage: ZLIB_NG_SRC=<zlib-ng checkout> bash tests/regression/run.sh [case...]
# The patch reproductions and plain regression tests. For each patch case below, builds the pinned zlib-ng in the verified configuration
# under AddressSanitizer (with pointer-pair checks) and UndefinedBehaviorSanitizer twice: once with every
# patch but the case's own ("unpatched" below), once with every patch (the verified source). The unpatched
# build must show the defect (a sanitizer report, or no return within the timeout); the patched build must
# exit 0 without a report and print the expected result. A case that stops reproducing, or whose patched
# build still fails, fails the run. Exit status: 0 all cases behave, 1 a case does not, 2 a setup error.
# A report is a UBSan "runtime error" or an "ERROR: AddressSanitizer"; ASan's warning that it could not allocate a
# block (the case makes malloc fail) is not one.
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

# case | patch prefix | arguments (comma-separated runs) | unpatched defect: "timeout", "none" (the defect
# is not observable on a run: no sanitizer reports it; the unpatched build must then behave like the patched
# one), or an extended regular expression that the output (sanitizer report or program output) must match |
# patched output line (one per run, ';') | optional timeout in seconds for this case (default $TIMEOUT or 10). In the defect field, " OR " separates alternatives (the field separator
# is '|'): memcpy from NULL with length 0 is reported by UBSan only where the C library declares it nonnull; GCC's
# UBSan does not report NULL plus an offset (gzbuffer-alloc-null-offset), so there the case accepts the unpatched run
# printing the patched result (clang reports it).
cases=(
  "inflate-copy-pointer-equality|0003||invalid-pointer-pair|inflateCopy 0"
  "gzseek-offset-overflow|0004||runtime error: signed integer overflow|seek2 -1"
  "deflatebound-gzip-extra-length|0006||bound-ok 0|bound-ok 1"
  "inflate-window-copy|0007|300,1|invalid-pointer-pair|inflate 1 1;inflate 1 1"
  "infback-window-overlap|0007|8 100 200 150,8 100 250 100,8 100 256 100,8 100 256 200,8 200 220 100,15 1000 32700 200,15 1000 32768 258,9 10 400 258,8 3 255 10|none|back 1 546 1;back 1 496 1;back 1 496 1;back 1 596 1;back 1 596 1;back 1 34008 1;back 1 34066 1;back 1 820 1;back 1 309 1"
  "inflatesync-null-next-in|0008||none|sync -3 1"
  "inflatesetdictionary-null|0009||setdict 0 OR null pointer passed as argument|setdict -2"
  "inflate-fast-primed-bits|0010||inflate 1 34 4294967294|inflate 1 32 0"
  "inflate-shared-header-extra|0011|copy,two,late|heap-buffer-overflow|inflate 0;inflate 0;inflate 0"
  "longest-match-offset-base|0012|f,x|none|deflate 1 31733 9f6d82f0;deflate 1 34825 6a1f0340"
  "deflate-medium-insert-count|0013||runtime error: division by zero|deflate 1 28"
  "gzwrite-clearerr-stale-input|0014||invalid-pointer-pair OR heap-buffer-overflow|gzwrite 0 -1 1"
  "gzclose-after-failed-write|0014||heap-use-after-free|gzclose 0 0"
  "gzbuffer-alloc-null-offset|0015||runtime error: .*null pointer OR runtime error: pointer overflow OR runtime error: pointer index expression OR ^gzwrite 0 0 -4 -4$|gzwrite 0 0 -4 -4"
  "gzread-position-overflow|0016||runtime error: signed integer overflow|gzread 0 9223372036854775807 0"
  "fixed-block-start-overflow|0018|f|runtime error: signed integer overflow|deflate 1 2151677952|180"
)

# Plain regression tests: defects of an earlier upstream release that upstream has since fixed, so no patch
# remains. Each must run on the verified source without a sanitizer report and print the expected lines.
# case | arguments (comma-separated runs) | expected output line (one per run, ';')
plain=(
  "adler32-null-len-1|1,0,7|adler_z 1;adler_z 1;adler_z 1"
  "crc32-combine-negative-len-hang|g,c|gen 0;comb 0"
  "gzbuffer-aligned-alloc-overflow||gzwrite 1"
)

# Open defects: undefined behaviour of the verified source with no patch yet. Each must still show its
# report on the verified source; a case that stops reproducing (upstream fixed it) fails the run.
# case | arguments | extended regular expression the report must match
open_cases=(
)

# Guards: an earlier, defective version of one of our patches, kept in the case's directory. The source built
# with that version in place of the current patch must show the defect on the case's reproduction, so that the
# case would catch the defect if it came back.
# case | patch prefix | earlier version (file in the case's directory) | arguments (comma-separated runs) |
# extended regular expression every run's report must match
guards=(
  "infback-window-overlap|0007|first-0007.patch|8 100 200 150,8 100 250 100,15 1000 32700 200,9 10 400 258,8 3 255 10|memcpy-param-overlap"
)

build() { # build <dir> [exclude-prefix]
  local dir=$1 ex=${2:-}
  if CFLAGS="$san" EXCLUDE="$ex" bash "$tests/zlib-ng-build-current.sh" "$dir"; then return 0; fi
  CFLAGS="$san" EXCLUDE="$ex" bash "$tests/build-zlib-ng.sh" "$src" "$dir" >/dev/null || exit 2
}

build "$work/patched"
fail=0
for entry in "${cases[@]}"; do
  IFS='|' read -r name patch args defect want tmo <<<"$entry"
  t_s=${tmo:-$timeout_s}
  defect=${defect// OR /|}
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
    out=$(cd "$work" && timeout "$t_s" "$work/$name-without-$patch" $arg 2>&1); rc=$?
    if [ "$defect" = none ]; then
      w=${wants[$i]}
      if [ $rc -eq 0 ] && printf '%s\n' "$out" | grep -qx "$w"; then echo "ok: without $patch: $w (defect not observable on a run)"
      else echo "UNEXPECTED: without $patch: status $rc: $out"; fail=1; fi
    elif [ "$defect" = timeout ]; then
      if [ $rc -eq 124 ]; then echo "ok: without $patch: no return within ${t_s}s"
      else echo "MISSING: without $patch the call returned (status $rc): $out"; fail=1; fi
    else
      if printf '%s\n' "$out" | grep -qE "$defect"; then
        echo "ok: without $patch: $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g")"
        printf '%s\n' "$out" | grep -m1 -E "^ +#[0-9]+ .* in [a-zA-Z_]" | sed "s#$work/##g; s#$src/##g; s#^ *#   at: #" || true
      else echo "MISSING: without $patch no report matching '$defect' (status $rc): $out"; fail=1; fi
    fi
    # patched: every patch
    out=$(cd "$work" && timeout "$t_s" "$work/$name-patched" $arg 2>&1); rc=$?
    w=${wants[$i]}
    if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
      echo "UNEXPECTED: with every patch: status $rc: $out"; fail=1
    elif printf '%s\n' "$out" | grep -qx "$w"; then
      echo "ok: with every patch: $w, no report"
    else
      echo "UNEXPECTED: with every patch, no line '$w' in: $out"; fail=1
    fi
    i=$((i + 1))
  done
done
for entry in "${plain[@]}"; do
  IFS='|' read -r name args want <<<"$entry"
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  cc $san -I"$work/patched" "$here/$name/repro.c" "$work/patched/libz.a" -o "$work/$name-patched" || exit 2
  IFS=',' read -r -a runs <<<"${args:-}"
  [ ${#runs[@]} -gt 0 ] || runs=("")
  IFS=';' read -r -a wants <<<"$want"
  i=0
  for arg in "${runs[@]}"; do
    echo "== $name ${arg:+($arg)} (fixed upstream)"
    out=$(cd "$work" && timeout "$timeout_s" "$work/$name-patched" $arg 2>&1); rc=$?
    w=${wants[$i]}
    if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
      echo "UNEXPECTED: status $rc: $out"; fail=1
    elif printf '%s\n' "$out" | grep -qx "$w"; then
      echo "ok: $w, no report"
    else
      echo "UNEXPECTED: no line '$w' in: $out"; fail=1
    fi
    i=$((i + 1))
  done
done
for entry in ${open_cases[@]+"${open_cases[@]}"}; do
  IFS='|' read -r name args defect <<<"$entry"
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  cc $san -I"$work/patched" "$here/$name/repro.c" "$work/patched/libz.a" -o "$work/$name-patched" || exit 2
  echo "== $name ${args:+($args)} (open, no patch)"
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-patched" $args 2>&1); rc=$?
  if printf '%s\n' "$out" | grep -qE "$defect"; then
    echo "ok: verified source: $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g")"
    printf '%s\n' "$out" | grep -m1 -E "^ +#[0-9]+ .* in [a-zA-Z_]" | sed "s#$work/##g; s#$src/##g; s#^ *#   at: #" || true
  else
    echo "FIXED?: no report matching '$defect' on the verified source (status $rc): $out"; fail=1
  fi
done
for entry in "${guards[@]}"; do
  IFS='|' read -r name patch earlier args defect <<<"$entry"
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  dir="$work/earlier-${earlier%.patch}"
  export REPLACE="$patch=$here/$name/$earlier"
  build "$dir"
  unset REPLACE
  cc $san -I"$dir" "$here/$name/repro.c" "$dir/libz.a" -o "$work/$name-earlier" || exit 2
  IFS=',' read -r -a runs <<<"$args"
  for arg in "${runs[@]}"; do
    echo "== $name ($arg) (guard: $earlier in place of $patch)"
    out=$(cd "$work" && timeout "$timeout_s" "$work/$name-earlier" $arg 2>&1); rc=$?
    if printf '%s\n' "$out" | grep -qE "$defect"; then
      echo "ok: with $earlier: $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g; s#0x[0-9a-f]*#0x...#g")"
    else
      echo "MISSING: with $earlier no report matching '$defect' (status $rc): $out"; fail=1
    fi
  done
done
if [ $fail -eq 0 ]; then
  echo "PASS: every patch reproduction shows its defect without its patch and none with all of them; every plain regression test passes; every open defect still reproduces; every guard shows the earlier defect"
fi
exit $fail
