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
# is '|'): memcpy from NULL with length 0 is reported by UBSan only where the C library declares it nonnull.
cases=(
  "inflate-copy-pointer-equality|0001||invalid-pointer-pair|inflateCopy 0"
  "gzseek-offset-overflow|0002|cur,set,pos|runtime error: signed integer overflow|seek2 -1;set unget 120 seek -1 tell -1 getc 120;pos getc 0 seek 9223372036854775806 seek -1 tell 9223372036854775806"
  "gzseek-refusal-state|0002|read,write,unget,raw|^read seek 100 -1 tell 0 getc 97$ OR ^write seek 10 -1 tell 0 putc 122 close 0 length 1$ OR ^unget unget 120 121 tell -2 seek -1 tell -1 getc 120 97$ OR ^raw unget 120 121 tell -2 seek -1 tell -1 getc 120 97$|read seek 100 -1 tell 100 getc 119;write seek 10 -1 tell 10 putc 122 close 0 length 11;unget unget 120 121 tell -2 seek -1 tell -2 getc 121 120;raw unget 120 121 tell -2 seek -1 tell -2 getc 121 120"
  "deflatebound-gzip-extra-length|0003||bound-ok 0|bound-ok 1"
  "inflate-window-copy|0004|300,1|invalid-pointer-pair|inflate 1 1;inflate 1 1"
  "infback-window-overlap|0004|8 100 200 150,8 100 250 100,8 100 256 100,8 100 256 200,8 200 220 100,15 1000 32700 200,15 1000 32768 258,9 10 400 258,8 3 255 10|none|back 1 546 1;back 1 496 1;back 1 496 1;back 1 596 1;back 1 596 1;back 1 34008 1;back 1 34066 1;back 1 820 1;back 1 309 1"
  "inflatesync-null-next-in|0005||none|sync -3 1"
  "inflatesetdictionary-null|0006||setdict 0 OR null pointer passed as argument|setdict -2"
  "inflate-fast-primed-bits|0007||inflate 1 34 4294967294|inflate 1 32 0"
  "inflate-shared-header-extra|0008|copy,two,late|heap-buffer-overflow|inflate 0;inflate 0;inflate 0"
  "longest-match-offset-base|0009|f,x|none|deflate 1 31733 9f6d82f0;deflate 1 34825 6a1f0340"
  "deflate-medium-insert-count|0010||runtime error: division by zero|deflate 1 28"
  "gzwrite-clearerr-stale-input|0011||invalid-pointer-pair OR heap-buffer-overflow|gzwrite 0 -1 1"
  "gzclose-after-failed-write|0011||heap-use-after-free|gzclose 0 0"
  "gzread-position-overflow|0013||runtime error: signed integer overflow|gzread 0 9223372036854775807 -1"
  "gzgetc-macro-position|0013|max,near|runtime error: signed integer overflow|max read 2 macro 0 last -1 pos 9223372036854775807 err -3;near read 1 macro 11 last -1 pos 9223372036854775807 err -3"
  "fixed-block-start-overflow|0015|f|runtime error: signed integer overflow|deflate 1 2151677952|180"
  "deflate-slow-match-start|0016|362,303|ERROR: AddressSanitizer OR runtime error OR round-trip MISMATCH|inflate 1 out 80393 of 80393 round-trip ok;inflate 1 out 86208 of 86208 round-trip ok"
  "gzdirect-pending-skip|0017||runtime error: signed integer overflow|seek 9223372036854775807 direct 1 getc -1 tell 13"
  "gzgets-pending-skip|0018||runtime error: signed integer overflow|seek 9223372036854775807 direct 1 gets null tell 3"
  "gzwrite-zero-retry|0019|max,retry|runtime error: signed integer overflow OR ^retry seek 10000 write 0 tell 14096 write 3 tell 14099 close 0 bytes 14099 bad$|max seek 9223372036854775807 write 0 tell 9223372036854775807;retry seek 10000 write 0 tell 10000 write 3 tell 10003 close 0 bytes 10003 ok"
  "gzprintf-failed-write-drift|0021|oob,corrupt|ERROR: AddressSanitizer: heap-buffer-overflow OR ERROR: AddressSanitizer: SEGV OR ERROR: AddressSanitizer: BUS OR ERROR: AddressSanitizer: unknown-crash OR ^corrupt close 0 inflate 0 bytes [0-9]+ bad$|oob close 0 inflate 1 bytes 786389 ok;corrupt close 0 inflate 1 bytes 733299 ok"
)

# Clang cases: patch reproductions whose defect only clang's UBSan reports (GCC's does not report NULL plus an
# offset). Each runs like a case above on the default compiler's builds, except that there the unpatched build may
# instead print the patched result with no report: that shows nothing, and the run says so with a NOT SHOWN line
# (it does not count as a pass of the defect). Then, unless the default compiler is clang, both builds are made again
# with clang, where the unpatched build must show the report. Without clang that run is skipped with a loud SKIPPED
# line; when CI is set a missing clang fails the run.
# case | patch prefix | report the unpatched clang build must show (" OR " separates alternatives) | patched line
clang_cases=(
  "gzbuffer-alloc-null-offset|0012|runtime error: .*null pointer OR runtime error: pointer overflow OR runtime error: pointer index expression|gzwrite 0 0 -4 -4"
)

# Plain regression tests: defects of an earlier upstream release that upstream has since fixed, so no patch
# remains. Each must run on the verified source without a sanitizer report and print the expected lines.
# case | arguments (comma-separated runs) | expected output line (one per run, ';')
plain=(
  "adler32-null-len-1|1,0,7|adler_z 1;adler_z 1;adler_z 1"
  "crc32-combine-negative-len-hang|g,c|gen 0;comb 0"
  "gzbuffer-aligned-alloc-overflow||gzwrite 1"
)

# Open defects: defects of the verified source with no patch yet (undefined behaviour, or a wrong result with no
# memory error). Each must still show its report or wrong result on the verified source; a case that stops
# reproducing (upstream fixed it) fails the run.
# case | arguments | extended regular expression the report (or the program's output) must match
open_cases=(
  "deflatereset-fixed-block-open||^deflate 0 0 1 [0-9]+ inflate -3 0$"
)

# Guards: an earlier, defective version of one of our patches, kept in the case's directory. The source built
# with that version in place of the current patch must show the defect on the case's reproduction, so that the
# case would catch the defect if it came back.
# case | patch prefix | earlier version (file in the case's directory) | arguments (comma-separated runs) |
# extended regular expression every run's report must match
guards=(
  "infback-window-overlap|0004|first-0004.patch|8 100 200 150,8 100 250 100,15 1000 32700 200,9 10 400 258,8 3 255 10|memcpy-param-overlap"
  "gzgetc-macro-position|0013|first-0013.patch|max,near|runtime error: signed integer overflow"
)

# 32-bit guards: like the guards, on a build whose size_t is 32 bits and whose file offsets are 64 bits
# (-m32 -D_FILE_OFFSET_BITS=64, the usual large-file build of a 32-bit system). The verified source built so must run
# the case without a report and print the expected line; the source with the earlier version of the patch must print
# a line matching the defect. They need a compiler and C library for -m32 (on x86_64 Linux, gcc-multilib). Without
# one they are skipped with a loud message, and when CI is set (as on the CI runners) a missing -m32 toolchain fails
# the run instead.
# case | patch prefix | earlier version | expected line with every current patch | extended regular expression the
# earlier version's output must match | optional flags in place of $m32 | optional widths line in place of
# "size_t 4 off 8" (the repro prints sizeof(size_t) and sizeof(z_off_t))
wide32=(
  "gzwrite-position-32bit|0014|first-0014.patch|pos32 seek 4294967295 write 1 tell 4294967296 err 0|^pos32 seek 4294967295 write 0 tell 4294967295 err -3$"
  "gzread-position-32bit|0013|first-0013.patch|pos32 seek max-5 fread 4 tell max-0 err -3|^pos32 seek max-5 fread [0-9]+ tell max-[0-9]{6,} err 0$|-m32 -D_LARGEFILE64_SOURCE=0|size_t 4 off 4"
)
m32="-m32 -D_FILE_OFFSET_BITS=64"

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
# check_patched <label> <binary> <want>: the patched build runs without a report and prints <want>
check_patched() {
  local out rc
  out=$(cd "$work" && timeout "$timeout_s" "$2" 2>&1); rc=$?
  if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
    echo "UNEXPECTED: $1: status $rc: $out"; fail=1
  elif printf '%s\n' "$out" | grep -qx "$3"; then
    echo "ok: $1: $3, no report"
  else
    echo "UNEXPECTED: $1, no line '$3' in: $out"; fail=1
  fi
}
cc_is_clang=""
skippedclang=""
if cc --version 2>/dev/null | grep -qi clang; then cc_is_clang=1; fi
clang_ok=""
for entry in "${clang_cases[@]}"; do
  IFS='|' read -r name patch defect want <<<"$entry"
  defect=${defect// OR /|}
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  build "$work/without-$patch" "$patch"
  for b in "without-$patch" patched; do
    cc $san -I"$work/$b" "$here/$name/repro.c" "$work/$b/libz.a" -o "$work/$name-$b" || exit 2
  done
  echo "== $name (default compiler)"
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-without-$patch" 2>&1); rc=$?
  if printf '%s\n' "$out" | grep -qE "$defect"; then
    echo "ok: without $patch: $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g")"
  elif [ -z "$cc_is_clang" ] && [ $rc -eq 0 ] && printf '%s\n' "$out" | grep -qx "$want"; then
    echo "NOT SHOWN: without $patch this compiler's UBSan prints the patched result '$want' with no report (it does not report NULL plus an offset); this run shows nothing, the clang run below must show the defect"
  else
    echo "MISSING: without $patch no report matching '$defect' (status $rc): $out"; fail=1
  fi
  check_patched "with every patch" "$work/$name-patched" "$want"
  [ -z "$cc_is_clang" ] || continue
  if [ -z "$clang_ok" ]; then
    if command -v clang >/dev/null 2>&1 && printf 'int main(void) { return 0; }\n' > "$work/probeclang.c" &&
        clang $san "$work/probeclang.c" -o "$work/probeclang" >"$work/probeclang.log" 2>&1 && "$work/probeclang"; then
      clang_ok=yes
    else
      clang_ok=no
    fi
  fi
  if [ "$clang_ok" = no ]; then
    if [ -n "${CI:-}" ]; then
      echo "MISSING: $name needs clang with ASan and UBSan, required when CI is set"; fail=1
    else
      echo "SKIPPED: $name NOT RUN with clang (no working clang): the defect of $patch is NOT SHOWN by this run"
      skippedclang="$skippedclang $name"
    fi
    continue
  fi
  for b in "without-$patch" patched; do
    ex=""; [ "$b" = patched ] || ex=$patch
    if ! CC=clang CFLAGS="$san" EXCLUDE="$ex" bash "$tests/zlib-ng-build-current.sh" "$work/$b-clang"; then
      CC=clang CFLAGS="$san" EXCLUDE="$ex" bash "$tests/build-zlib-ng.sh" "$src" "$work/$b-clang" >/dev/null || exit 2
    fi
    clang $san -I"$work/$b-clang" "$here/$name/repro.c" "$work/$b-clang/libz.a" -o "$work/$name-$b-clang" || exit 2
  done
  echo "== $name (clang)"
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-without-$patch-clang" 2>&1); rc=$?
  if printf '%s\n' "$out" | grep -qE "$defect"; then
    echo "ok: without $patch (clang): $(printf '%s\n' "$out" | grep -m1 -E "$defect" | sed "s#$work/##g; s#$src/##g")"
  else
    echo "MISSING: without $patch (clang) no report matching '$defect' (status $rc): $out"; fail=1
  fi
  check_patched "with every patch (clang)" "$work/$name-patched-clang" "$want"
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
sel32=()
for entry in "${wide32[@]}"; do
  IFS='|' read -r name patch earlier want defect flags32 widths <<<"$entry"
  [ $# -eq 0 ] || [[ " $* " == *" $name "* ]] || continue
  sel32+=("$entry")
  # the same case on the verified (LP64) build: the same line, no report
  cc $san -I"$work/patched" "$here/$name/repro.c" "$work/patched/libz.a" -o "$work/$name-patched" || exit 2
  echo "== $name (LP64)"
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-patched" 2>&1); rc=$?
  if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
    echo "UNEXPECTED: status $rc: $out"; fail=1
  elif printf '%s\n' "$out" | grep -qx "$want"; then
    echo "ok: $want, no report"
  else
    echo "UNEXPECTED: no line '$want' in: $out"; fail=1
  fi
done
skipped32=""
if [ ${#sel32[@]} -gt 0 ]; then
  printf '#include <stddef.h>\n#include <sys/types.h>\nint main(void) { return !(sizeof(size_t) == 4 && sizeof(off_t) == 8); }\n' \
    > "$work/probe32.c"
  if ! { cc $san $m32 "$work/probe32.c" -o "$work/probe32" >"$work/probe32.log" 2>&1 && "$work/probe32"; }; then
    if [ -n "${CI:-}" ]; then
      echo "MISSING: no working -m32 toolchain (size_t of 32 bits, off_t of 64), required when CI is set:"; cat "$work/probe32.log"
      fail=1
    else
      skipped32="${#sel32[@]}"
      echo "SKIPPED: ${#sel32[@]} 32-bit guard(s) NOT RUN: no working -m32 toolchain (on x86_64 Linux install gcc-multilib)"
    fi
    sel32=()
  fi
fi
for entry in ${sel32[@]+"${sel32[@]}"}; do
  IFS='|' read -r name patch earlier want defect flags32 widths <<<"$entry"
  flags32=${flags32:-$m32}
  widths=${widths:-size_t 4 off 8}
  tag=$(printf '%s' "$flags32" | tr -c 'A-Za-z0-9' '_')
  CFLAGS="$san $flags32" bash "$tests/zlib-ng-build-current.sh" "$work/patched-m32$tag" ||
    CFLAGS="$san $flags32" bash "$tests/build-zlib-ng.sh" "$src" "$work/patched-m32$tag" >"$work/build-m32.log" 2>&1 ||
    { tail -20 "$work/build-m32.log"; exit 2; }
  dir="$work/earlier-m32$tag-${earlier%.patch}"
  if ! REPLACE="$patch=$here/$name/$earlier" CFLAGS="$san $flags32" bash "$tests/zlib-ng-build-current.sh" "$dir"; then
    REPLACE="$patch=$here/$name/$earlier" CFLAGS="$san $flags32" bash "$tests/build-zlib-ng.sh" "$src" "$dir" \
      >"$work/build-m32.log" 2>&1 || { tail -20 "$work/build-m32.log"; exit 2; }
  fi
  for b in "patched-m32$tag" "earlier-m32$tag-${earlier%.patch}"; do
    cc $san $flags32 -I"$work/$b" "$here/$name/repro.c" "$work/$b/libz.a" -o "$work/$name-$b" || exit 2
  done
  echo "== $name (32-bit build: $flags32)"
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-patched-m32$tag" 2>&1); rc=$?
  if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
    echo "UNEXPECTED: with every patch: status $rc: $out"; fail=1
  elif ! printf '%s\n' "$out" | grep -qx "$widths"; then
    echo "UNEXPECTED: not a build with '$widths': $out"; fail=1
  elif printf '%s\n' "$out" | grep -qx "$want"; then
    echo "ok: with every patch: $want, no report"
  else
    echo "UNEXPECTED: with every patch, no line '$want' in: $out"; fail=1
  fi
  out=$(cd "$work" && timeout "$timeout_s" "$work/$name-earlier-m32$tag-${earlier%.patch}" 2>&1); rc=$?
  if printf '%s\n' "$out" | grep -qE "$defect"; then
    echo "ok: with $earlier: $(printf '%s\n' "$out" | grep -m1 -E "$defect")"
  else
    echo "MISSING: with $earlier no line matching '$defect' (status $rc): $out"; fail=1
  fi
done
if [ $fail -eq 0 ]; then
  echo "PASS: every patch reproduction shows its defect without its patch and none with all of them; every plain regression test passes; every open defect still reproduces; every guard shows the earlier defect${skipped32:+; $skipped32 32-bit guard(s) SKIPPED (no -m32 toolchain)}${skippedclang:+; clang case(s)$skippedclang SKIPPED (no clang): their defects are NOT SHOWN}"
fi
exit $fail
