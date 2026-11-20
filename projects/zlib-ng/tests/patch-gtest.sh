#!/usr/bin/env bash
# Usage: ZLIB_NG_SRC=<zlib-ng checkout> bash tests/patch-gtest.sh [patch-prefix...]
# Runs the GoogleTest cases that the patch series add (upstream's own test suite, test/gtest_zlib), as each
# ../patches/NNNN-slug/gtest.txt lists them:
#   <gtest filter> <fails without this patch: yes|no> [VAR=value ...]
# 1. Builds the verified source with every series applied in full (library and test hunks; apply-patches.sh) with
#    upstream's CMake, tests on, under AddressSanitizer (pointer-pair checks on C only) and UndefinedBehaviorSanitizer,
#    and runs every listed filter: each must run at least one test, none skipped, and pass without a report.
# 2. For every patch with a "yes" line, builds the same source without that patch's library hunks (its test hunks
#    stay) and runs its "yes" filters: each must fail (a failed test or a sanitizer report).
# The build flags follow the series' own verification: CMAKE_BUILD_TYPE=None, -O0, the sanitizers above with
# detect_invalid_pointer_pairs=2, and the verified option set of build-zlib-ng.sh (--cmake-options).
# GoogleTest is the release upstream's test/CMakeLists.txt asks for (GTEST_TAG v1.16.0), pinned here by commit and
# fetched once into $WORK/googletest (or taken from GTEST_SRC, which must be a checkout of that commit); the builds
# themselves are offline. Build trees are reused while their digest (series, flags, GoogleTest) is unchanged.
#   WORK=<dir>   build directory (default tests/build/patch-gtest)
#   CC, CXX      compilers (default clang, clang++)
#   JOBS         parallel build jobs (default 4)
# Exit status: 0 every check holds, 1 a check fails, 2 a setup error.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
patches=$(cd "$here/../patches" && pwd)
src=${ZLIB_NG_SRC:-${UPSTREAM_DIR:-$here/../zlib-ng}}
[ -f "$src/zlib.h.in" ] || { echo "patch-gtest: set ZLIB_NG_SRC to the pinned zlib-ng checkout" >&2; exit 2; }
src=$(cd "$src" && pwd)
work=${WORK:-$here/build/patch-gtest}
mkdir -p "$work"
work=$(cd "$work" && pwd)
CC=${CC:-clang}
CXX=${CXX:-clang++}
jobs=${JOBS:-4}
GTEST_REPO=https://github.com/google/googletest.git
GTEST_COMMIT=6910c9d9165801d8827d628cb72eb7ea9dd538c5 # v1.16.0
cflags="-O0 -g -fsanitize=address,pointer-compare,pointer-subtract,undefined -fno-sanitize-recover=undefined"
cxxflags="-O0 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined"
export ASAN_OPTIONS="detect_invalid_pointer_pairs=2:detect_leaks=0"
export UBSAN_OPTIONS="print_stacktrace=1"

setup() { echo "patch-gtest: $*" >&2; exit 2; }

# The entries: patch directory, filter, yes/no, environment.
entries=()
for f in $(find "$patches" -mindepth 2 -maxdepth 2 -name gtest.txt | LC_ALL=C sort); do
  d=$(basename "$(dirname "$f")")
  if [ $# -gt 0 ]; then
    sel=""; for p in "$@"; do case "$d" in "$p"*) sel=1;; esac; done
    [ -n "$sel" ] || continue
  fi
  while read -r filter fails rest; do
    case "$filter" in ''|'#'*) continue;; esac
    case "$fails" in yes|no) ;; *) setup "$f: '$filter': the second field must be yes or no";; esac
    for kv in $rest; do case "$kv" in *=*) ;; *) setup "$f: '$filter': '$kv' is not VAR=value";; esac; done
    entries+=("$d|$filter|$fails|$rest")
  done < "$f"
done
[ ${#entries[@]} -gt 0 ] || setup "no gtest.txt entries${*:+ for $*}"

# GoogleTest at the pinned commit.
gtest=${GTEST_SRC:-$work/googletest}
if [ -z "${GTEST_SRC:-}" ] && [ "$(git -C "$gtest" rev-parse HEAD 2>/dev/null)" != "$GTEST_COMMIT" ]; then
  rm -rf "$gtest"
  git init -q "$gtest" && git -C "$gtest" fetch -q --depth 1 "$GTEST_REPO" "$GTEST_COMMIT" &&
    git -C "$gtest" checkout -q FETCH_HEAD || setup "could not fetch GoogleTest $GTEST_COMMIT"
fi
[ "$(git -C "$gtest" rev-parse HEAD 2>/dev/null)" = "$GTEST_COMMIT" ] || setup "$gtest is not GoogleTest $GTEST_COMMIT"

read -r -a verified <<<"$(bash "$here/build-zlib-ng.sh" --cmake-options)"

# build <name> [apply-patches options...]: the source with the selected series, built with tests, in $work/<name>.
build() {
  local name=$1; shift
  local dir="$work/$name" digest p
  digest=$( { for p in $(bash "$here/apply-patches.sh" --list "$@"); do shasum -a 256 "$p" | cut -d' ' -f1; done
              echo "$* | $CC | $CXX | $cflags | $cxxflags | ${verified[*]} | $GTEST_COMMIT"; } )
  if [ -x "$dir/gtest_zlib" ] && [ "$(cat "$dir/DIGEST" 2>/dev/null)" = "$digest" ]; then return 0; fi
  rm -rf "$dir"; mkdir -p "$dir/src"
  (cd "$src" && tar --exclude=.git -cf - .) | tar -C "$dir/src" -xf -
  bash "$here/apply-patches.sh" "$@" "$dir/src" || setup "the series do not apply for $name"
  cmake -S "$dir/src" -B "$dir/cmake" "${verified[@]}" -DBUILD_SHARED_LIBS=OFF -DBUILD_TESTING=ON -DWITH_GTEST=ON \
    -DWITH_FUZZERS=OFF -DWITH_BENCHMARKS=OFF -DWITH_BENCHMARK_APPS=OFF -DCMAKE_BUILD_TYPE=None \
    -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DCMAKE_C_FLAGS="$cflags" -DCMAKE_CXX_FLAGS="$cxxflags" \
    -DCMAKE_DISABLE_FIND_PACKAGE_GTest=ON -DFETCHCONTENT_FULLY_DISCONNECTED=ON \
    -DFETCHCONTENT_SOURCE_DIR_GOOGLETEST="$gtest" >"$dir/cmake.log" 2>&1 || { tail -30 "$dir/cmake.log"; setup "cmake failed for $name"; }
  cmake --build "$dir/cmake" --target gtest_zlib -j "$jobs" >"$dir/make.log" 2>&1 || { tail -40 "$dir/make.log"; setup "build failed for $name"; }
  p=$(find "$dir/cmake" -name gtest_zlib -type f -perm -u+x | head -1)
  [ -n "$p" ] || setup "no gtest_zlib in $dir/cmake"
  cp "$p" "$dir/gtest_zlib"
  printf '%s\n' "$digest" > "$dir/DIGEST"
}

# run <binary> <filter> <env>: sets $out and $rc.
run() {
  out=$(cd "$work" && env $3 "$1" --gtest_filter="$2" 2>&1); rc=$?
}
report() { printf '%s\n' "$out" | grep -m1 -E "runtime error|ERROR: AddressSanitizer|\[  FAILED  \]" || true; }

fail=0
build all
for e in "${entries[@]}"; do
  IFS='|' read -r d filter fails envs <<<"$e"
  echo "== $d: $filter${envs:+ ($envs)}"
  run "$work/all/gtest_zlib" "$filter" "$envs"
  ran=$(printf '%s\n' "$out" | sed -n 's/^\[==========\] \([0-9]*\) tests\{0,1\} from .* ran\..*/\1/p' | tail -1)
  if [ $rc -ne 0 ] || printf '%s\n' "$out" | grep -q "runtime error\|ERROR: AddressSanitizer"; then
    echo "FAIL: with every patch: status $rc: $(report)"; fail=1
  elif [ -z "$ran" ] || [ "$ran" -eq 0 ]; then
    echo "FAIL: with every patch: the filter ran no test"; fail=1
  elif printf '%s\n' "$out" | grep -q '^\[  SKIPPED \]'; then
    echo "FAIL: with every patch: a test was skipped (missing environment?)"; fail=1
  else
    echo "ok: with every patch: $ran test(s) passed, no report"
  fi
done
for d in $(printf '%s\n' "${entries[@]}" | awk -F'|' '$3 == "yes" {print $1}' | LC_ALL=C sort -u); do
  build "without-$d" --without "$d"
  for e in "${entries[@]}"; do
    IFS='|' read -r ed filter fails envs <<<"$e"
    [ "$ed" = "$d" ] && [ "$fails" = yes ] || continue
    echo "== $d: $filter${envs:+ ($envs)} without the patch"
    run "$work/without-$d/gtest_zlib" "$filter" "$envs"
    if [ $rc -ne 0 ] && printf '%s\n' "$out" | grep -qE "runtime error|ERROR: AddressSanitizer|\[  FAILED  \]"; then
      echo "ok: without $d: $(report)"
    else
      echo "MISSING: without $d the test does not fail (status $rc)"; printf '%s\n' "$out" | tail -5; fail=1
    fi
  done
done
[ $fail -eq 0 ] && echo "PASS: every listed GoogleTest case passes with every patch, and each marked one fails without its patch"
exit $fail
