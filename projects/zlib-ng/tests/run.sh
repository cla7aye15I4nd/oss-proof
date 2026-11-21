#!/usr/bin/env bash
# Differential test: for every driver listed in tests/list.txt, run the REAL C function and the Lean
# translation on the same inputs and compare the outputs byte for byte; then run the patch reproductions and the
# GoogleTest cases of the patch series.
#
#   ZLIB_NG_SRC=<zlib-ng checkout>  bash tests/run.sh   # builds the patched copy of zlib-ng, then tests
#   ZLIB_NG_BUILD=<dir>             bash tests/run.sh   # reuse a copy made by build-zlib-ng.sh
#   ONLY=<name>               run only that list entry (or ONLY=patches: only the reproductions and GoogleTest cases)
#   SAN=1                     build zlib-ng and the C drivers with ASan+UBSan (and run them so)
# Exit status: 0 all equal, 1 a difference (the first one is printed), 2 a setup error.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
build="$here/build"
ZLIB_NG_SRC=${ZLIB_NG_SRC:-${UPSTREAM_DIR:-}}
sfx=""; cflags=""
if [ "${SAN:-0}" = 1 ]; then sfx="-san"; cflags="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g"; fi
ZLIB_NG_BUILD=${ZLIB_NG_BUILD:-$build/zlib-ng$sfx}
if ! CFLAGS="$cflags" bash "$here/zlib-ng-build-current.sh" "$ZLIB_NG_BUILD"; then
  # A missing build, or one made before the current patches or configuration (the directory persists).
  [ -n "$ZLIB_NG_SRC" ] || { echo "run.sh: $ZLIB_NG_BUILD is missing or not built from the current patches; set ZLIB_NG_SRC to rebuild it" >&2; exit 2; }
  CFLAGS="$cflags" bash "$here/build-zlib-ng.sh" "$ZLIB_NG_SRC" "$ZLIB_NG_BUILD"
fi
ZLIB_NG_BUILD=$(cd "$ZLIB_NG_BUILD" && pwd)
echo "zlib-ng under test: patches applied: $(tr '\n' ' ' < "$ZLIB_NG_BUILD/PATCHES_APPLIED")"
echo "configuration: $(bash "$here/build-zlib-ng.sh" --cmake-options)"
mkdir -p "$build/bin$sfx" "$build/data"
cd "$here"
names=$(grep -v '^[[:space:]]*\(#\|$\)' list.txt)
total=0
for name in $names; do
  [ -z "${ONLY:-}" ] || [ "$ONLY" = "$name" ] || continue
  cc -O2 -Wall -Wextra $cflags -I"$ZLIB_NG_BUILD" "c/$name.c" "$ZLIB_NG_BUILD/libz.a" -o "$build/bin$sfx/c_$name"
  if [ "${SKIP_LAKE_BUILD:-0}" != 1 ]; then
    LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake build --wfail "difftest_$name" >"$build/lake_$name.log" 2>&1 || { cat "$build/lake_$name.log"; echo "run.sh: lake build failed for $name" >&2; exit 2; }
  fi
  python3 "gen/$name.py" > "$build/data/$name.in"
  in="$build/data/$name.in"
  "$build/bin$sfx/c_$name" < "$in" > "$build/data/$name.c.out"
  .lake/build/bin/difftest_$name < "$in" > "$build/data/$name.lean.out"
  # Open defects (undefined behaviour of the verified source, no patch yet): on the inputs listed in
  # expected-faults.txt the translation must fault with the listed message; see expected_faults.py.
  python3 expected_faults.py "$name" "$in" "$build/data/$name.c.out" "$build/data/$name.lean.out" || exit 1
  nin=$(grep -c . "$in"); nc=$(grep -c . "$build/data/$name.c.out"); nl=$(grep -c . "$build/data/$name.lean.out")
  if [ "$nin" != "$nc" ] || [ "$nin" != "$nl" ]; then
    echo "DIFFERENCE ($name): $nin inputs, $nc C results, $nl Lean results"; exit 1
  fi
  if ! cmp -s "$build/data/$name.c.out" "$build/data/$name.lean.out"; then
    n=$(awk 'NR==FNR{a[NR]=$0;next} a[FNR]!=$0{print FNR; exit}' "$build/data/$name.c.out" "$build/data/$name.lean.out")
    echo "DIFFERENCE ($name) at input line $n:"
    echo "  input : $(sed -n "${n}p" "$in" | cut -c1-300) (line length $(sed -n "${n}p" "$in" | wc -c))"
    echo "  C     : $(sed -n "${n}p" "$build/data/$name.c.out")"
    echo "  Lean  : $(sed -n "${n}p" "$build/data/$name.lean.out")"
    echo "  files : $in  $build/data/$name.c.out  $build/data/$name.lean.out"
    exit 1
  fi
  echo "== $name: $nin inputs, outputs identical"
  # Round trip: the translation's deflate output, inflated by the real C inflate, gives back the input.
  if [ "$name" = deflate ]; then
    "$build/bin$sfx/c_deflate" roundtrip "$build/data/$name.lean.out" < "$in" || { echo "FAIL: round trip" >&2; exit 1; }
  fi
  awk '{print $1}' "$in" | sort | uniq -c | awk '{printf "     %-24s %s inputs\n", $2, $1}'
  total=$((total + nin))
done
echo "PASS: $total inputs, C and Lean agree byte for byte"

# The patches: each reproduction builds the source with every patch but its own and shows the defect on
# the real C, then builds the verified source and shows none.
if [ -z "${ONLY:-}" ] || [ "$ONLY" = patches ]; then
  [ -n "$ZLIB_NG_SRC" ] || { echo "run.sh: the patch reproductions need ZLIB_NG_SRC" >&2; exit 2; }
  ZLIB_NG_SRC="$ZLIB_NG_SRC" bash "$here/regression/run.sh" || { echo "FAIL: patch reproductions" >&2; exit 1; }
  # The GoogleTest cases of the patch series (patches/*/gtest.txt): they pass with every patch, and each marked one
  # fails without its patch.
  ZLIB_NG_SRC="$ZLIB_NG_SRC" bash "$here/patch-gtest.sh" || { echo "FAIL: patch GoogleTest cases" >&2; exit 1; }
fi
