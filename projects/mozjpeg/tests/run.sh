#!/usr/bin/env bash
# Differential test: compare real C (mozjpeg static build under optional ASan+UBSan) against
# the Lean translation byte for byte across all drivers listed in tests/list.txt.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export PATH="$HOME/.elan/bin:$PATH"
build="$here/build"
MOZJPEG_SRC=${MOZJPEG_SRC:-${UPSTREAM_DIR:-}}
sfx=""; cflags=""
if [ "${SAN:-0}" = 1 ]; then sfx="-san"; cflags="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g"; fi
MOZJPEG_BUILD=${MOZJPEG_BUILD:-$build/mozjpeg$sfx}
if ! CFLAGS="$cflags" bash "$here/mozjpeg-build-current.sh" "$MOZJPEG_BUILD"; then
  [ -n "$MOZJPEG_SRC" ] || { echo "run.sh: $MOZJPEG_BUILD is missing or stale; set MOZJPEG_SRC to rebuild" >&2; exit 2; }
  CFLAGS="$cflags" bash "$here/build-mozjpeg.sh" "$MOZJPEG_SRC" "$MOZJPEG_BUILD"
fi
MOZJPEG_BUILD=$(cd "$MOZJPEG_BUILD" && pwd)
echo "mozjpeg under test: patches applied: $(tr '\n' ' ' < "$MOZJPEG_BUILD/PATCHES_APPLIED")"
echo "configuration: $(bash "$here/build-mozjpeg.sh" --cmake-options)"
mkdir -p "$build/bin$sfx" "$build/data"
cd "$here"
names=$(grep -v '^[[:space:]]*\(#\|$\)' list.txt)
total=0
for name in $names; do
  [ -z "${ONLY:-}" ] || [ "$ONLY" = "$name" ] || continue
  cc -O2 -Wall -Wextra $cflags -I"$MOZJPEG_BUILD" "c/$name.c" "$MOZJPEG_BUILD/libjpeg.a" -lm -o "$build/bin$sfx/c_$name"
  lake build --wfail "difftest_$name" >"$build/lake_$name.log" 2>&1 || { cat "$build/lake_$name.log"; echo "run.sh: lake build failed for $name" >&2; exit 2; }
  python3 "gen/$name.py" > "$build/data/$name.in"
  in="$build/data/$name.in"
  "$build/bin$sfx/c_$name" < "$in" > "$build/data/$name.c.out"
  .lake/build/bin/difftest_$name < "$in" > "$build/data/$name.lean.out"
  nin=$(grep -c . "$in"); nc=$(grep -c . "$build/data/$name.c.out"); nl=$(grep -c . "$build/data/$name.lean.out")
  if [ "$nin" != "$nc" ] || [ "$nin" != "$nl" ]; then
    echo "DIFFERENCE ($name): $nin inputs, $nc C results, $nl Lean results"; exit 1
  fi
  if ! cmp -s "$build/data/$name.c.out" "$build/data/$name.lean.out"; then
    n=$(awk 'NR==FNR{a[NR]=$0;next} a[FNR]!=$0{print FNR; exit}' "$build/data/$name.c.out" "$build/data/$name.lean.out")
    echo "DIFFERENCE ($name) at input line $n:"
    echo "  input : $(sed -n "${n}p" "$in" | cut -c1-300)"
    echo "  C     : $(sed -n "${n}p" "$build/data/$name.c.out")"
    echo "  Lean  : $(sed -n "${n}p" "$build/data/$name.lean.out")"
    exit 1
  fi
  echo "== $name: $nin inputs, outputs identical"
  awk '{print $1}' "$in" | sort | uniq -c | awk '{printf "     %-28s %s inputs\n", $2, $1}'
  total=$((total + nin))
done
echo "PASS: $total inputs, C and Lean agree byte for byte"
