#!/usr/bin/env bash
# Usage: bash tests/patch-reverts/run.sh [case id ...]      (default: every row of cases.tsv)
# For each case: the C side (the case's run.sh, see c-check.sh), then the model side. The model side
# copies the translation (ZlibF/Zlib, ZlibF/Runtime) and the test drivers' library (tests/lean) to a
# work directory, builds them once, and runs the case's model.lean there. Then it copies that build,
# applies the case's lean.patch to the copy, rebuilds, and runs model.lean again. Verdict:
#   * on the unmodified translation, model.lean prints exactly what trigger.c prints on the verified
#     source (no fault);
#   * with lean.patch, its output contains the model outcome of the case's row in cases.tsv.
# The repository is never modified. ZLIB_SRC is the zlib checkout (default: the submodule), WORK the
# work directory (default tests/build/patch-reverts). A case whose C side needs another system
# (its run.sh exits 3) is skipped on the C side; its model must then only return without a fault on
# the unmodified translation. Exit status: 0 every case as expected, 1 not, 2 a setup error.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
export WORK=${WORK:-$root/tests/build/patch-reverts}
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
ids=("$@")
[ ${#ids[@]} -gt 0 ] || ids=($(awk -F'\t' '!/^#/ && NF { print $1 }' "$here/cases.tsv"))

# The C builds of the verified source are made again by each run (c-check.sh keeps them per flags).
rm -rf "$WORK"/fixed-*

# The unmodified translation, built once.
base="$WORK/lean-base"
modules="DiffTest.Common DiffTest.Heap"
for f in "$root"/ZlibF/Zlib/*.lean; do modules="$modules ZlibF.Zlib.«$(basename "$f" .lean)»"; done
rm -rf "$base"; mkdir -p "$base"
(cd "$root" && tar -cf - ZlibF/Zlib ZlibF/Runtime lakefile.toml lean-toolchain tests/lean tests/lakefile.toml \
   tests/lean-toolchain tests/lake-manifest.json) | tar -C "$base" -xf -
(cd "$base/tests" && lake build $modules >"$WORK/lean-base.log" 2>&1) ||
  { tail -30 "$WORK/lean-base.log"; echo "run.sh: the translation does not build" >&2; exit 2; }

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

# model <translation copy> <model.lean>: run it interpreted, stopped after $MODEL_LIMIT seconds. The
# fuel of the model's loops is 2^64 iterations, so a hang is seen as a run that does not return.
MODEL_LIMIT=${MODEL_LIMIT:-120}
model() {
  local lp lean out status
  lp=$(cd "$1/tests" && lake env printenv LEAN_PATH)
  lean="$(cd "$1/tests" && lean --print-prefix)/bin/lean"     # the binary itself, not the elan proxy
  out=$(cd "$1/tests" && LEAN_PATH="$lp" limit "$MODEL_LIMIT" "$lean" --run "$2" 2>&1); status=$?
  if [ $status -eq 142 ]; then echo "TIMEOUT: no return within $MODEL_LIMIT seconds"; else printf '%s\n' "$out"; fi
}

fail=0
for id in "${ids[@]}"; do
  case="$here/$id"
  row=$(awk -F'\t' -v id="$id" '$1 == id' "$here/cases.tsv")
  [ -d "$case" ] && [ -n "$row" ] || { echo "run.sh: unknown case $id" >&2; exit 2; }
  expect=$(printf '%s\n' "$row" | cut -f7)
  echo "######## $id: $(printf '%s\n' "$row" | cut -f4): $(printf '%s\n' "$row" | cut -f5)"
  bash "$case/run.sh" >"$WORK/$id.c.log" 2>&1; c=$?
  [ $c -eq 2 ] && { cat "$WORK/$id.c.log"; echo "run.sh: setup error in the C side of $id" >&2; exit 2; }
  if [ $c -eq 0 ]; then echo "C: confirmed (sanitizer finding with the revert, none without)"
  elif [ $c -eq 3 ]; then echo "C: skipped: $(head -1 "$WORK/$id.c.log")"
  else echo "C: NOT CONFIRMED"; grep -E '^(==|ok|MISSING|UNEXPECTED)' "$WORK/$id.c.log"; fail=1; fi

  copy="$WORK/$id/lean"
  rm -rf "$copy"; mkdir -p "$WORK/$id"; cp -a "$base" "$copy"
  (cd "$copy" && patch -p1 --batch --forward < "$case/lean.patch" >"$WORK/$id.lean.log" 2>&1) ||
    { cat "$WORK/$id.lean.log"; echo "run.sh: lean.patch of $id does not apply" >&2; exit 2; }
  (cd "$copy/tests" && lake build $modules >>"$WORK/$id.lean.log" 2>&1) ||
    { tail -30 "$WORK/$id.lean.log"; echo "run.sh: the translation with lean.patch of $id does not build" >&2; exit 2; }
  m0=$(model "$base" "$case/model.lean")
  m1=$(model "$copy" "$case/model.lean")
  cfixed=$(cat "$WORK/$id/run-fixed/stdout" 2>/dev/null)
  echo "model, translation:            $m0"
  echo "model, translation + revert:   $m1"
  if [ $c -eq 3 ] && printf '%s\n' "$m0" | grep -q '^FAULT'; then
    echo "MODEL FAULT on the unmodified translation"; fail=1
  elif [ $c -ne 3 ] && [ "$m0" != "$cfixed" ]; then
    echo "MODEL MISMATCH: the translation does not print what the C prints: $cfixed"; fail=1
  elif ! contains "$m1" "$expect"; then
    echo "MODEL NOT DETECTED: expected $expect"; fail=1
  else
    echo "model: detected"
  fi
done
[ $fail -eq 0 ] && echo "PASS: ${#ids[@]} cases" || echo "FAIL"
exit $fail
