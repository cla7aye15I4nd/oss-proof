#!/usr/bin/env bash
# The check of ZlibF/Results.lean (ZlibF/ResultsCheck.lean) on small fixtures: good.lean must pass, every
# other fixture must fail with its message. Needs ZlibF.ResultsCheck built; takes seconds.
#   bash tests/results-check/run.sh
set -uo pipefail
cd "$(dirname "$0")/../.."
status=0
expect() {  # fixture, expected exit (0 or 1), message that must appear
  out=$(lake env lean "tests/results-check/$1" 2>&1); rc=$?
  if { [ "$2" = 0 ] && [ $rc -ne 0 ]; } || { [ "$2" = 1 ] && [ $rc -eq 0 ]; } || ! grep -qF "$3" <<<"$out"; then
    echo "FAIL $1 (exit $rc)"; echo "$out" | head -20; status=1
  else
    echo "ok   $1"
  fi
}
expect good.lean 0 "3 goals defined, 3 listed"
expect wrong-type.lean 1 "is not exactly Fixture.Goal.a"
expect extra-axiom.lean 1 "depends on [Fixture.extra]"
expect unlisted-goal.lean 1 "goal Fixture.Goal.c is neither proved nor listed as not done"
expect required-not-done.lean 1 "required goal Fixture.Goal.c is not proved"
exit $status
