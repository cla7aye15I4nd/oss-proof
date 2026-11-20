#!/usr/bin/env bash
# Generic, host-agnostic Linux build runner for oss-proof remote build hosts.
# Enforces:
#   1. Per-host flock serialization (one heavy build slot at a time per lock file).
#   2. MemAvailable >= MIN_FREE_MEM_GB gate before launching Lean.
#   3. On-disk TMPDIR (never /tmp tmpfs, preventing RAM exhaustion).
#   4. Per-job isolated `systemd-run --user --scope` with MemoryMax and MemorySwapMax=0
#      (never sharing one scope across multiple concurrent workers).
#
# Usage:
#   OSS_PROOF_THREADS=8 OSS_PROOF_MEM_MAX_GB=16 OSS_PROOF_SLICE=ossproof.slice \
#     bash framework/remote_runner.sh <mode: build|gate|difftest> <project_id> [targets...]
set -euo pipefail

MODE="${1:?usage: remote_runner.sh <build|gate|difftest> <project_id> [targets...]}"
PROJECT_ID="${2:?missing project_id}"
shift 2 || true

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export PATH="${OSS_PROOF_LEAN_BIN:-$HOME/.elan/bin}:$PATH"

THREADS="${OSS_PROOF_THREADS:-8}"
MEM_MAX_GB="${OSS_PROOF_MEM_MAX_GB:-16}"
MIN_FREE_GB="${OSS_PROOF_MIN_FREE_GB:-6}"
SLICE="${OSS_PROOF_SLICE:-}"
PYTHON_BIN="${OSS_PROOF_PYTHON:-python3}"

STATE_DIR="${OSS_PROOF_REMOTE_STATE:-$HOME/.local/state/oss-proof}"
LOCK_FILE="${OSS_PROOF_REMOTE_LOCK:-$STATE_DIR/build.lock}"
TMP_BASE="$STATE_DIR/tmp"
mkdir -p "$STATE_DIR" "$TMP_BASE"

JOB_TMP="$(mktemp -d "$TMP_BASE/job.XXXXXX")"
cleanup() {
  # Guard against ever crossing mount boundaries during cleanup.
  if [ -d "$JOB_TMP" ]; then
    rm -rf --one-file-system "$JOB_TMP" 2>/dev/null || rm -rf "$JOB_TMP"
  fi
}
trap cleanup EXIT
export TMPDIR="$JOB_TMP"

wait_for_memory() {
  if [ ! -r /proc/meminfo ]; then
    return 0
  fi
  local min_kb=$((MIN_FREE_GB * 1024 * 1024))
  local waited=0
  while true; do
    local avail_kb
    avail_kb="$(awk '/^MemAvailable:/ {print $2; exit}' /proc/meminfo)"
    if [ -z "$avail_kb" ] || [ "$avail_kb" -ge "$min_kb" ]; then
      return 0
    fi
    if [ "$waited" -ge 300 ]; then
      echo "remote_runner: timed out waiting for MemAvailable >= ${MIN_FREE_GB} GiB (current $((avail_kb / 1024)) MiB)" >&2
      return 1
    fi
    sleep 5
    waited=$((waited + 5))
  done
}

run_capped() {
  export LEAN_NUM_THREADS="$THREADS"
  local -a cmd=("$@")
  if command -v systemd-run >/dev/null 2>&1 && systemctl --user status >/dev/null 2>&1; then
    local -a sd=(
      systemd-run --user --scope --quiet --collect
      -p "MemoryMax=${MEM_MAX_GB}G"
      -p "MemorySwapMax=0"
      -p "OOMPolicy=continue"
    )
    if [ -n "$SLICE" ]; then
      sd+=(--slice="$SLICE")
    fi
    if command -v /usr/bin/time >/dev/null 2>&1; then
      /usr/bin/time -f "PEAK_RSS_KB=%M ELAPSED=%E" "${sd[@]}" "${cmd[@]}"
    else
      "${sd[@]}" "${cmd[@]}"
    fi
  else
    if command -v /usr/bin/time >/dev/null 2>&1; then
      /usr/bin/time -f "PEAK_RSS_KB=%M ELAPSED=%E" "${cmd[@]}"
    else
      "${cmd[@]}"
    fi
  fi
}

exec 9>"$LOCK_FILE"
if command -v flock >/dev/null 2>&1; then
  flock 9
fi

wait_for_memory
cd "$REPO_ROOT"

case "$MODE" in
  build)
    if [ "$#" -gt 0 ]; then
      TARGETS=("$@")
    else
      mapfile -t TARGETS < <("$PYTHON_BIN" - "$PROJECT_ID" <<'PY'
import sys
from framework.manifest import load_project
proj = load_project(sys.argv[1])
for t in proj.targets:
    print(t)
PY
      )
    fi
    set +e
    run_capped lake --dir "projects/$PROJECT_ID" build --wfail "${TARGETS[@]}"
    rc=$?
    set -e
    echo "BUILD_EXIT=$rc"
    exit "$rc"
    ;;
  gate)
    if [ "$#" -gt 0 ]; then
      TARGETS=("$@")
    else
      mapfile -t TARGETS < <("$PYTHON_BIN" - "$PROJECT_ID" <<'PY'
import sys
from framework.manifest import load_project
proj = load_project(sys.argv[1])
for t in proj.targets:
    print(t)
PY
      )
    fi
    set +e
    run_capped lake --dir "projects/$PROJECT_ID" build --wfail "${TARGETS[@]}"
    brc=$?
    set -e
    echo "BUILD_EXIT=$brc"
    [ "$brc" -eq 0 ] || exit "$brc"
    set +e
    "$PYTHON_BIN" framework/check_project.py "$PROJECT_ID" --skip-build
    grc=$?
    set -e
    echo "GATE_EXIT=$grc"
    exit "$grc"
    ;;
  difftest)
    set +e
    run_capped "$PYTHON_BIN" framework/run_difftest.py "$PROJECT_ID" "$@"
    drc=$?
    set -e
    echo "DIFFTEST_EXIT=$drc"
    exit "$drc"
    ;;
  *)
    echo "remote_runner: unknown mode '$MODE' (expected build|gate|difftest)" >&2
    exit 2
    ;;
esac
