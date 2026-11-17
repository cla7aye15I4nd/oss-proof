#!/usr/bin/env bash
# No `sorry` is allowed in the Lean sources.
# The search ignores comments and string literals (scripts/lean_sorry.py). With arguments, it
# searches those files and directories instead of the library.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
if [ "$#" -eq 0 ]; then
  cd "$here/.."
  set -- ZlibF ZlibF.lean
fi
if ! python3 "$here/lean_sorry.py" "$@"; then
  echo "error: sorry is not allowed" >&2
  exit 1
fi
