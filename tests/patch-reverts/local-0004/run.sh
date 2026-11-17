#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/local-0004/run.sh
# The C side of the case: trigger.c on the verified source and on the source without patch 0004,
# under ASan and UBSan. See ../c-check.sh. Linux only: it needs a /dev/zero on which lseek succeeds
# without moving; elsewhere it exits 3 (skipped).
here=$(cd "$(dirname "$0")" && pwd)
[ "$(uname -s)" = Linux ] || { echo "skip: needs Linux (/dev/zero with a succeeding lseek)"; exit 3; }
exec bash "$here/../c-check.sh" "$here"
