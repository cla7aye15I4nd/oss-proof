#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/a9e14e8/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# a9e14e8 reversed, under ASan and UBSan. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
exec bash "$here/../c-check.sh" "$here"
