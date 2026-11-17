#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/7dd6aa7/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# 7dd6aa7 reversed, under ASan and UBSan. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
exec bash "$here/../c-check.sh" "$here"
