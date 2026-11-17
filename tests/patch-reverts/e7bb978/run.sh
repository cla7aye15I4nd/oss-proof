#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/e7bb978/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# e7bb978 reversed, under ASan and UBSan. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
exec bash "$here/../c-check.sh" "$here"
