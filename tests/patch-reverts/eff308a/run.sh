#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/eff308a/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commits
# 1eb7682 and eff308a reversed, under ASan and UBSan. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
exec bash "$here/../c-check.sh" "$here"
