#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/local-0003/run.sh
# The C side of the case: trigger.c on the verified source and on the source without patch 0003,
# under ASan and UBSan. trigger.c replaces read() through dlsym. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
[ "$(uname -s)" = Linux ] && export LDLIBS="-ldl"
exec bash "$here/../c-check.sh" "$here"
