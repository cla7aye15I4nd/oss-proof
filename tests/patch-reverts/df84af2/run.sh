#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/df84af2/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# df84af2 reversed, under ASan and UBSan. trigger.c replaces write() through dlsym. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
[ "$(uname -s)" = Linux ] && export LDLIBS="-ldl"
exec bash "$here/../c-check.sh" "$here"
