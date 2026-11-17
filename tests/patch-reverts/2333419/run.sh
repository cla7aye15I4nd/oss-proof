#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/2333419/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# 2333419 reversed, under ASan and UBSan. ASan fills every allocation with zeros, so that a field
# that is never set reads 0. See ../c-check.sh.
here=$(cd "$(dirname "$0")" && pwd)
export ASAN_OPTIONS="detect_leaks=0:malloc_fill_byte=0:max_malloc_fill_size=1048576"
exec bash "$here/../c-check.sh" "$here"
