#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/local-0001/run.sh
# The C side of the case: trigger.c on the verified source and on the source without patch 0001,
# under ASan with the pointer-pair check, and UBSan. See ../c-check.sh. The pointer-pair check needs
# GCC: clang at -O1 reports a comparison inside inflate() on both sources.
here=$(cd "$(dirname "$0")" && pwd)
export CC=${CC:-gcc}
export SAN_EXTRA="-fsanitize=pointer-compare"
export ASAN_OPTIONS="detect_invalid_pointer_pairs=2:detect_leaks=0"
exec bash "$here/../c-check.sh" "$here"
