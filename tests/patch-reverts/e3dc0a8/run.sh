#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/patch-reverts/e3dc0a8/run.sh
# The C side of the case: trigger.c on the verified source and on the source with upstream commit
# e3dc0a8 reversed, under ASan with the pointer-pair check, and UBSan. See ../c-check.sh. As in
# local-0001, the case uses GCC for the pointer-pair check. (UBSan does not report the null pointer
# plus zero offset here, with GCC or clang.)
here=$(cd "$(dirname "$0")" && pwd)
export CC=${CC:-gcc}
export SAN_EXTRA="-fsanitize=pointer-compare"
export ASAN_OPTIONS="detect_invalid_pointer_pairs=2:detect_leaks=0"
exec bash "$here/../c-check.sh" "$here"
