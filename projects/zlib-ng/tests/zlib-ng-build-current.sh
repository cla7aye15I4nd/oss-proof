#!/usr/bin/env bash
# Usage: [CFLAGS=...] [EXCLUDE=...] zlib-ng-build-current.sh <build-dir>
# Exit 0 when <build-dir> holds a libz.a that build-zlib-ng.sh made from the current ../patches/NNNN-slug series
# (same names, contents and order), the same CMake option set and the same CFLAGS; exit 1 otherwise. The
# differential test and the reproductions reuse build directories across commits, so a tree built before a
# patch or the configuration changed must not be reused.
set -euo pipefail
dir=${1:?usage: zlib-ng-build-current.sh <build-dir>}
here=$(cd "$(dirname "$0")" && pwd)
[ -f "$dir/libz.a" ] && [ -f "$dir/BUILD_DIGEST" ] || exit 1
expected=$(bash "$here/build-zlib-ng.sh" --patch-digest)
[ "$(cat "$dir/BUILD_DIGEST")" = "$expected" ]
