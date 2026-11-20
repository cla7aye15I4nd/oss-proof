#!/usr/bin/env bash
# Usage: [CFLAGS=...] mozjpeg-build-current.sh <build-dir>
# Exit 0 when <build-dir> holds a libjpeg.a built from current patches, options, and CFLAGS.
set -euo pipefail
dir=${1:?usage: mozjpeg-build-current.sh <build-dir>}
here=$(cd "$(dirname "$0")" && pwd)
[ -f "$dir/libjpeg.a" ] && [ -f "$dir/BUILD_DIGEST" ] || exit 1
expected=$(bash "$here/build-mozjpeg.sh" --patch-digest)
[ "$(cat "$dir/BUILD_DIGEST")" = "$expected" ]
