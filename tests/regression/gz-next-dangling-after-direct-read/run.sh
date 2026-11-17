#!/usr/bin/env bash
# Usage: ZLIB_SRC=<zlib checkout> bash tests/regression/gz-next-dangling-after-direct-read/run.sh
# Same build and probe as ../gz-reset-next-uninitialised/run.sh (the verified source under ASan
# and UBSan), running dangling.c instead. The probe must see x.next, pointing into the freed caller
# buffer, evaluated with n == 0 in gzseek64 and gz_skip_have, and no sanitizer may report.
here=$(cd "$(dirname "$0")" && pwd)
PROG=dangling PROGDIR=$here WORK=${WORK:-$here/../../../tests/build/gz-next-dangling-after-direct-read} \
  exec bash "$here/../gz-reset-next-uninitialised/run.sh"
