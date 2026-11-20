#!/usr/bin/env bash
# Usage: build-mozjpeg.sh <mozjpeg-checkout> <output-dir>
# Copies <mozjpeg-checkout> to <output-dir>/src, applies ../patches/*.patch there in name order,
# and builds static libjpeg.a in <output-dir> under the verified configuration.
#   CFLAGS=<flags>                extra compiler flags (e.g. sanitizers)
#   build-mozjpeg.sh --patch-digest
#   build-mozjpeg.sh --cmake-options
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
patches="$here/../patches"
CMAKE_OPTIONS=(
  -DBUILD_SHARED_LIBS=FALSE
  -DWITH_JPEG8=1
  -DWITH_TURBOJPEG=FALSE
  -DPNG_SUPPORTED=FALSE
  -DWITH_SIMD=FALSE
)
selected_patches() {
  local p
  for p in $(ls "$patches"/*.patch 2>/dev/null | LC_ALL=C sort); do
    echo "$p"
  done
}
build_digest() {
  local p
  for p in $(selected_patches); do
    printf '%s  %s\n' "$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$p")" "$(basename "$p")"
  done
  echo "cmake ${CMAKE_OPTIONS[*]}"
  echo "cflags ${CFLAGS:-}"
}
if [ "${1:-}" = "--patch-digest" ]; then build_digest; exit 0; fi
if [ "${1:-}" = "--cmake-options" ]; then echo "${CMAKE_OPTIONS[*]}"; exit 0; fi
src=${1:?usage: build-mozjpeg.sh <mozjpeg-checkout> <output-dir>}
out=${2:?usage: build-mozjpeg.sh <mozjpeg-checkout> <output-dir>}
[ -f "$src/jpeglib.h" ] || { echo "build-mozjpeg: $src is not a mozjpeg checkout" >&2; exit 2; }
src=$(cd "$src" && pwd)
mkdir -p "$out"
out=$(cd "$out" && pwd)
case "$out" in "$src"|"$src"/*) echo "build-mozjpeg: output must be outside the checkout" >&2; exit 2;; esac
rm -rf "$out"
mkdir -p "$out/src"
(cd "$src" && tar --exclude=.git -cf - .) | tar -C "$out/src" -xf -
: > "$out/PATCHES_APPLIED"
for p in $(selected_patches); do
  (cd "$out/src" && patch -p1 --batch --forward --quiet < "$p")
  basename "$p" >> "$out/PATCHES_APPLIED"
done
cmake -S "$out/src" -B "$out/cmake" "${CMAKE_OPTIONS[@]}" \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DCMAKE_C_FLAGS="-O1 ${CFLAGS:-}" >"$out/cmake.log" 2>&1 || { cat "$out/cmake.log"; exit 1; }
cmake --build "$out/cmake" -j "${JOBS:-4}" --target jpeg-static >"$out/make.log" 2>&1 || { cat "$out/make.log"; exit 1; }
cp "$out/cmake/libjpeg.a" "$out/cmake/jconfig.h" "$out/cmake/jconfigint.h" \
   "$out/src/jpeglib.h" "$out/src/jmorecfg.h" "$out/src/jerror.h" "$out/src/jpegint.h" "$out/src/jinclude.h" "$out/"
build_digest > "$out/BUILD_DIGEST"
echo "built $out/libjpeg.a with patches: $(tr '\n' ' ' < "$out/PATCHES_APPLIED")"
