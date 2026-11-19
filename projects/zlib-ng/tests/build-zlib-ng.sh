#!/usr/bin/env bash
# Usage: build-zlib-ng.sh <zlib-ng-checkout> <output-dir>
# Copies the zlib-ng checkout (the upstream submodule, at the pinned tag) to <output-dir>/src, applies
# ../patches/*.patch there in name order, and builds the static libz.a in <output-dir> with the verified
# configuration (the option set below). The checkout itself is never modified.
#   CFLAGS=<flags>        extra compiler flags (e.g. sanitizers)
#   EXCLUDE=<prefix>      skip the patches whose file name starts with <prefix> (e.g. 0007); used by the
#                         patch reproductions to build the source before one fix
#   build-zlib-ng.sh --patch-digest   prints the digest of the current patches (one line per patch).
#   build-zlib-ng.sh --cmake-options  prints the verified CMake option set.
# After a build, <output-dir> holds libz.a and the generated zlib.h / zconf.h.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
patches="$here/../patches"
# The verified configuration: the zlib-compatible API, no architecture-specific code, no Chorba CRC, no
# run-time CPU dispatch. With these options every FUNCTABLE_CALL(name) is a direct call to the generic C
# function: adler32 -> adler32_c, crc32 -> crc32_braid.
CMAKE_OPTIONS=(
  -DZLIB_COMPAT=ON
  -DWITH_OPTIM=OFF
  -DWITH_CRC32_CHORBA=OFF
  -DWITH_RUNTIME_CPU_DETECTION=OFF
  -DWITH_NATIVE_INSTRUCTIONS=OFF
  -DWITH_GZFILEOP=ON
  -DWITH_NEW_STRATEGIES=ON
  -DWITH_REDUCED_MEM=OFF
  -DWITH_INFLATE_STRICT=OFF
  -DWITH_INFLATE_ALLOW_INVALID_DIST=OFF
)
selected_patches() {
  local p
  for p in $(ls "$patches"/*.patch 2>/dev/null | LC_ALL=C sort); do
    if [ -n "${EXCLUDE:-}" ]; then
      case "$(basename "$p")" in "$EXCLUDE"*) continue;; esac
    fi
    echo "$p"
  done
}
# One line per applied patch, in application order: its SHA-256 and name, then the option set and CFLAGS.
# Recorded in BUILD_DIGEST of every build, so that a reused build directory can be checked against the
# current patches and configuration (zlib-ng-build-current.sh).
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
src=${1:?usage: build-zlib-ng.sh <zlib-ng-checkout> <output-dir>}
out=${2:?usage: build-zlib-ng.sh <zlib-ng-checkout> <output-dir>}
[ -f "$src/zlib.h.in" ] || { echo "build-zlib-ng: $src is not a zlib-ng checkout" >&2; exit 2; }
src=$(cd "$src" && pwd)
mkdir -p "$out"
out=$(cd "$out" && pwd)
case "$out" in "$src"|"$src"/*) echo "build-zlib-ng: output must be outside the checkout" >&2; exit 2;; esac
rm -rf "$out"
mkdir -p "$out/src"
(cd "$src" && tar --exclude=.git -cf - .) | tar -C "$out/src" -xf -
: > "$out/PATCHES_APPLIED"
for p in $(selected_patches); do
  (cd "$out/src" && patch -p1 --batch --forward --quiet < "$p")
  basename "$p" >> "$out/PATCHES_APPLIED"
done
cmake -S "$out/src" -B "$out/cmake" "${CMAKE_OPTIONS[@]}" \
  -DBUILD_SHARED_LIBS=OFF -DBUILD_TESTING=OFF -DCMAKE_BUILD_TYPE=None \
  -DCMAKE_C_FLAGS="-O1 ${CFLAGS:-}" >"$out/cmake.log" 2>&1 || { cat "$out/cmake.log"; exit 1; }
cmake --build "$out/cmake" -j "${JOBS:-4}" >"$out/make.log" 2>&1 || { cat "$out/make.log"; exit 1; }
cp "$out/cmake/libz.a" "$out/cmake/zlib.h" "$out/cmake/zconf.h" "$out/cmake/zlib_name_mangling.h" "$out/"
# The configuration check: the public checksum entry points must call the generic kernels directly.
nm -A "$out/libz.a" > "$out/symbols.txt" 2>/dev/null
if grep -qE '[ :]_?(crc32_chorba[a-z0-9_]*|functable|init_functable)$' "$out/symbols.txt"; then
  echo "build-zlib-ng: libz.a contains Chorba or functable symbols; the configuration is not the verified one" >&2
  exit 1
fi
for want in 'adler32\.c\.o:.* U _?adler32_c$' 'crc32\.c\.o:.* U _?crc32_braid$'; do
  grep -qE "$want" "$out/symbols.txt" || {
    echo "build-zlib-ng: no reference matching '$want' in libz.a; the configuration is not the verified one" >&2
    exit 1
  }
done
build_digest > "$out/BUILD_DIGEST"
echo "built $out/libz.a with patches: $(tr '\n' ' ' < "$out/PATCHES_APPLIED")"
