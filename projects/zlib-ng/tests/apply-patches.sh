#!/usr/bin/env bash
# Usage: apply-patches.sh [options] <tree>
# Applies the patch series of ../patches to <tree>, a copy of the pinned zlib-ng source (without .git), in
# directory name order. Each series is ../patches/NNNN-slug/upstream.patch, a `git format-patch` series that may hold
# several commits and test/ hunks; it is applied in full with `git apply` (which applies the commits of one file in
# order), never with a fuzz factor, offline. This is the rule that forms the verified source (../patches/README.md).
#   --library-only            apply only the hunks outside test/ (the library; what build-zlib-ng.sh builds)
#   --without <prefix>        leave out the library hunks of the series whose directory name starts with <prefix>
#                             (its test/ hunks are still applied unless --library-only); used to build the source
#                             before one fix
#   --replace <prefix>=<file> apply <file> (library hunks only) in place of that series; used by the regression
#                             guards to build an earlier, defective version of one fix
#   --list                    print the series that would be applied, one path per line, and apply nothing
# Fails (exit 2) when no series is found, when a directory lacks upstream.patch, when ../patches holds a flat
# *.patch file, or when a prefix selects no series; fails (exit 1) when a series does not apply.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
patches=${PATCHES_DIR:-$here/../patches}
lib_only="" without="" replace="" list=""
while [ $# -gt 0 ]; do
  case "$1" in
    --library-only) lib_only=1; shift;;
    --without) without=$2; shift 2;;
    --replace) replace=$2; shift 2;;
    --list) list=1; shift;;
    --) shift; break;;
    -*) echo "apply-patches: unknown option $1" >&2; exit 2;;
    *) break;;
  esac
done
die() { echo "apply-patches: $*" >&2; exit 2; }
if compgen -G "$patches/*.patch" >/dev/null; then die "flat patch files in $patches (the layout is one directory per patch)"; fi
series=()
while IFS= read -r d; do
  [ -n "$d" ] || continue
  [ -f "$d/upstream.patch" ] || die "$d has no upstream.patch"
  series+=("$d")
done < <(find "$patches" -mindepth 1 -maxdepth 1 -type d -name '[0-9][0-9][0-9][0-9]-*' | LC_ALL=C sort)
[ ${#series[@]} -gt 0 ] || die "no patch directories in $patches"
for pre in "$without" "${replace%%=*}"; do
  [ -z "$pre" ] && continue
  n=0
  for d in "${series[@]}"; do case "$(basename "$d")" in "$pre"*) n=$((n + 1));; esac; done
  [ $n -eq 1 ] || die "prefix '$pre' selects $n patch directories, not one"
done
if [ -n "$list" ]; then
  for d in "${series[@]}"; do
    name=$(basename "$d")
    if [ -n "$replace" ]; then case "$name" in "${replace%%=*}"*) echo "${replace#*=}"; continue;; esac; fi
    if [ -n "$without" ] && [ -n "$lib_only" ]; then case "$name" in "$without"*) continue;; esac; fi
    echo "$d/upstream.patch"
  done
  exit 0
fi
tree=${1:?usage: apply-patches.sh [options] <tree>}
[ -d "$tree" ] || die "$tree is not a directory"
[ ! -e "$tree/.git" ] || die "$tree has a .git; apply to an exported copy"
tree=$(cd "$tree" && pwd)
# Without a ceiling, git apply run inside another work tree applies paths relative to that tree's top and skips
# the rest silently.
export GIT_CEILING_DIRECTORIES
GIT_CEILING_DIRECTORIES=$(dirname "$tree")
apply() { (cd "$tree" && git apply --whitespace=nowarn "$@") || { echo "apply-patches: ${*: -1} does not apply" >&2; exit 1; }; }
for d in "${series[@]}"; do
  name=$(basename "$d")
  if [ -n "$replace" ]; then
    case "$name" in "${replace%%=*}"*)
      apply --exclude='test/*' "${replace#*=}"
      [ -n "$lib_only" ] || apply --include='test/*' "$d/upstream.patch"
      continue;;
    esac
  fi
  if [ -n "$without" ]; then
    case "$name" in "$without"*)
      [ -n "$lib_only" ] || apply --include='test/*' "$d/upstream.patch"
      continue;;
    esac
  fi
  if [ -n "$lib_only" ]; then apply --exclude='test/*' "$d/upstream.patch"; else apply "$d/upstream.patch"; fi
done
