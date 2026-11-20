#!/usr/bin/env bash
# Usage: bash tests/patch-source-identity.sh <git-rev> [expected-diff]
# Compares the library part of the verified source (everything outside test/) formed from the patch series of
# ../patches (apply-patches.sh --library-only) with the source formed from the flat patches of an earlier commit
# (projects/zlib-ng/patches/*.patch at <git-rev>, applied in name order), both on the pinned submodule. Prints
# `diff -r` of the two trees (before/ = <git-rev>, after/ = now). Exit 0 when the diff is empty, or equals the
# contents of [expected-diff] when given; 1 otherwise; 2 on a setup error. Used when the patch layout changed to
# show that the proved library source did not.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
proj=$(cd "$here/.." && pwd)
rev=${1:?usage: patch-source-identity.sh <git-rev> [expected-diff]}
expected=${2:-}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pin=$(git -C "$proj" ls-tree "$rev" zlib-ng | awk '{print $3}')
[ "$pin" = "$(git -C "$proj/zlib-ng" rev-parse HEAD)" ] || { echo "patch-source-identity: the submodule pin of $rev is not the checked-out one" >&2; exit 2; }
mkdir -p "$work/before" "$work/after" "$work/old"
git -C "$proj/zlib-ng" archive HEAD | tar -C "$work/before" -xf -
git -C "$proj/zlib-ng" archive HEAD | tar -C "$work/after" -xf -
names=$(git -C "$proj" ls-tree --name-only "$rev" patches/ | grep '\.patch$' | LC_ALL=C sort)
[ -n "$names" ] || { echo "patch-source-identity: no flat patches at $rev" >&2; exit 2; }
export GIT_CEILING_DIRECTORIES="$work"
for n in $names; do
  git -C "$proj" show "$rev:projects/zlib-ng/$n" > "$work/old/$(basename "$n")"
  (cd "$work/before" && git apply "$work/old/$(basename "$n")")
done
bash "$here/apply-patches.sh" --library-only "$work/after"
out=$(cd "$work" && diff -r -x test before after || true)
printf '%s\n' "$out"
if [ -n "$expected" ]; then
  [ "$out" = "$(cat "$expected")" ] && { echo "SAME: the library sources differ exactly as $expected says"; exit 0; }
  echo "DIFFERENT: the library sources differ otherwise than $expected says"; exit 1
fi
[ -z "$out" ] && { echo "SAME: the library sources are identical"; exit 0; }
echo "DIFFERENT"; exit 1
