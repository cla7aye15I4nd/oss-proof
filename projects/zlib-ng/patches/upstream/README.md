# Upstream Patch Review Bundle (`zlib-ng/zlib-ng`)

Submission-ready patch series against upstream `zlib-ng/zlib-ng` (`develop` @ `5f1f489934a5b298a835acf22db84d480ac14c22`), corresponding to the local proof patches in [../README.md](../README.md) (and Finding 18 in [../../docs/en/findings.md](../../docs/en/findings.md)).

Compared with the minimal proof patches in `projects/zlib-ng/patches/`, each `upstream.patch` here adds upstream-style commit messages (with proper `madler/zlib` commit attribution where adapted), GoogleTest regression tests in `test/`, and updates addressing upstream maintainer (`nmoinvaz`) and CodeRabbit review feedback on open PRs.

## Index

Total: **20 entries** (**18** runnable `upstream.patch` series + **2** 0-commit duplicate trackers `0009`/`0010`).

| Entry | Local Proof Reference | Upstream PR / Status | Commits | Modified Files |
| --- | --- | --- | --- | --- |
| [0003](0003/pr-summary.md) | `0003-inflate-copy-pointer-equality.patch` | [zlib-ng#2524](https://github.com/zlib-ng/zlib-ng/pull/2524) (open) | 1 | `inflate.c`, `test/test_inflate_copy.cc` |
| [0004](0004/pr-summary.md) | `0004-gzseek-overflow.patch` | [zlib-ng#2525](https://github.com/zlib-ng/zlib-ng/pull/2525) (open; revised) | 4 | `gzguts.h`, `gzlib.c`, `zlib.h.in`, `zlib-ng.h.in`, `test/test_gzseek.cc` |
| [0006](0006/pr-summary.md) | `0006-deflatebound-gzip-extra-length.patch` | [zlib-ng#2523](https://github.com/zlib-ng/zlib-ng/pull/2523) (open; revised) | 1 | `deflate.c`, `test/test_deflate_bound.cc` |
| [0007](0007/pr-summary.md) | `0007-inflate-window-copy.patch` | Ready to submit | 1 | `inffast_tpl.h`, `inflate.c`, `test/test_inflate_back.cc`, `test/test_inflate_far_distance.cc` |
| [0008](0008/pr-summary.md) | `0008-inflatesync-null-next-in.patch` | Ready to submit | 1 | `inflate.c`, `test/test_inflate_sync.cc` |
| [0009](0009/pr-summary.md) | `0009-inflatesetdictionary-null.patch` | Duplicate of [zlib-ng#2516](https://github.com/zlib-ng/zlib-ng/pull/2516) | 0 | — (`inflate.c`, `test/test_inflate_api_errors.cc` in `#2516`) |
| [0010](0010/pr-summary.md) | `0010-inflate-fast-primed-bits.patch` | Duplicate of [zlib-ng#2526](https://github.com/zlib-ng/zlib-ng/pull/2526) | 0 | — (`inflate.c`, tests in `#2526`) |
| [0011](0011/pr-summary.md) | `0011-inflate-extra-copy-bound.patch` | [zlib-ng#2528](https://github.com/zlib-ng/zlib-ng/pull/2528) (open; revised) | 1 | `inflate.c`, `test/test_inflate_copy.cc` |
| [0012](0012/pr-summary.md) | `0012-longest-match-offset-base.patch` | Ready to submit | 1 | `match_tpl.h`, `test/test_deflate.cc` |
| [0013](0013/pr-summary.md) | `0013-deflate-medium-insert-count.patch` | Ready to submit (+ `deflate_fast` hardening) | 1 | `deflate_fast.c`, `deflate_medium_tpl.h`, `test/test_deflate_tune.cc` |
| [0014](0014/pr-summary.md) | `0014-gzwrite-caller-buffer-pointer.patch` | [zlib-ng#2527](https://github.com/zlib-ng/zlib-ng/pull/2527) (open; revised) | 1 | `gzwrite.c`, `test/test_gzfile_api_errors.cc` |
| [0015](0015/pr-summary.md) | `0015-gz-buffer-alloc-null-offset.patch` | Ready to submit | 1 | `gzlib.c`, `test/test_gzfile_api_errors.cc` |
| [0016](0016/pr-summary.md) | `0016-gzread-position-bound.patch` | Ready to submit (upgraded with `gz_room`) | 1 | `gzguts.h`, `gzread.c`, `test/test_gzio.cc` |
| [0017](0017/pr-summary.md) | `0017-gzwrite-position-bound.patch` | Ready to submit (upgraded; `uint64_t` room) | 1 | `gzguts.h`, `gzwrite.c`, `test/test_gzio.cc` |
| [0018](0018/pr-summary.md) | `0018-fill-window-block-start-bound.patch` | Ready to submit | 1 | `deflate.c`, `test/test_deflate_cve.cc` |
| [0019](0019/pr-summary.md) | `0019-deflate-slow-match-start-bound.patch` | Ready to submit (root-cause `CLEAR_HASH`) | 1 | `deflate.c`, `test/test_deflate_params.cc` |
| [0020](0020/pr-summary.md) | `0020-gzdirect-pending-skip.patch` | Ready to submit (`madler/zlib@b2596bde` + guard) | 2 | `gzread.c`, `test/test_gzseek.cc` |
| [0021](0021/pr-summary.md) | `0021-gzgets-pending-skip.patch` | Ready to submit (`madler/zlib@f40786e3` + `gzgets`) | 2 | `gzread.c`, `test/test_gzseek.cc` |
| [0022](0022/pr-summary.md) | `0022-gzwrite-zero-skip-on-failure.patch` | Ready to submit (`madler/zlib@51c7cd2c` port) | 1 | `gzwrite.c`, `test/test_gzio.cc` |
| [deflate-reset-block-open](deflate-reset-block-open/pr-summary.md) | Finding 18 (`not patched` locally yet) | Ready to submit (`block_open = 0` on reset) | 1 | `deflate.c`, `test/test_deflate_quick_block_open.cc` |

---

## Overlap, Conflict, and Merge-Order Matrix

All 18 runnable patch series were audited together for source overlap, test-file collision, and interaction with open upstream PRs.

### 1. Shared Library Source Files

| File | Series Touching File | Conflict / Semantic Relationship |
| --- | --- | --- |
| `gzguts.h` | `0004`, `0016`, `0017` | All three add the identical `GZ_OFF_MAX` macro at EOF so each PR builds standalone. Once `0004` (`#2525`) merges, `0016` and `0017` drop their duplicate `GZ_OFF_MAX` addition cleanly. |
| `gzread.c` | `0016`, `0020`, `0021` | **Disjoint hunks; must rebase `0021` after `0020`.** `0016` bounds `gz_look`, `gz_fetch`, `gz_read`, and copy size in `gzgets`. `0020` extracts `gz_skip_have()` from `gz_skip()` and calls it from `gzdirect()`. `0021` updates `gz_skip()` EOF handling and adds the EOF/pending-skip early return before `gz_fetch()` in `gzgets()`. |
| `gzwrite.c` | `0014`, `0017`, `0022` | **Completely disjoint functions; zero conflict.** `0014` touches `gz_write_init()` and `gz_write()` direct-path error handling; `0017` guards `gz_write()`, `gzputc()`, and `gzvprintf()` against `GZ_OFF_MAX`; `0022` fixes consumed byte accounting in `gz_zero()`. |
| `inflate.c` | `0003`, `0007`, `0008`, `0011` | **Completely disjoint functions/states; zero conflict.** (`0007`: `MATCH` state; `0011`: `EXTRA` state; `0003`: `inflateCopy()`; `0008`: `inflateSync()`.) Note: if `0009`/`0010` are fixed via `#2516`/`#2526`, those touch `inflateSetDictionary()` and `LEN` state (`inffast_tpl.h` guard), also disjoint. |
| `deflate.c` | `0006`, `0018`, `0019`, `deflate-reset-block-open` | **Completely disjoint regions; zero conflict.** (`0019`: `CLEAR_HASH()` macro near top; `0006`: `deflateBound_z()`; `deflate-reset-block-open`: `deflateResetKeep()`; `0018`: `fill_window()`.) |

### 2. Shared Test Files (EOF / Include Appends Only)

| Test File | Series Appending Tests | Eliminated Draft Conflicts |
| --- | --- | --- |
| `test/test_inflate_copy.cc` | `0003`, `0011` | `0007`'s tests were relocated to `test/test_inflate_far_distance.cc` and `test/test_inflate_back.cc` so `test_inflate_copy.cc` is touched only by copy/shared-header tests. |
| `test/test_gzseek.cc` | `0004`, `0020`, `0021` | `0004` tests moved out of `test_gzfile_api_errors.cc` into `test_gzseek.cc`; `0020` and `0021` also live here (`TEST` appends at EOF only). |
| `test/test_gzio.cc` | `0016`, `0017`, `0022` | `0017` and `0022` split cleanly; `0016` and `0022` share top-of-file `<fcntl.h>`/`<unistd.h>` includes. |
| `test/test_gzfile_api_errors.cc` | `0014`, `0015` | Only `0014` and `0015` append here; each test name is unique. |
| Unique test files (1 series each) | `0006` (`test_deflate_bound.cc`), `0007` (`test_inflate_far_distance.cc`, `test_inflate_back.cc`), `0008` (`test_inflate_sync.cc`), `0012` (`test_deflate.cc`), `0013` (`test_deflate_tune.cc`), `0018` (`test_deflate_cve.cc`), `0019` (`test_deflate_params.cc`), `deflate-reset-block-open` (`test_deflate_quick_block_open.cc`) | Moved `0012` out of `test_deflate_tune.cc` (avoided colliding with `0013`) and moved `0018` out of `test_deflate_quick_block_open.cc` (avoided colliding with `deflate-reset-block-open`). |

### 3. Overlap with Other Open Upstream `zlib-ng/zlib-ng` PRs

| Upstream PR | Author | Interaction with This Bundle |
| --- | --- | --- |
| [#2516](https://github.com/zlib-ng/zlib-ng/pull/2516) | `Dead2` | Covers `0009` (`inflateSetDictionary` NULL pointer checks + tests); do not submit a duplicate PR for `0009`. |
| [#2526](https://github.com/zlib-ng/zlib-ng/pull/2526) | `arfa-21` | Covers `0010` (`inflate_fast` with `>= 8` primed bits); do not submit a duplicate PR for `0010`. |
| [#2404](https://github.com/zlib-ng/zlib-ng/pull/2404) | `dfengliu` | Also modifies `inflateCopy()` (`state->next` bounds check) and `test/test_inflate_copy.cc`; rebase `#2524` (`0003`) / `#2528` (`0011`) trivially if `#2404` merges first. |
| [#2432](https://github.com/zlib-ng/zlib-ng/pull/2432) | `nmoinvaz` | Modifies `inffast_tpl.h` non-safe fast loop (two chunks per iteration); review `0007`'s non-safe `inffast_tpl.h` copy path against `#2432` depending on merge order. |
| [#2517](https://github.com/zlib-ng/zlib-ng/pull/2517) | `Dead2` | Appends `gz*` NULL-argument tests to `test/test_gzfile_api_errors.cc`; only EOF context rebase needed for `0014`/`0015`. |

### 4. Recommended Upstream Submission / Merge Order

1. **Update open PRs first**: `#2523` (`0006`), `#2525` (`0004` — should land before `0016` and `0017` so they reuse `GZ_OFF_MAX`), `#2527` (`0014`), `#2528` (`0011`); `#2524` (`0003`) is already ready.
2. **After `#2525` (`0004`)**: submit `0016` (`gz_room` read bound) and `0017` (`uint64_t` write bound), plus `0022` (`gz_zero` accounting).
3. **Sequential `gzread.c` pair**: submit `0020` (`gzdirect` pending skip) before `0021` (`gzgets` pending skip at EOF).
4. **Independent PRs (any order)**: `0007`, `0008`, `0012`, `0013`, `0015`, `0018`, `0019`, and `deflate-reset-block-open`.

---

## Verification Method & Sanitizer Builds

Important CMake notes when reproducing locally:
- Always configure sanitizer builds with **`-DCMAKE_BUILD_TYPE=None`** so `Release` optimization flags (`-O2` / `-DNDEBUG`) are not appended after custom sanitizer flags.
- Pass **`-fsanitize=address,pointer-compare,pointer-subtract,undefined`** on **`CMAKE_C_FLAGS` only** (keep `CMAKE_CXX_FLAGS` on `-fsanitize=address,undefined` because GoogleTest/libstdc++ headers trigger false positives under strict pointer-pair comparison), and export `ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0`.

Example verification builds:

```sh
# 1. Clang compat build with pointer-pair + ASan + UBSan
cmake -S . -B build-compat-san \
  -DCMAKE_BUILD_TYPE=None -DZLIB_COMPAT=ON -DWITH_OPTIM=OFF \
  -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF -DBUILD_SHARED_LIBS=OFF \
  -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS="-O0 -g -fsanitize=address,pointer-compare,pointer-subtract,undefined -fno-sanitize-recover=undefined" \
  -DCMAKE_CXX_FLAGS="-O0 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined"
cmake --build build-compat-san -j
ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0 ctest --test-dir build-compat-san --output-on-failure

# 2. Clang native build with architecture optimizations + ASan + UBSan
cmake -S . -B build-native-san \
  -DCMAKE_BUILD_TYPE=None -DZLIB_COMPAT=OFF -DWITH_OPTIM=ON -DBUILD_SHARED_LIBS=OFF \
  -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_FLAGS="-O0 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined" \
  -DCMAKE_CXX_FLAGS="-O0 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined"
cmake --build build-native-san -j
ctest --test-dir build-native-san --output-on-failure

# 3. GCC compat Release build with optimizations
cmake -S . -B build-gcc-rel \
  -DCMAKE_BUILD_TYPE=Release -DZLIB_COMPAT=ON -DWITH_OPTIM=ON -DBUILD_SHARED_LIBS=OFF \
  -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++
cmake --build build-gcc-rel -j
ctest --test-dir build-gcc-rel --output-on-failure
```

Every series in this bundle was verified independently after its latest revision on both `build-compat-san` and `build-native-san`, including reproducing failures on unpatched `5f1f4899` where runtime-observable (`0003`, `0004`, `0006`, `0007`, `0011`, `0013`–`0022`, `deflate-reset-block-open`), plus stacked full `ctest` verification (67/67 compat-san, 68/68 native-san, 67/67 gcc-rel, opt-in `0015`/`0018`, and stacked gzip suite `85 compat / 83 native` after splitting `0017`/`0022`).
