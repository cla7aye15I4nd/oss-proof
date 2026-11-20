# Differential tests: the Lean translation against the real C

The translation in `ZlibNgF/ZlibNg/*.lean` is trusted, not proved. This directory is the evidence that
it matches the C. For each translated function, the same inputs go to

* the **real zlib-ng**: the pinned `zlib-ng/` submodule plus the library hunks (everything outside `test/`) of
  every `patches/NNNN-slug/upstream.patch` in directory name order (`apply-patches.sh --library-only`), applied to
  a **copy** (the submodule is never touched) and built as `libz.a` by `build-zlib-ng.sh` with the
  verified configuration
  `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`
  (the script rejects a library that contains Chorba or function-table symbols, and checks that
  `adler32.c` calls `adler32_c` and `crc32.c` calls `crc32_braid`);
* the **Lean translation**, called through the runtime (`C.run` on a heap built by
  `lean/DiffTest/Common.lean`).

The two outputs are compared byte for byte. This is a test, not a proof: it shows that the two agree on
the inputs tried, nothing more. The drivers import the translation modules themselves, never a copy,
and are not part of the checked library.

## Run

```bash
ZLIB_NG_SRC=$PWD/zlib-ng bash tests/run.sh          # from projects/zlib-ng
SAN=1 ZLIB_NG_SRC=$PWD/zlib-ng bash tests/run.sh    # C side under ASan + UBSan (what CI runs)
ZLIB_NG_SRC=$PWD/zlib-ng bash tests/regression/run.sh [case...]   # only the patch reproductions
ZLIB_NG_SRC=$PWD/zlib-ng bash tests/patch-gtest.sh [patch...]      # only the GoogleTest cases of the patches
```

`run.sh` needs `cc`, `cmake`, `git`, `nm`, `timeout`, `python3`, `tar` and `lake`. Variables:
`ZLIB_NG_SRC` (a zlib-ng checkout), `ZLIB_NG_BUILD` (reuse a copy made by `build-zlib-ng.sh`),
`ONLY=name` (one list entry, or `patches`), `SAN=1`. It exits 0 if all outputs are identical, 1 on the
first difference (it prints the input line and both results), 2 on a setup error. Everything it makes
is in `tests/build/` and `tests/.lake/`. A build directory records the patches, options and flags it was
made with (`BUILD_DIGEST`) and is rebuilt when they change.

## Drivers

| Name | C file | Functions |
| --- | --- | --- |
| `adler32` | `adler32.c`, `arch/generic/adler32_c.c` | `adler32`, `adler32_z`, `adler32_combine`, `adler32_combine64` |
| `crc32` | `crc32.c`, `arch/generic/crc32_braid_c.c`, `crc32_braid_comb.c` | `crc32`, `crc32_z`, `crc32_combine`, `crc32_combine64`, `crc32_combine_gen`, `crc32_combine_gen64`, `crc32_combine_op`, `get_crc_table` (all 256 entries) |
| `zutil` | `zutil.c` | `zlibVersion`, `zlibCompileFlags`, `zError`, `zcalloc` / `zcfree` (write, read back, free), `zng_alloc_aligned` / `zng_free_aligned` (NULL or not, alignment, write, read back, free) |
| `compress` | `compress.c` | `compressBound`, `compressBound_z` |
| `inflate` | `inflate.c`, `inftrees.c`, `inffast_tpl.h` / `chunkset_tpl.h` (`arch/generic/chunkset_c.c`), `inflate_p.h`, `uncompr.c` | `inflateInit2_`, `inflate` (every flush mode, input and output in pieces), `inflateSetDictionary` (on `Z_NEED_DICT`), `inflateGetHeader`, `inflateReset`, `inflateResetKeep`, `inflateReset2`, `inflateEnd`; zlib, gzip and raw streams of every block type, every `windowBits`, dictionaries, gzip headers, corrupted and truncated streams, window-crossing matches, distances 1..64. A line prints every call's return value, stream fields (`next_in` / `next_out` offsets, `avail_*`, `total_*`, `adler`, `data_type`, `msg`), the output bytes and the header fields and buffers. Call scripts on one stream: `inflatePrime`, `inflateSync`, `inflateSyncPoint`, `inflateCopy` mid-stream (then going on with the copy), `inflateGetDictionary`, `inflateSetDictionary` (also `NULL`, too early, too late), `inflateUndermine`, `inflateValidate`, `inflateMark`, `inflateCodesUsed`, resets and calls after `inflateEnd`. `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` with exact, short and empty output, `NULL` pointers and length cells, short, corrupted and trailing input. `inflateInit_` / `inflateInit2_` with wrong versions and structure sizes |
| `deflate` | `deflate.c`, `deflate_p.h`, `trees.c`, `trees_emit.h`, the strategies (`deflate_stored.c`, `deflate_quick.c`, `deflate_fast.c`, `deflate_medium.c` / `deflate_medium_tpl.h`, `deflate_slow.c`, `deflate_rle.c`, `deflate_huff.c`), `insert_string.c`, `arch/generic/compare256_c.c` (`match_tpl.h`), `arch/generic/slide_hash_c.c`, `compress.c` | `deflateInit2_` (also invalid parameters), then a script of calls on one stream: `deflate` (every flush mode and sequences of them, input and output in chunks down to one byte, zero-length calls, calls after `Z_STREAM_END` and after errors), `deflateParams` (level and strategy changes mid-stream), `deflateCopy` (going on with the copy), `deflatePrime`, `deflatePending`, `deflateUsed`, `deflateTune` (also `max_lazy` outside 0..258), `deflateSetDictionary` (also `NULL`, too late, longer than the window), `deflateGetDictionary`, `deflateSetHeader` (extra, name, comment, header CRC), `deflateBound` / `deflateBound_z`, `deflateReset`, `deflateResetKeep`, `deflateEnd`; every level and strategy, raw / zlib / gzip wrappers, every `windowBits` and `memLevel`, inputs around the window size and twice it, zero / random / text / repetitive / mixed data (generated by the same xorshift in both drivers). A line prints every call's return value and stream fields, the output bytes and the final `deflateEnd`. `compress`, `compress2`, `compress_z`, `compress2_z` with exact, short, zero and `NULL` destinations and length cells |
| `infback` | `infback.c` (with the parts of `inflate.c`, `inftrees.c`, `inffast_tpl.h` / `chunkset_tpl.h` it calls) | `inflateBackInit_`, `inflateBack`, `inflateBackEnd`: raw streams of every block type and hand-built fixed-code streams, every `windowBits` 8..15 with a window of exactly that size, input from `next_in` and from `in()` in chunks of 1 byte, odd sizes or all at once, `in()` running out early, `out()` failing at its first and later calls, corrupted and truncated streams, matches wrapping the window, matches into the previous pass of the window whose window copy overlaps its destination or is a copy onto itself (distance equal to the window size), two `inflateBack` calls on one state, init argument errors (`NULL` window, bad `windowBits`, version, `stream_size`), `NULL` and stateless streams. A line prints the return value, `next_in` (which buffer, offset), `avail_in`, `msg`, the number of `in()` calls, the length of every `out()` call and the bytes written. No generated input is filtered out |
| `gz` | `gzlib.c`, `gzread.c`, `gzwrite.c` (with the `inflate` and `deflate` code they call) | Every public gz* function, in scripts of operations on one handle (`tests/c/gz.c`, `gen/gz.py`): `gzopen` / `gzdopen` with every mode letter and invalid modes, reading gzip, concatenated, transparent, truncated and corrupted files through every reader, writing in every mode, level and strategy, `gzseek` / `gzrewind` / `gztell` / `gzoffset` in both modes (also to near `2^63`), `gzsetparams`, `gzflush`, `gzclearerr`, the `NULL` handle. The library's `open`, `read`, `write`, `lseek`, `close` and `strerror` are a file-system model shared with the Lean side, with a schedule of failures, short reads and writes, device data and `lseek` values; its `malloc` calls are numbered and the schedule can make any of them return `NULL` (`gz_state`, path, buffers, inflate and deflate state, error message). A line prints every call's result, the error state and the files' final contents |

## File formats

One test case per line, fields separated by one space. Blank lines are skipped.

| Field | Written as |
| --- | --- |
| function | its C name (`adler32_z`, ...) |
| unsigned integer | decimal |
| signed integer | decimal, optional `-` |
| buffer | `null:LEN` (a NULL pointer, passed with length LEN), `hex:DIGITS` (a non-NULL pointer to those bytes; empty digits give a valid pointer to zero bytes) or `off:K:DIGITS` (a pointer K bytes into a block whose last bytes are the digits: an unaligned buffer) |

The C side allocates every buffer with `malloc` of the exact size, so sanitizers see overreads. The
output has one line per input line. The Lean side prints `FAULT ...` if the translation raises
`Fault.ub` or `Fault.outOfFuel`; the C side cannot fault, so a fault is always a difference. Malformed
input prints `BADINPUT` and fails the run. Inputs that are undefined behaviour in C (a length larger
than the buffer) are not generated.

Types follow LP64: `uLong`, `z_size_t` are 64 bits, `uInt` 32, `z_off_t` and `z_off64_t` signed 64.

## Patch reproductions

`regression/run.sh` builds the source twice per case under ASan (with pointer-pair checks) and UBSan,
at `-O0`: with every patch but the case's own, and with every patch. The first must show the defect (the
named sanitizer report, or no return within the timeout), the second must run without a report and
print the expected result.

The evidence column labels what a case shows. **Public API**: the case makes documented calls only and the defect is
seen on the run (a sanitizer report, or a wrong result). **Letter of the standard**: the case makes documented calls
only, but no sanitizer reports the undefined behaviour and nothing misbehaves; the case then only checks that the
calls run alike with and without the patch, and the defect rests on the wording of ISO C17 (and, for the findings, on a
traced run). **White-box**: a test that sets the library's internal state itself. No case here is white-box: none
includes an internal header or touches `strm->state` or the `gz_state`; failures and devices come from ordinary
descriptors, or, for `gzread-position-overflow` on a host that is not Linux, from an `lseek` that answers as Linux's
`/dev/zero` does. A sanitizer report of the pointer-pair check (0001, 0004) is a report of undefined behaviour by the
letter of the standard that misbehaves on no flat-memory target.

| Case | Patch | Defect shown without the patch | Evidence |
| --- | --- | --- | --- |
| `inflate-copy-pointer-equality` | 0001 | invalid pointer pair in `inflateCopy` | public API (pointer-pair check) |
| `gzseek-offset-overflow` | 0002 | signed overflow in `gzseek64`: `offset + skip` with `SEEK_CUR` (run `cur`), `offset - x.pos` after `gzungetc` at position 0 (`set`), `x.pos + offset` in the test of the raw area (`pos`, on `/dev/zero`, its `lseek` answered as Linux's on other hosts); the `lseek` offset `offset - x.have` (run `lseek` of the repro, not run here: with patch 0013 in the build `x.pos + x.have <= GZ_OFF_MAX` rules it out) | public API; the `x.next + 0` that 0002 also removes is letter of the standard and not shown |
| `gzseek-refusal-state` | 0002 | none (a change of behaviour): with the patch a refused seek leaves the position unchanged, as zlib documents; without it a refused `SEEK_CUR` before the start on a reader and on a writer drops the pending skip, and a `SEEK_SET` to a negative offset after two `gzungetc` at position 0 (gzip file and plain file) is sought instead of refused (each run prints a different line) | public API (no defect: different documented results) |
| `deflatebound-gzip-extra-length` | 0003 | `deflateBound` too small for a gzip extra field with `extra_len > 0xffff` | public API (wrong result) |
| `inflate-window-copy` | 0004 | invalid pointer pair (window vs output) in `chunkcopy_safe` | public API (pointer-pair check) |
| `infback-window-overlap` | 0004 | none: upstream is clean here; the case checks that `inflateBack`, whose output is the window, decodes matches into the previous window pass alike with and without the patch | public API (no defect: same results) |
| `inflatesync-null-next-in` | 0005 | none observable: `NULL + 0` is not reported by any sanitizer; the case checks the calls run alike | letter of the standard |
| `inflatesetdictionary-null` | 0006 | `memcpy` from `NULL` (UBSan, where the C library declares `memcpy`'s arguments nonnull, as glibc does) or `inflateSetDictionary(strm, NULL, 0)` returning `Z_OK` instead of `Z_STREAM_ERROR` | public API (UBSan with GCC and clang on glibc; wrong result elsewhere) |
| `inflate-fast-primed-bits` | 0007 | after `inflatePrime`, `inflate` returns with `avail_in` larger than the caller gave (`next_in` before the buffer) | public API (wrong result) |
| `inflate-shared-header-extra` | 0008 | heap buffer overflow in `inflate` (state `EXTRA`) when two streams share one `gz_header` | public API |
| `longest-match-offset-base` | 0009 | none observable: forming `window - match_offset` is not reported by any sanitizer; the case checks that level 9 `deflate` gives the same output with and without the patch | letter of the standard |
| `deflate-medium-insert-count` | 0010 | division by zero in `insert_knuth_stepped` after `deflateTune` with `max_lazy = INT_MIN` (level 4) | public API |
| `gzwrite-clearerr-stale-input` | 0011 | invalid pointer pair (heap buffer overflow without the pair check) in `gz_write` after a failed direct `gzwrite` and `gzclearerr` | public API |
| `gzclose-after-failed-write` | 0011 | heap use after free: `gzclose` writes from the caller's freed buffer after a failed direct `gzwrite` | public API |
| `gzbuffer-alloc-null-offset` | 0012 | `NULL` plus an offset in `gz_buffer_alloc` when the allocation fails: clang's UBSan only (see below) | public API (clang only) |
| `gzread-position-overflow` | 0013 | signed overflow of `x.pos` in `gz_read` after `gzseek` to `INT64_MAX` on a descriptor that keeps delivering data | public API |
| `gzgetc-macro-position` | 0013 | the `gzgetc()` macro of `zlib.h` in the caller: `gzseek` to `INT64_MAX - 2` and `gzread` of 4 bytes, then the macro (run `max`; without the patch `gz_read` itself overflows); `gzseek` to `INT64_MAX - 12`, `gzread` of 1 byte, then the macro 12 times (run `near`): signed overflow of `x.pos` in the caller's code; the first version of 0013 is kept as a guard | public API |
| `fixed-block-start-overflow` | 0015 | signed overflow of `block_start` in `fill_window` after `2^31` bytes of one `Z_FIXED` level-1 stream (about 20 s) | public API |
| `deflate-slow-match-start` | 0016 | level 8 `deflate_slow` takes a match at or after `strstart` (levels 5 then 8 after `Z_FULL_FLUSH`): the wrapped distance makes `d_code` read far outside `dist_code` (AddressSanitizer), and without a sanitizer the stream decodes to wrong data | public API |
| `gzdirect-pending-skip` | 0017 | `gzseek` to `INT64_MAX`, `gzdirect`, `gzgetc`, `gztell` on a file that is not gzip: signed overflow of `x.pos + skip` in `gztell64` | public API |
| `gzgets-pending-skip` | 0018 | `gzseek` to `INT64_MAX` and `gzdirect` on a file of 3 bytes that is not gzip, the file grows, then `gzgets` and `gztell`: signed overflow of `x.pos + skip` in `gztell64` | public API (the file grows between two calls) |
| `gzwrite-zero-retry` | 0019 | on a transparent writer whose descriptor is a full non-blocking pipe: `gzseek` to `INT64_MAX`, a failed `gzwrite`, `gztell`: signed overflow of `x.pos + skip` in `gztell64` (run `max`); `gzseek` to 10000, a failed `gzwrite`, the pipe drained, `gzclearerr`, `gzwrite` again: 14099 bytes in the file and `gztell` 14099 instead of 10003 (run `retry`) | public API |
| `gzprintf-failed-write-drift` | 0021 | on a writer (`"wb0"`, 262144-byte buffer) whose descriptor is a non-blocking pipe with the room set before each call: `gzprintf` rounds whose writes fail, with `gzclearerr` between, move `next_in + avail_in` past the input half of the buffer; the last `gzprintf` writes past the buffer block (AddressSanitizer heap buffer overflow, or a wild write at `gzwrite.c:389`, run `oob`); stopping before it and closing, the gzip stream does not inflate (run `corrupt`). On a host that is not Linux, `write()` on that descriptor is answered as a Linux pipe of 1 MiB answers it | public API on Linux |
| `deflatereset-fixed-block-open` | 0022 | `deflateReset` while a `Z_FIXED` level-1 static block is open: the next stream continues the block without its header, and `inflate` rejects it with `Z_DATA_ERROR` | public API (wrong result) |

`gzbuffer-alloc-null-offset` (0012) shows its defect only with clang: GCC's UndefinedBehaviorSanitizer does not
report `NULL` plus an offset, so a GCC build without the patch prints the patched result and shows nothing. The case
runs on the default compiler's builds, where a GCC run prints a `NOT SHOWN` line instead of passing as a
reproduction, and then on two builds made with clang, where the build without 0012 must report the offset. Without
clang that part prints a `SKIPPED` line (and the final line names the case); when `CI` is set a missing clang fails
the run. The CI job installs clang.

Patch 0014 (the writers' position) has no case here: its defect needs `2^31 + 1` failing `gzfwrite` calls of
`2^32 - 1` bytes, each followed by `gzclearerr` (about 7 minutes with UndefinedBehaviorSanitizer alone, more under
AddressSanitizer). It was shown through documented calls only (public API) on the real C (findings page); the `gz`
differential test covers the refusal it adds (`gzfwrite` lengths above `GZ_OFF_MAX`, refused before the buffer is
read).

Patch 0020 (`gzungetc`'s position) has no case here either: no run of documented calls can tell the patched build
from the unpatched one in reasonable time. The cycle that lowers `x.pos` (push until the buffer is full, the failed
push, `gzclearerr`) is the same in both (the patch acts only at its bound), and the bound is reached only after about `2^63` pushes. The mechanism
was shown once on the real C (findings page); the `gz` differential test covers `gzungetc` below the bound, where
the patch changes nothing.

32-bit guards: `gzwrite-position-32bit` builds the source with `-m32 -D_FILE_OFFSET_BITS=64` (32-bit `size_t`, 64-bit
file offsets) and writes one byte at position `2^32 - 1` (documented calls only: `gzdopen` of `/dev/null` for
transparent writing, `gzbuffer`, `gzseek`, `gzwrite`, `gztell`, `gzerror`). With every current patch the write
succeeds; with the first version of patch 0014 (`first-0014.patch` there, which converted the room left to `size_t`)
it must still be refused with `Z_DATA_ERROR`. The case also runs on the verified LP64 build, where the write succeeds.
`gzread-position-32bit` builds the source with `-m32 -D_LARGEFILE64_SOURCE=0` (a 32-bit `z_off64_t`, as `zconf.h` gives
without large-file functions) and reads at `GZ_OFF_MAX - 4` with `gzfread` of `2^31` one-byte items (documented calls;
the caller points the descriptor at `/dev/null` with `dup2` so that no more data comes): with every current patch 4 bytes
and `Z_DATA_ERROR` at `GZ_OFF_MAX`; with the first version of 0013 (`first-0013.patch` there, which converted the count
to `z_off64_t`) `x.pos` must still wrap. It needs a compiler and C library for `-m32` (on x86_64 Linux, `gcc-multilib`, which the CI job installs); without
one it is skipped with a `SKIPPED` line, and when `CI` is set a missing `-m32` toolchain fails the run.

Plain regression tests (defects of 2.3.3 that the `develop` branch fixes; each must pass on the verified
source without a sanitizer report): `adler32-null-len-1`, `crc32-combine-negative-len-hang` (the
`g` and `c` runs), `gzbuffer-aligned-alloc-overflow`.

Open defects (defects of the verified source with no patch yet: undefined behaviour, or a wrong result with no
memory error; each must still show its report or wrong result, and the run fails once it stops reproducing): none at
present.

Guards (an earlier, defective version of one of our patches, built in place of the current one; the case's
reproduction must still show its defect there): `infback-window-overlap` with `first-0004.patch`, the first
version of patch 0004, whose `memcpy` copies overlapping ranges when the output is the window
(`memcpy-param-overlap`); `gzgetc-macro-position` with `first-0013.patch`, the first version of patch 0013, which left
output buffered past `GZ_OFF_MAX` (the macro overflows in both runs).

## Library source across the patch layout change

`patch-source-identity.sh <rev> [expected-diff]` builds the library part of the verified source (everything outside
`test/`) twice on the pinned submodule: from the flat `patches/*.patch` of an earlier commit `<rev>`, and from the
current series (`apply-patches.sh --library-only`), and prints `diff -r` of the two. Against the last commit with flat
patches, the expected difference is `patch-source-identity.expected`: three comments, from the series `0006`, `0008`
and `0015` in the form proposed upstream, and the `(z_size_t)` cast that `0003` drops in `deflateBound` (upstream
review asked for it; the value is the same), and the new fix `0022` (`s->block_open = 0;` in `deflateResetKeep`, added
after the layout change); no other statement differs.

## GoogleTest cases of the patches

Each patch series (`../patches/NNNN-slug/upstream.patch`) may add or change GoogleTest cases in upstream's `test/`
suite. `patch-gtest.sh` runs the ones that `../patches/NNNN-slug/gtest.txt` lists, one per line:
`<gtest filter> <fails without this patch: yes|no> [VAR=value ...]` (the variables are set for that run, e.g. to
enable an opt-in upstream test). It builds upstream's `gtest_zlib` with upstream's CMake, the verified option set and
`CMAKE_BUILD_TYPE=None`, under ASan + UBSan at `-O0` (pointer-pair checks on the C code only, as GoogleTest's own
headers trip them; `ASAN_OPTIONS=detect_invalid_pointer_pairs=2:detect_leaks=0`), first with every series applied in
full: each listed filter must run at least one test, skip none and pass without a report. Then, for every patch with a
`yes` line, it builds the same source without that patch's library hunks (its test hunks stay) and each `yes` filter
must fail there (a failed assertion or a sanitizer report). GoogleTest is v1.16.0, the release upstream's
`test/CMakeLists.txt` asks for, pinned by commit in the script and fetched once into `tests/build/patch-gtest/`
(`GTEST_SRC=<checkout>` uses a local copy); the builds themselves are offline. Variables: `ZLIB_NG_SRC`, `WORK`,
`CC`/`CXX` (default `clang`/`clang++`), `JOBS`. A patch whose series has tests gets a `gtest.txt`; `run.sh` runs
`patch-gtest.sh` after the reproductions.

Open defects in the differential test: `expected-faults.txt` lists the generated inputs on which the verified C
source has undefined behaviour with no patch yet (see the findings page), so the translation faults there while the
C prints a result. `expected_faults.py` (called by `run.sh`) checks that the translation faults on each listed input
with the listed message and only then counts the line as agreeing; every other line is compared byte for byte. An
entry whose input is no longer generated, or on which the translation stops faulting, fails the run. The list is
empty: the translation and the C agree on every generated input.

Round trip: after the `deflate` comparison, `c_deflate roundtrip` inflates, with the real C `inflate`, every
output of the translation that is one whole stream of its input (a `deflate` call returned `Z_STREAM_END`; no
`deflatePrime`, `deflateResetKeep`, second dictionary or late raw dictionary in the script) and checks that it gives
back exactly the input bytes the stream consumed. When the script calls `deflateReset`, the stream checked is the one
after the last reset: the output from `next_out` at the reset, against the input from `next_in` at the reset.

The reference C library is built for the target's gzip `OS_CODE` (3, as on Linux) on every host: `build-zlib-ng.sh`
removes the `__APPLE__` branch of `zutil.h` in the copy it builds, which the x86_64 Linux target never takes.
