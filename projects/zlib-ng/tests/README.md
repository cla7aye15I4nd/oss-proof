# Differential tests: the Lean translation against the real C

The translation in `ZlibNgF/ZlibNg/*.lean` is trusted, not proved. This directory is the evidence that
it matches the C. For each translated function, the same inputs go to

* the **real zlib-ng**: the pinned `zlib-ng/` submodule plus `patches/*.patch` in name order, applied to
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
```

`run.sh` needs `cc`, `cmake`, `patch`, `nm`, `timeout`, `python3`, `tar` and `lake`. Variables:
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
| `compress` | `compress.c` | `compressBound` |
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

| Case | Patch | Defect shown without the patch |
| --- | --- | --- |
| `inflate-copy-pointer-equality` | 0003 | invalid pointer pair in `inflateCopy` |
| `gzseek-offset-overflow` | 0004 | signed overflow in `gzseek64` |
| `deflatebound-gzip-extra-length` | 0006 | `deflateBound` too small for a gzip extra field with `extra_len > 0xffff` |
| `inflate-window-copy` | 0007 | invalid pointer pair (window vs output) in `chunkcopy_safe` |
| `infback-window-overlap` | 0007 | none: upstream is clean here; the case checks that `inflateBack`, whose output is the window, decodes matches into the previous window pass alike with and without the patch |
| `inflatesync-null-next-in` | 0008 | none observable: `NULL + 0` is not reported by any sanitizer; the case checks the calls run alike |
| `inflatesetdictionary-null` | 0009 | `inflateSetDictionary(strm, NULL, 0)` returns `Z_OK` instead of `Z_STREAM_ERROR` |
| `inflate-fast-primed-bits` | 0010 | after `inflatePrime`, `inflate` returns with `avail_in` larger than the caller gave (`next_in` before the buffer) |
| `longest-match-offset-base` | 0012 | none observable: forming `window - match_offset` is not reported by any sanitizer; the case checks that level 9 `deflate` gives the same output with and without the patch |
| `deflate-medium-insert-count` | 0013 | division by zero in `insert_knuth_stepped` after `deflateTune` with `max_lazy = INT_MIN` (level 4) |
| `gzwrite-clearerr-stale-input` | 0014 | invalid pointer pair (heap buffer overflow without the pair check) in `gz_write` after a failed direct `gzwrite` and `gzclearerr` |
| `gzclose-after-failed-write` | 0014 | heap use after free: `gzclose` writes from the caller's freed buffer after a failed direct `gzwrite` |
| `gzbuffer-alloc-null-offset` | 0015 | `NULL` plus an offset in `gz_buffer_alloc` when the allocation fails (clang's UBSan; GCC's does not report it, and the case then checks that the calls run alike) |
| `gzread-position-overflow` | 0016 | signed overflow of `x.pos` in `gz_read` after `gzseek` to `INT64_MAX` on a descriptor that keeps delivering data |
| `fixed-block-start-overflow` | 0018 | signed overflow of `block_start` in `fill_window` after `2^31` bytes of one `Z_FIXED` level-1 stream (about 20 s) |
| `deflate-slow-match-start` | 0019 | level 8 `deflate_slow` takes a match at or after `strstart` (levels 5 then 8 after `Z_FULL_FLUSH`): the wrapped distance makes `d_code` read far outside `dist_code` (AddressSanitizer), and without a sanitizer the stream decodes to wrong data |
| `gzdirect-pending-skip` | 0020 | `gzseek` to `INT64_MAX`, `gzdirect`, `gzgetc`, `gztell` on a file that is not gzip: signed overflow of `x.pos + skip` in `gztell64` |
| `gzwrite-zero-retry` | 0022 | on a transparent writer whose descriptor is a full non-blocking pipe: `gzseek` to `INT64_MAX`, a failed `gzwrite`, `gztell`: signed overflow of `x.pos + skip` in `gztell64` (run `max`); `gzseek` to 10000, a failed `gzwrite`, the pipe drained, `gzclearerr`, `gzwrite` again: 14099 bytes in the file and `gztell` 14099 instead of 10003 (run `retry`) |

Every case above uses documented calls only (**public API**); none sets the library's internal state itself
(**white-box**). Their failures and devices come from ordinary descriptors, or, for `gzread-position-overflow` on a
host that is not Linux, from an `lseek` that answers as Linux's `/dev/zero` does.

Patch 0017 (the writers' position) has no case here: its defect needs `2^31 + 1` failing `gzfwrite` calls of
`2^32 - 1` bytes, each followed by `gzclearerr` (about 7 minutes with UndefinedBehaviorSanitizer alone, more under
AddressSanitizer). It was shown through documented calls only (public API) on the real C (findings page); the `gz`
differential test covers the refusal it adds (`gzfwrite` lengths above `GZ_OFF_MAX`, refused before the buffer is
read).

32-bit guards: `gzwrite-position-32bit` builds the source with `-m32 -D_FILE_OFFSET_BITS=64` (32-bit `size_t`, 64-bit
file offsets) and writes one byte at position `2^32 - 1` (documented calls only: `gzdopen` of `/dev/null` for
transparent writing, `gzbuffer`, `gzseek`, `gzwrite`, `gztell`, `gzerror`). With every current patch the write
succeeds; with the first version of patch 0017 (`first-0017.patch` there, which converted the room left to `size_t`)
it must still be refused with `Z_DATA_ERROR`. The case also runs on the verified LP64 build, where the write succeeds.
It needs a compiler and C library for `-m32` (on x86_64 Linux, `gcc-multilib`, which the CI job installs); without
one it is skipped with a `SKIPPED` line, and when `CI` is set a missing `-m32` toolchain fails the run.

Plain regression tests (defects of 2.3.3 that the `develop` branch fixes; each must pass on the verified
source without a sanitizer report): `adler32-null-len-1`, `crc32-combine-negative-len-hang` (the
`g` and `c` runs), `gzbuffer-aligned-alloc-overflow`.

Open defects (defects of the verified source with no patch yet: undefined behaviour, or a wrong result with no
memory error; each must still show its report or wrong result, and the run fails once it stops reproducing):
`deflatereset-fixed-block-open` (`deflateReset` while a `Z_FIXED` level-1 static block is open: the next stream
continues the block without its header, and `inflate` rejects it with `Z_DATA_ERROR`).

Guards (an earlier, defective version of one of our patches, built in place of the current one; the case's
reproduction must still show its defect there): `infback-window-overlap` with `first-0007.patch`, the first
version of patch 0007, whose `memcpy` copies overlapping ranges when the output is the window
(`memcpy-param-overlap`).

Open defects in the differential test: `expected-faults.txt` lists the generated inputs on which the verified C
source has undefined behaviour with no patch yet (see the findings page), so the translation faults there while the
C prints a result. `expected_faults.py` (called by `run.sh`) checks that the translation faults on each listed input
with the listed message and only then counts the line as agreeing; every other line is compared byte for byte. An
entry whose input is no longer generated, or on which the translation stops faulting, fails the run. The list is
empty: the translation and the C agree on every generated input.

Round trip: after the `deflate` comparison, `c_deflate roundtrip` inflates, with the real C `inflate`, every
output of the translation that is one whole stream of its input (a `deflate` call returned `Z_STREAM_END`; no
`deflatePrime`, reset, second dictionary or late raw dictionary in the script) and checks that it gives back
exactly the input bytes the stream consumed.

The reference C library is built for the target's gzip `OS_CODE` (3, as on Linux) on every host: `build-zlib-ng.sh`
removes the `__APPLE__` branch of `zutil.h` in the copy it builds, which the x86_64 Linux target never takes.
