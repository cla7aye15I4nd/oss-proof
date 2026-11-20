# Working rules (`projects/zlib-ng`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined
Behaviour Policy** (no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object
pointer subtraction or comparison, and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling
pointers). On any shared rule the root `AGENTS.md` is authoritative.

Goal: kernel-checked Lean 4 proofs about a faithful translation of zlib-ng at the pinned commit of its `develop` branch
(`zlib-ng/` submodule), built as the `ZLIB_COMPAT` x86_64 Linux LP64 static library with
`-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF` (other
options at their defaults). With these options there is no SIMD code and no function table: every
`FUNCTABLE_CALL(name)` is a direct call to the generic C function (`adler32` -> `adler32_c`, `crc32` ->
`crc32_braid`). `WITH_OPTIM=OFF` alone is not enough: with run-time detection off, the default
`WITH_CRC32_CHORBA=ON` makes `crc32` call `crc32_chorba`. `tests/build-zlib-ng.sh` holds the option set
and rejects a library that contains Chorba or function-table symbols. The goal is safety (no
undefined behaviour, no memory error, termination) of every public function of `zlib.h`, plus the
functional theorems stated in `ZlibNgF/Spec/Functional/`.

Read `docs/en/overview.md` first. State the status only in `docs/{en,zh}/progress.md`, as done or
not done.

## Source

- `zlib-ng/` is the upstream submodule (`https://github.com/zlib-ng/zlib-ng`, branch `develop`, commit
  `e591472c`). Never
  modify it. The verified source is `zlib-ng/` plus every `patches/NNNN-slug/upstream.patch` (one
  directory per fix, numbered from 0001; library and test hunks) applied in full with `git apply` in directory
  name order (`tests/apply-patches.sh`); `patches/README.md` is the index and lists exactly the directories.
- Translations mirror the C layout: `zlib-ng/X.c` is `ZlibNgF/ZlibNg/X.c.lean`, `zlib-ng/X.h` is
  `ZlibNgF/ZlibNg/X.h.lean`, and `zlib-ng/arch/generic/X.c` is
  `ZlibNgF/ZlibNg/arch/generic/X.c.lean`. Each function keeps its C name, and its docstring starts
  with the C signature.
- Specifications live in `ZlibNgF/Spec/{Common,Safety,Functional}/`; proofs of public goals in
  `ZlibNgF/Proof/public-<name>.lean`; heap-free mathematics in `ZlibNgF/Math/`; the runtime in
  `ZlibNgF/Runtime/`.
- `ZlibNgF/Results.lean` pairs every goal with its theorem or lists it as not done.

## Model notes

- Static tables (`crc_table`, `x2n_table`) live in the heap and are read-only; the goals that read
  them take `CrcGlobals h`, which says they hold the constants of `crc32_braid_tbl.h`.
- Pointer-to-integer conversions (`(uintptr_t)buf`) use `Heap.baseAddr`, and every theorem holds
  for every `baseAddr` oracle.
- The braided CRC kernel reads `z_word_t` words as eight byte loads. The model does not check the
  effective-type rule (ISO C17 §6.5p7) for these word reads.

- Inflate objects (`Runtime/Inflate.lean`, trusted base): a caller's `z_stream` / `gz_header` is a typed object of
  `Heap.streams` / `Heap.gzheaders`. The block that `alloc_inflate` gets from `zalloc` is a byte block; the casts
  `(inflate_allocs *)(buff + alloc_pos)` and `(inflate_state *)(buff + state_pos)` are the carve primitives
  `carveAllocs` / `carveState`, which fault (`Fault.ub`) unless the region fits in the plain bytes of the live
  block, the address is aligned for the type (`Heap.baseAddr`, as `Ptr.castAligned`), and the block holds no
  object of that type yet; they cut the byte array at the start of the region, so the carved regions are
  disjoint and a byte access into them faults. Their pointer fields start `Ival.uninit` (reading one faults) and
  their integers come from `Heap.garbage`. A carved object lives as long as its block. Trusted: the sizes and
  alignments `SIZEOF_INFLATE_STATE = 9152`, `ALIGNOF_INFLATE_STATE = 64`, `SIZEOF_INFLATE_ALLOCS = 32`,
  `SIZEOF_Z_STREAM = 112` (measured on the built configuration; LP64 layout); that the C accesses a carved object
  only through a pointer to its type (true of the translated code; `inflateCopy`'s `memcpy` of a whole
  `inflate_state` is a record copy, `copyState`); the static `lenfix` / `distfix` tables
  (`Runtime/InffixedTbl.lean`, copied from `inffixed_tbl.h` by a script). Only the default allocator is modelled:
  `zalloc` / `zfree` are `FnPtr.zcalloc` / `FnPtr.zcfree`; calling another function pointer faults.

## Inflate scope (pinned `develop` commit, verified option set)

Evidence: `nm` of the `libz.a` built by `tests/build-zlib-ng.sh` (symbols of `inflate.c.o`, `inftrees.c.o`,
`chunkset_c.c.o`, `uncompr.c.o`) and the preprocessor conditions of the files below. `infback.c`
(`inflateBack*`) has its own section below.

- Public entry points (`inflate.c`): `inflateInit_`, `inflateInit2_` (both call the hidden `inflateInit2`
  after `CHECK_VER_STSIZE`), `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateResetKeep`,
  `inflatePrime`, `inflateSetDictionary`, `inflateGetDictionary`, `inflateGetHeader`, `inflateSync`,
  `inflateSyncPoint`, `inflateCopy` (with patch 0001), `inflateUndermine` (returns `Z_DATA_ERROR`:
  `INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR` is off), `inflateValidate`, `inflateMark`, `inflateCodesUsed`;
  `uncompr.c`: `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z`.
- Internal functions of `inflate.c`: `inflateStateCheck`, `alloc_inflate`, `free_inflate` (one `zalloc`
  call of `PAD_64(window + state + allocs + 63)` bytes, carved into the window of `(1 << MAX_WBITS) + 64`
  bytes, the `inflate_state` and the `inflate_allocs` record; `free_inflate` frees `buf_start` through the
  saved `zfree`), `fixedtables` (points `lencode`/`distcode` at the static `lenfix`/`distfix` of
  `inffixed_tbl.h`), `updatewindow`, `syncsearch`, `inf_chksum`, `inf_chksum_cpy`. Macros of
  `inflate_p.h`: `LOAD`, `RESTORE`, `PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS`, `INITBITS`,
  `SET_BAD`, `CRC2`/`CRC4` (header CRC through the static `crc_table` of `crc32_braid_tbl.h`, included by
  `inflate_p.h`), `REFILL`, `CODE_BITS`, `CODE_EXTRA`, `EXTRA_BITS`, `COMBINE_OP`, `COMBINE_BITS`, and the
  static functions `load_64_bits` and `chunkcopy_safe`. `bits_t` is `uint8_t` on x86_64 (`ARCH_X86`), `unsigned`
  elsewhere.
- `inftrees.c`: `zng_inflate_table` and `count_lengths`, with the static `lbase`/`lext`/`dbase`/`dext`;
  `ENOUGH = ENOUGH_LENS + ENOUGH_DISTS = 1332 + 592`.
- Function table, resolved at compile time (`DISABLE_RUNTIME_CPU_DETECTION`, generic fallbacks of
  `arch/generic/generic_functions.h`): `FUNCTABLE_CALL(inflate_fast)` = `inflate_fast_c` (called from the
  `LEN` state when `have >= 15` and `left >= 260`), `inflate_fast_safe` = `inflate_fast_safe_c` (`3 <= left <
  260`), `chunkmemset_safe` = `chunkmemset_safe_c`, `adler32` = `adler32_c`, `adler32_copy` = `adler32_copy_c`,
  `crc32` = `crc32_braid`, `crc32_copy` = `crc32_copy_braid`; `crc32_small` (`crc32.c`) is called directly for
  gzip header fields. There are no fold variants in this build.
- `arch/generic/chunkset_c.c` instantiates `chunkset_tpl.h` (`chunk_t = uint64_t`, `CHUNKCOPY` = `chunkcopy_c`,
  `CHUNKMEMSET` = `chunkmemset_c`, `CHUNKMEMSET_SAFE` = `chunkmemset_safe_c`, `CHUNKUNROLL`, `CHUNKCOPY_SAFE`,
  `GET_CHUNK_MAG`, `HAVE_CHUNKMEMSET_4`/`_8`, loads and stores through `zng_memread_8`/`zng_memwrite_8` of
  `zmemory.h`, i.e. `memcpy`) and `inffast_tpl.h` twice (`inflate_fast_c`; `inflate_fast_safe_c` with
  `USE_SAFE_MODE`). `OPTIMAL_CMP` is 64 on x86_64, so the alignment prologue of `CHUNKMEMSET_SAFE` is not
  compiled.
- Allocation: `inflateInit2` installs `zcalloc`/`zcfree` when `zalloc`/`zfree` are `NULL`; all inflate memory is
  the single block of `alloc_inflate`. The model has to place typed objects (`inflate_state`, `inflate_allocs`,
  the window bytes) inside one `char` block obtained from `zalloc`, and carry the function pointers `zalloc` /
  `zfree` and the static code tables as pointer targets; the runtime of this project does not support that yet.
- Undefined behaviour of upstream reached by documented calls, fixed by patches 0004-0007 (see the findings page): pointer
  comparison and subtraction between the window and the caller's output in `chunkcopy_safe`
  (`inflate_p.h:224-225`, from `inflate.c:1100`), `CHUNKCOPY_SAFE` (`chunkset_tpl.h:319`) and `chunkmemset_c`
  (`chunkset_tpl.h:119`, `125`) from `inflate_fast_c` (`inffast_tpl.h:269`); `strm->next_in += 0` on a null
  `next_in` in `inflateSync` after `inflatePrime`; `NULL + 0` and `memcpy` from `NULL` in `updatewindow` from
  `inflateSetDictionary(strm, NULL, 0)` on a raw stream; `in -= len` at the end of `inflate_fast`
  (`inffast_tpl.h:327`) moving `next_in` before the caller's buffer when `inflatePrime` left 8 or more bits in
  the bit buffer on entry. Patch 0008 bounds the copy into `head->extra` in state `EXTRA`, which overran the buffer
  when two streams share one `gz_header`.

## Deflate scope (pinned `develop` commit, verified option set)

Evidence: `nm` of the `libz.a` built by `tests/build-zlib-ng.sh` (symbols of `deflate*.c.o`, `trees.c.o`,
`insert_string.c.o`, `compare256_c.c.o`, `slide_hash_c.c.o`, `compress.c.o`) and the preprocessor conditions of the
files below (`OPTIMAL_CMP` is 64 on x86_64; no `NO_QUICK_STRATEGY`, `NO_MEDIUM_STRATEGY`, `S390_DFLTCC_DEFLATE`,
`ZLIB_DEBUG`; `HASH_SIZE` 65536; `GZIP` defined).

- Public entry points (`deflate.c`): `deflateInit_`, `deflateInit2_` (both call the hidden `deflateInit2`), `deflate`,
  `deflateEnd`, `deflateSetDictionary`, `deflateGetDictionary`, `deflateCopy`, `deflateReset`, `deflateResetKeep`,
  `deflateParams`, `deflateTune`, `deflateBound`, `deflateBound_z` (patch 0003), `deflatePending`, `deflateUsed`,
  `deflatePrime`, `deflateSetHeader`; `compress.c`: `compress`, `compress2`, `compress_z`, `compress2_z`,
  `compressBound`, `compressBound_z`. `zng_deflateSetParams` / `zng_deflateGetParams` are not compiled
  (`ZLIB_COMPAT`).
- Internal functions of `deflate.c`: `alloc_deflate` (one `zalloc` of `PAD_64(window + prev + head + pending + state
  + allocs + 63)` bytes, aligned up to 64 and carved in that order: the window of `W_BUF_SIZE(w) = MAX(2 * w, 32768)`
  bytes, `prev` (`w` `Pos`), `head` (65536 `Pos`), `pending_buf` of `4 * lit_bufsize + 1 + 8` bytes with `sym_buf` at
  `pending_buf + lit_bufsize + 8`, the `deflate_state` (5440 bytes, `ALIGNED_(64)`) and the `deflate_allocs` record
  (56 bytes); `prev` is zeroed), `free_deflate`, `deflateStateCheck`, `deflateHeaders`, `lm_set_level`, `lm_init`,
  `fill_window`, `flush_pending`. `configuration_table`: level 0 `deflate_stored`, 1 `deflate_quick`, 2
  `deflate_fast`, 3-4 `deflate_medium`, 5-6 `deflate_medium_fizzle`, 7-9 `deflate_slow`; `deflate` calls
  `deflate_stored` for level 0, `deflate_huff` for `Z_HUFFMAN_ONLY`, `deflate_rle` for `Z_RLE`, else the table entry.
  `lm_set_level` stores `longest_match_slow_roll_c` / `insert_roll_batch` for level 9 (`MIN_ROLL_LEVEL`),
  `longest_match_slow_knuth_c` and `insert_knuth_batch_head` (level 1) or `insert_knuth_batch` otherwise.
- `deflate_p.h` (`zng_tr_tally_lit` / `_dist` with 4-byte `sym_buf` stores, `flush_pending_inline`, `bi_reverse`,
  `read_buf` with `crc32_copy_braid` / `adler32_copy_c`, `max_match_continues`, `FLUSH_BLOCK*`), `trees.c` (radix
  `build_tree` over `pq_leaves` / `pq_scratch`, `compress_block` with the `OPTIMAL_CMP >= 64` symbol reads),
  `trees_emit.h`, `trees_tbl.h` (static trees and code tables, runtime `Runtime/TreesTbl.lean`), the strategies
  `deflate_stored.c`, `deflate_quick.c`, `deflate_fast.c`, `deflate_medium.c` (`deflate_medium_tpl.h` twice),
  `deflate_slow.c`, `deflate_rle.c` (`compare256_rle_64`), `deflate_huff.c`; `insert_string.c` with
  `insert_string_p.h`; `arch/generic/compare256_c.c` (`compare256_64`, `compare256_8`, `compare256_c` =
  `compare256_64_static`, and `match_tpl.h` three times: `longest_match_c` for levels 2-6 through
  `FUNCTABLE_CALL(longest_match)`, `longest_match_slow_knuth_c`, `longest_match_slow_roll_c`); `slide_hash_c` /
  `slide_hash_head_c` of `arch/generic/slide_hash_c.c`.
- Translation layout: `fill_window` is `ZlibNgF/ZlibNg/deflate.c.fill_window.lean` (the strategies call it and
  `deflate.c` calls the strategies), `flush_pending` sits next to `flush_pending_inline` in `deflate_p.h.lean`,
  `bi_reverse` in `trees.c.lean`, the size macros of `zutil.h` in `zutil.h.lean`.
- Deflate objects (`Runtime/Deflate.lean`, trusted base): the `deflate_state` and `deflate_allocs` are carved from the
  `zalloc` block like the inflate objects (`carveDState`, `carveDAllocs`, measured sizes `SIZEOF_DEFLATE_STATE`,
  `SIZEOF_DEFLATE_ALLOCS`); the window, `prev`, `head` and `pending_buf` stay plain bytes of the block (one object in
  C, so pointer arithmetic is bounded by the block), `Pos` elements are two-byte accesses; the trees, `bl_count` and
  `pq_*` arrays are fields of the state record with their own `Space` instances. `deflateCopy`'s `memcpy` of a whole
  `deflate_state` is a record copy.
- Deflate patches (findings page): 0009 keeps `mbase_start = window` in `match_tpl.h` and reads candidates at
  `mbase_start + (cur_match - match_offset)` (the slow variants of levels 7-9 formed `window - match_offset`, before
  the window's block); 0010 bounds `max_insert_count` of `deflate_medium` to `2..STD_MAX_MATCH` (`deflateTune` with
  `max_lazy = INT_MIN` made `insert_knuth_stepped` divide by zero). `tests/expected-faults.txt` is empty: Lean and C
  agree on every generated input. `insert_knuth_stepped` is otherwise called with `count >= 3` and
  `max_inserts >= 4` (`deflate_fast`, through `insert_knuth_spread_static`) or `count > 2 * max_insert_count >= 4`
  (`deflate_medium`), so `inserts - 1 >= 1`.

## inflateBack scope (pinned `develop` commit, verified option set)

Evidence: `nm` of `infback.c.o` in the `libz.a` of `tests/build-zlib-ng.sh` (it defines `inflateBackInit`,
`inflateBackInit_`, `inflateBack`, `inflateBackEnd` and the static `order`, and calls `alloc_inflate`, `free_inflate`,
`fixedtables`, `zng_inflate_table`, `inflate_fast_safe_c`, `chunkmemset_safe_c`, `zcalloc`, `zcfree`).

- Public entry points: `inflateBackInit_` (`CHECK_VER_STSIZE`, then the hidden `inflateBackInit`), `inflateBack`,
  `inflateBackEnd`. Translation: `ZlibNgF/ZlibNg/infback.c.lean`.
- Shared with `inflate.c`: `alloc_inflate` (the same single block, window part included: `inflateBackInit` uses the
  caller's window instead and never reads the allocated one), `free_inflate` (`inflateBackEnd`), `fixedtables`,
  `zng_inflate_table`, and from `inflate_p.h` `LOAD`, `RESTORE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS`,
  `INITBITS`, `SET_BAD`, `CODE_BITS`, `CODE_EXTRA` and the static `chunkcopy_safe`. `infback.c` has its own `PULL`,
  `PULLBYTE` (calling `in()`) and `ROOM` (calling `out()`).
- `inflateBackInit` does not set `state->strm`, `state->mode` or the code pointers; `inflateBack` sets `mode`, `last`
  and `whave` at entry and keeps `hold` / `bits` in locals that start at 0 on every call (there is no `inflatePrime`
  for these streams, so the bit buffer holds fewer than 8 bits whenever `LEN` calls the fast path, and patch 0007's
  cap on the bytes given back never binds). `state->wnext` stays 0.
- `LEN` calls `inflate_fast_safe_c(strm, state->wsize)` (not `inflate_fast_c`) when `have >= 15` and `left >= 3`, with
  `next_out` inside the caller's window, so the output of `inflate_fast` *is* the window (`beg == window`). The safe
  variant bails out to `MATCH` when a match does not fit in `left`; `MATCH` of `infback.c` copies it with
  `chunkcopy_safe` (window to window) or `chunkmemset_safe_c`.
- Patch 0004's concern (comparing a pointer into the window with one into the caller's output) does not arise in
  `infback.c`: both are the caller's window. Patch 0004 copies a window match in `inflate_fast` with `memcpy` only
  when `window != beg`; called from `inflateBack` (`beg == window`) it keeps upstream's `chunkcopy_safe`, which
  handles the overlap of a distance that reaches into the previous window pass (`dist + min(op, len) > wsize`).
  The first version of 0004 used `memcpy` there too (overlapping ranges, ISO C17 §7.24.2.1p2); the guard of
  `tests/regression/infback-window-overlap` keeps that version and checks that it still shows the overlap.
- Call-backs: `in_func` / `out_func` are the parameters `InCb` / `OutCb` of `inflateBack` (caller code); what the
  goals assume of them is in `ZlibNgF/Spec/Common/Infback.lean`.

## gz scope (pinned `develop` commit, verified option set)

Evidence: `nm` of `gzlib.c.o`, `gzread.c.o` and `gzwrite.c.o` in the `libz.a` of `tests/build-zlib-ng.sh`
(`WITH_GZFILEOP=ON`), and the preprocessor conditions of `gzguts.h` (no `_WIN32`, `NO_GZCOMPRESS`, `NO_STRERROR`,
`WIDECHAR`; `O_CLOEXEC` and `O_EXCL` defined; `GZBUFSIZE` 131072, `GZBUFSIZE_MAX` `1u << 30`, `DEF_MEM_LEVEL` 8).

- Public entry points: `gzlib.c`: `gzopen`, `gzopen64`, `gzdopen`, `gzbuffer`, `gzrewind`, `gzseek`, `gzseek64`
  (patch 0002), `gztell`, `gztell64`, `gzoffset`, `gzoffset64`, `gzeof`, `gzerror`, `gzclearerr`, `gzclose`;
  `gzread.c`: `gzread`, `gzfread`, `gzgetc`, `gzgetc_`, `gzungetc`, `gzgets`, `gzdirect`, `gzclose_r`; `gzwrite.c`:
  `gzwrite`, `gzfwrite`, `gzputc`, `gzputs`, `gzvprintf`, `gzprintf`, `gzflush`, `gzsetparams`, `gzclose_w`.
  `gzopen_w` is Windows only (`WIDECHAR`): not applicable. With `ZLIB_COMPAT` and LP64, `z_off_t` and `z_off64_t`
  are both 64-bit, so `gzseek` / `gztell` / `gzoffset` call their `64` variants and return the value unchanged.
- Internal functions: `gzlib.c`: `gz_state_init`, `gz_state_free`, `gz_reset`, `gz_buffer_alloc`, `gz_buffer_free`,
  `gz_open`, `gz_error`, `gz_intmax` (never called); `gzread.c`: `gz_read_init`, `gz_load`, `gz_avail`, `gz_look`,
  `gz_decomp`, `gz_fetch`, `gz_skip`, `gz_read`; `gzwrite.c`: `gz_write_init`, `gz_comp`, `gz_zero`, `gz_write`.
- Library callees: `inflateInit2_` (the `inflateInit2` macro of `zlib.h`, with `ZLIB_VERSION` and `sizeof(z_stream)`),
  `inflate`, `inflateReset`, `inflateEnd`, `deflateInit2_`, `deflate`, `deflateReset`, `deflateParams`, `deflateEnd`,
  `zng_alloc_aligned` / `zng_free_aligned` (the in/out buffers: one block of `in_size + out_size` bytes aligned to 64;
  `in` is `want * 2` bytes when writing, `out` is `want * 2` bytes when reading and absent when writing
  transparently), `zng_alloc` / `zng_free` (`zutil_p.h`: `malloc` / `free` of the `gz_state`).
- libc callees: `open` (glibc: `open`), `read`, `write`, `close`, `lseek` (glibc: `lseek64`, because `zbuild.h`
  defines `_LARGEFILE64_SOURCE`), `strerror`, `errno`, `malloc`, `free`, `strlen`, `memcpy`, `memchr`, `memmove`,
  `memset`, `snprintf` (formats `"%s"`, `"<fd:%d>"`, `"%s%s%s"`), `vsnprintf` (the caller's format).
- Objects: `gz_state` is 248 bytes on LP64, alignment 8, with the `z_stream` embedded at offset 136.
  `gz_state_init` leaves `x.next`, `path`, `buffers`, `err`, `how`, `start`, `eof`, `reset` and most of the
  embedded `z_stream` unset; `gz_reset` sets `err` (through `gz_error`, which reads `msg` only), `x.have`, `x.pos`,
  `skip`, `avail_in` and, when reading, `eof`, `past`, `how`.
- gz model (`Runtime/Fs.lean`, `Runtime/Gz.lean`, trusted base): a gz computation is `G α = StateT World M α`. The
  world holds the file system and descriptor table that `open`, `read`, `write`, `lseek` and `close` act on,
  `errno`, the per-call oracles that choose any other result those calls may give, the `strerror` and
  `vsnprintf` oracles, and the `gz_state` objects. A `gz_state` is a typed object carved from its `malloc` block
  (like the inflate state): its pointer fields start `Ival.uninit`, its integers come from `Heap.garbage`, it
  lives as long as the block, and `free` of the block ends it and the embedded `z_stream` (an entry of
  `Heap.streams`). A `gzFile` is a pointer to the `gz_state` (its first member is the public `struct gzFile_s`).
  What the model trusts about the libc calls is listed in `Runtime/Fs.lean` and `Runtime/Gz.lean`; in short:
  `open` flags and `errno` numbers are those of x86_64 Linux glibc (`O_LARGEFILE` is 0 in user space); `read`,
  `write`, `lseek`, `open`, `close` do what the regular-file model does or what a per-call oracle chooses within
  their POSIX contract (failures with any `errno`, short reads and writes, device data from a finite budget, any
  `lseek` value); `strerror` returns a read-only string of any text; `vsnprintf` with the caller's format and
  arguments (which must match) writes inside `[next, next + size)` only: `min(r, size - 1)` bytes and a zero for a
  result `r >= 0`, any `size` bytes for a failure; `snprintf` with the three fixed formats of `gzlib.c` is modelled
  exactly; `malloc` returns memory aligned for any object; `sizeof(gz_state)` is 248.
- Differential test (`tests/c/gz.c`): the C driver defines `open`, `open64`, `read`, `write`, `lseek`, `lseek64`,
  `close` and `strerror` itself (taking precedence over the C library for the statically linked `libz.a`) as the
  same file-system model and schedule as the Lean side, with Linux flag values (host flags are translated),
  Linux `errno` values and glibc's texts, so the run is target-faithful on any host. It also defines `malloc`, which
  numbers the library's calls on each line and fails the ones the schedule names (`A<k>`), as the Lean side's
  `Heap.allocOk`; the driver's own buffers come from the C library's `malloc` and are not numbered. The C library's
  `snprintf`, `vsnprintf` and string functions are real.
- Undefined behaviour of upstream reached by documented calls, fixed by patches 0011-0014 (findings page): a failed
  `gzwrite` on the direct path left `next_in` in the caller's buffer (`gzwrite.c:185` cross-object subtraction after
  `gzclearerr`; `gzwrite.c:70` reads it again in `gzclose`): patch 0011 resets `next_in` / `avail_in` on that path;
  `gz_buffer_alloc` formed `NULL + in_size` when the allocation failed (`gzlib.c:90`): patch 0012; the readers'
  position `x.pos` overflowed after `gzseek` to near `2^63` on a descriptor whose `lseek` succeeds and which keeps
  delivering data (`gzread.c:356`): patch 0013 stops the readers at `GZ_OFF_MAX`; the writers' `x.pos` overflowed after
  `2^63` bytes in all, failed writes included (`gzwrite.c:210`): patch 0014 refuses a write past `GZ_OFF_MAX`
  (`Z_DATA_ERROR`, comparing in `uint64_t` so that a 32-bit `size_t` does not truncate the room left; guard
  `tests/regression/gzwrite-position-32bit`). Its reproduction needs `2^31 + 1` failing `gzfwrite` calls (minutes), too
  long for `tests/regression/`; the differential test covers the refusal (`gzfwrite` lengths above `GZ_OFF_MAX`, which
  are refused before the buffer is read). `gz_zero` added a batch of a seek's zeros to `x.pos` before writing it but took
  it off `skip` only after success, so a failed write broke `x.pos + skip <= GZ_OFF_MAX` (`gztell` overflow at
  `gzlib.c:496`; the batch written twice after `gzclearerr`): patch 0019 takes it off `skip` before the write, which
  `GzWF`'s `pos_skip` clause needs on the write side. `gzungetc` lowered `x.pos` without a bound (a failed push when the
  buffer is full drops the pushed bytes but keeps the lowered `x.pos`; after `gzclearerr` the pushes start again): patch
  0020 refuses a push at `x.pos <= -GZ_OFF_MAX` (not the minimum value: `gzseek64` negates a negative position), which
  `GzPos.pos_lower` needs. `gzvprintf` counted `size` bytes of input from `next_in`, which a failed `gz_comp` leaves moved
  forward with input left: after `gzclearerr` the input end passed `in + size`, the formatted text overwrote unwritten
  compressed data and then the bytes after the buffer block (guard `tests/regression/gzprintf-failed-write-drift`):
  patch 0021 moves leftover input to `in` before formatting, so `next_in + avail_in <= in + size` holds at every
  return of every writer, as `GzWBuf.inp` says. Open question, not a finding:
  `gzoffset64` computes `offset - avail_in` on an `lseek` result, which overflows for an `lseek` value below
  `INT64_MIN + avail_in`: `GzWF` admits only the `lseek` values POSIX allows (`-1` or not negative), a
  `deviations.md` row (Linux files with unsigned offsets fail their reads at such offsets).

## Checking

`python3 framework/check_project.py zlib-ng` from the repository root. It includes the public API
coverage check (`scripts/verification.py`): `tests/audit/public-api.json` lists every function that
`zlib-ng/zlib.h.in` declares, each `done` (its own `Goal.<function>_safety` proved and in `required` of
`ZlibNgF/Results.lean`) or `not-done` with a reason. When a function becomes done, change its entry and add
its goals to `required`.

Differential tests: `python3 framework/run_difftest.py zlib-ng`, or
`ZLIB_NG_SRC=$PWD/zlib-ng SAN=1 bash tests/run.sh` from this directory. They compare every translated
public function (and the `zutil.c` allocation helpers) with the real patched C library on generated
inputs, then run the patch reproductions of `tests/regression/` (each shows its defect without its
patch and none with all patches). They are evidence of translation fidelity, not proof. When a new C
file is translated, add a driver (`tests/c/`, `tests/lean/Driver/`, `tests/gen/`, `tests/list.txt`,
`tests/lakefile.toml`).
