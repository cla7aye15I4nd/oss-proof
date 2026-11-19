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
  `5f1f4899`). Never
  modify it. The verified source is `zlib-ng/` plus `patches/*.patch` applied in name order, each
  listed in `patches/README.md`.
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
  alignments `SIZEOF_INFLATE_STATE = 9088`, `ALIGNOF_INFLATE_STATE = 64`, `SIZEOF_INFLATE_ALLOCS = 32`,
  `SIZEOF_Z_STREAM = 112` (measured on the built configuration; LP64 layout); that the C accesses a carved object
  only through a pointer to its type (true of the translated code; `inflateCopy`'s `memcpy` of a whole
  `inflate_state` is a record copy, `copyState`); the static `lenfix` / `distfix` tables
  (`Runtime/InffixedTbl.lean`, copied from `inffixed_tbl.h` by a script). Only the default allocator is modelled:
  `zalloc` / `zfree` are `FnPtr.zcalloc` / `FnPtr.zcfree`; calling another function pointer faults.

## Inflate scope (pinned `develop` commit, verified option set)

Evidence: `nm` of the `libz.a` built by `tests/build-zlib-ng.sh` (symbols of `inflate.c.o`, `inftrees.c.o`,
`chunkset_c.c.o`, `uncompr.c.o`) and the preprocessor conditions of the files below. `infback.c`
(`inflateBack*`) is out of this scope.

- Public entry points (`inflate.c`): `inflateInit_`, `inflateInit2_` (both call the hidden `inflateInit2`
  after `CHECK_VER_STSIZE`), `inflate`, `inflateEnd`, `inflateReset`, `inflateReset2`, `inflateResetKeep`,
  `inflatePrime`, `inflateSetDictionary`, `inflateGetDictionary`, `inflateGetHeader`, `inflateSync`,
  `inflateSyncPoint`, `inflateCopy` (with patch 0003), `inflateUndermine` (returns `Z_DATA_ERROR`:
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
- Undefined behaviour of upstream reached by documented calls, fixed by patches 0007-0010 (see the findings page): pointer
  comparison and subtraction between the window and the caller's output in `chunkcopy_safe`
  (`inflate_p.h:224-225`, from `inflate.c:1100`), `CHUNKCOPY_SAFE` (`chunkset_tpl.h:319`) and `chunkmemset_c`
  (`chunkset_tpl.h:119`, `125`) from `inflate_fast_c` (`inffast_tpl.h:269`); `strm->next_in += 0` on a null
  `next_in` in `inflateSync` after `inflatePrime`; `NULL + 0` and `memcpy` from `NULL` in `updatewindow` from
  `inflateSetDictionary(strm, NULL, 0)` on a raw stream; `in -= len` at the end of `inflate_fast`
  (`inffast_tpl.h:327`) moving `next_in` before the caller's buffer when `inflatePrime` left 8 or more bits in
  the bit buffer on entry.

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
