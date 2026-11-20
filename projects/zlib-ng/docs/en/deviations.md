# Deviations: what a call must satisfy

This page lists every premise of a goal that is narrower than `zlib.h`, or that a reader could
miss. A call outside these lines is not covered: it is neither proved safe nor claimed to be
unsafe.

## Every call

- The library is the zlib-ng `develop` branch at commit `5f1f4899` with the twenty-one patches, built for x86_64
  Linux LP64 with `-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF`,
  so that `adler32` and `adler32_z` run `adler32_c`, and `crc32` and `crc32_z` run `crc32_braid`. A build that
  dispatches to SIMD kernels or to the Chorba CRC-32 kernel (the default) is not covered.
- The static CRC tables `crc_table` and `x2n_table` hold the constants of `crc32_braid_tbl.h`
  (`CrcGlobals`). In C they are constant data; in the model they are part of the heap, so the CRC
  goals state it.
- A buffer argument is either `NULL`, with any `len`, or points to `len` readable bytes inside one
  live object (`BufferBytes`). This is what `zlib.h` asks.
- Theorems hold for every address of every object (`Heap.baseAddr`), so every alignment of a
  buffer is covered.
- The model reads a buffer as 64-bit words (`crc32_braid`, `adler32_swar`) through byte loads; the conversion to
  the word pointer is checked for alignment, the effective-type rule (ISO C17 §6.5p7) is not.

## Narrower than `zlib.h`

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `compressBound` (value only) | `sourceLen ≤ 0xe38e38e38e38e377`. | `Goal.compressBound_functional` | Above this, the sum wraps and the function returns `ULONG_MAX`. Safety holds for every `sourceLen`. |
| `crc32_combine_op` | The low 32 bits of `op` are not 0. | `Goal.crc32_combine_op_safety` | `zlib.h` allows only an `op` made by `crc32_combine_gen` from a non-negative length, which is never 0; with a zero low half `multmodp` does not return. |
| `zng_alloc_aligned` (internal) | `align ≥ 8` and `8 + size + align < 2^32`; the alignment theorem asks `align = 2^k` with `3 ≤ k ≤ 31`. | `Goal.zng_alloc_aligned_safety`, `Goal.zng_alloc_aligned_alignment` | The only caller (`gz_buffer_alloc`) passes 64 and at most `3 * 2^30` bytes. |

## Inflate and uncompress

The goals of `inflate*` and `uncompress*` are stated on the streams that `zlib.h` lets a program reach
(`InflateReachable`): made by a successful `inflateInit_`, `inflateInit2_` or `inflateCopy`, then changed only by
inflate calls with valid arguments and by the program, which may change `next_in`, `avail_in`, `next_out` and
`avail_out` and memory the library does not own. A stream of `Z_NULL`, or with a `NULL` state, is also accepted.

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `inflateInit_`, `inflateInit2_` (and every stream made by them) | `zalloc` and `zfree` are `Z_NULL` (the library's default allocator) or already the defaults. | `InitReady` | Calls through a caller's allocator are not modelled. |
| `inflate`, `inflateSync` | `next_in` and `next_out` are `NULL` or point to `avail_in` readable and `avail_out` writable bytes; these buffers and the registered `gz_header` buffers do not overlap one another or the library's allocation. | `StreamIO` | Caller buffers with no reason to overlap. |
| `inflateSync` | `next_in` is not `NULL` when `avail_in` is not 0. | `SyncInput` | `avail_in` counts the bytes at `next_in`. |
| `inflateGetDictionary` | The buffer is `NULL` or has at least 32768 writable bytes. | `Goal.inflateGetDictionary_safety` | `zlib.h` names 32768 bytes as always enough; the call itself needs only the current window size. |
| `inflateCopy` | `dest` and `source` are different streams; `dest` is ready for initialisation. | `Goal.inflateCopy_safety` | The copy of the `z_stream` is a `memcpy`, undefined for the same object. |
| `inflateGetHeader` | `head` is not `Z_NULL`. | `Goal.inflateGetHeader_safety` | `zlib.h` asks for a `gz_header` structure; on a gzip stream the C writes `head->done` without a test. |
| `inflateInit_`, `inflateInit2_`, `inflateCopy`, `inflateBackInit_`, `uncompress*` | The heap model records no object (bytes, `inflate_state` or `inflate_allocs`) in a block not yet allocated. | `FreshBlocks` | A well-formedness condition of the heap model, true of every heap a program reaches; not a restriction of the C inputs. |
| `inflate` (each call in the history of a stream) | The static CRC tables hold their constants (`CrcGlobals`). | `InflateStep` | Constant data in C (see above); `Goal.inflate_safety` asks it of the call itself. |
| Between calls | The program does not change the other `z_stream` fields or the library's allocation, and does not free a registered `gz_header` record. Any field of that record may change (the program, or another stream that shares it, may write it); its buffers are checked at each `inflate` call. | `CallerStep` | `zlib.h` reserves the `z_stream` fields and the allocation to the library; a registered header is written by `inflate`, so it must stay allocated. |
| `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` | `dest` and `source` do not overlap. | `Disjoint` | Caller buffers with no reason to overlap. |
| `uncompress`, `uncompress2`, `uncompress_z`, `uncompress2_z` | Every object has fewer than `2^63` bytes (at most `PTRDIFF_MAX`). | `ObjBound` | True of every object on x86_64 Linux. The model runs a loop at most `2^64` times and does not bound the size of an object itself; the one-shot loop is bounded by the bytes of source and destination together. |

## Deflate and compress

The goals of `deflate*` and `compress*` are stated on the streams that `zlib.h` lets a program reach
(`DeflateReachable`): made by a successful `deflateInit_`, `deflateInit2_` or `deflateCopy`, then changed only by
deflate calls with valid arguments and by the program, which may change `next_in`, `avail_in`, `next_out` and
`avail_out` and memory the library does not own. A stream of `Z_NULL`, or with a `NULL` state, is also accepted.

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `deflateInit_`, `deflateInit2_` (and every stream made by them) | `zalloc` and `zfree` are `Z_NULL` (the library's default allocator) or already the defaults. | `DInitReady` | Calls through a caller's allocator are not modelled. |
| `deflate`, `deflateParams` | `next_in` and `next_out` are `NULL` or point to `avail_in` readable and `avail_out` writable bytes; the output does not overlap the input or the registered `gz_header` buffers; none of them is inside the library's allocation. | `DStreamIO` | Caller buffers with no reason to overlap. |
| `deflateGetDictionary` | The buffer is `NULL` or has at least 32768 writable bytes. | `Goal.deflateGetDictionary_safety` | `zlib.h` names 32768 bytes as always enough. |
| `deflateCopy` | `dest` and `source` are different streams. | `Goal.deflateCopy_safety` | The copy of the `z_stream` is a `memcpy`, undefined for the same object. |
| `deflateCopy` (failed) | After `deflateCopy` returns an error, `dest` is not an initialised stream; the goals make no claim about later calls on it. | `DeflateReachable`, `DNoState` | Such a `dest` is neither a stream without state nor a stream reached by the calls of `zlib.h`. |
| `deflateSetHeader` (in the history of a stream) | It is called before the first `deflate` call, with a header whose `extra` has `extra_len` readable bytes and whose `name` and `comment` are C strings. | `DeflateStep` | What `zlib.h` asks of `deflateSetHeader`; the call itself is safe at any time (`Goal.deflateSetHeader_safety`). |
| `deflatePrime` (in the history of a stream) | It is called before any pending output of the stream was flushed (`pending_out` is still `pending_buf`), as it is before the first `deflate` call after `deflateInit2` or `deflateReset`. | `DeflateStep`, `PrimeReady` | What `zlib.h` asks of `deflatePrime`. The call writes its bytes at `pending_buf + pending`; after a partial flush, primed bytes push the range that the next `deflate` flushes past `pending_buf`, and repeated calls read past the end of the allocation (AddressSanitizer heap-buffer-overflow in `flush_pending`). The call itself is safe at any time (`Goal.deflatePrime_safety`). |
| `deflateSetDictionary` (in the history of a stream) | It is called with no symbol tallied in the stream's state, as before the first `deflate` call or right after a completed block. | `DeflateStep`, `DictReady` | What `zlib.h` asks: for raw deflate, before any call of `deflate` or right after a block completed with `Z_BLOCK`, `Z_PARTIAL_FLUSH`, `Z_SYNC_FLUSH` or `Z_FULL_FLUSH`. The call sets `block_start` to `strstart`; in the middle of a block the tallied symbols lose their window bytes, and a later `deflateParams` to level 0 can start `deflate_stored` with symbols pending. The call itself is safe at any time (`Goal.deflateSetDictionary_safety`). |
| `deflateResetKeep` (in the history of a stream) | The stream has nothing unfinished: no unfinished block (`block_start` equals `strstart`), no lookahead, no lazy match. Fresh and reset streams meet it, and so do streams after a completed `Z_FINISH` at every level: each strategy ends the last block with `block_start` at `strstart` and no lookahead (at level 1, `quick_end_block` and `quick_start_block` set `block_start` to `strstart`). | `DeflateStep`, `ResetKeepReady` | `deflateResetKeep` is exported but listed among the undocumented functions of `zlib.h`. It keeps the window, `strstart`, `block_start` and the lookahead; on a stream with an unfinished block, a later `deflateParams` to level 0 is accepted without a flush, and `deflate_stored` then copies from a stale `block_start`. The call itself is safe at any time (`Goal.deflateResetKeep_safety`); `deflateReset` has no such premise. |
| `deflateGetDictionary` (in the history of a stream) | The buffer does not overlap the registered `gz_header`'s `extra`, `name` and `comment`. | `DeflateStep` | Caller buffers with no reason to overlap; `deflate` resumes the gzip header at a saved index into these buffers. |
| `deflateBound`, `deflateBound_z` | A registered `gz_header` is readable as for `deflateSetHeader`; every object has fewer than `2^63` bytes. | `DHeaderReadable`, `ObjBound` | `deflateBound` reads the header's strings up to their zero byte. The model runs that loop at most `2^64` times and does not bound the size of an object itself; every object on x86_64 Linux is far smaller. |
| `deflateInit_`, `deflateInit2_`, `deflateCopy` (also as a call that makes a stream the other deflate calls accept, or a step on such a stream), `compress*` | The heap model records no object (bytes, inflate or deflate state) in a block not yet allocated. | `DFreshBlocks` | A well-formedness condition of the heap model, true of every heap a program reaches; not a restriction of the C inputs. |
| `deflate`, `deflateParams` (each call in the history of a stream) | The static CRC tables hold their constants (`CrcGlobals`). | `DeflateStep` | Constant data in C. |
| Between calls | The program does not change the other `z_stream` fields or the library's allocation, and does not free a registered `gz_header` record. While `deflate` is writing the gzip header (from the `deflate` call that starts the header to the one that finishes it), the program keeps the header's `extra`, `extra_len`, `name` and `comment` fields and the lengths of the two strings unchanged. | `DCallerStep` | `zlib.h` reserves the `z_stream` fields and the allocation to the library; `deflate` resumes the header at a saved index into these buffers. |
| `compress`, `compress2`, `compress_z`, `compress2_z` | `dest` and `source` do not overlap; every object has fewer than `2^63` bytes. | `Disjoint`, `ObjBound` | As for `uncompress*`. |

## Call-back decoder

The goal of `inflateBack` is stated on the streams that `zlib.h` lets a program reach (`BackReachable`): made by a
successful `inflateBackInit_` with a window of `2^windowBits` writable bytes, then changed only by `inflateBack` calls
whose call-backs behave as below and by the program.

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `inflateBackInit_` | `zalloc` and `zfree` are `Z_NULL` or already the defaults. | `InitReady` | As for `inflateInit_`. |
| `inflateBack` | The first input (`next_in`, `avail_in`) and every chunk that `in()` hands out are readable, do not overlap the window and are not inside the library's allocation. | `BackCallbacks.chunk` | Caller buffers with no reason to overlap; `zlib.h` asks only that the input stays unchanged until the next `in()` call. |
| `inflateBack` | `in()` and `out()` return, do not write or free the `z_stream` or the library's allocation, and do not free the window or change its size. | `BackCallbacks`, `BackKeep` | `zlib.h` reserves these to the library and forbids changing the window; a call-back that writes the window's contents is not excluded. |
| `inflateBack` | One call is offered fewer than `2^48` input bytes in all, the first chunk included. | `BackCallPre` | With endless input `inflateBack` does not return, in C either. |
| Between calls | The program changes only `next_in`, `avail_in`, `next_out`, `avail_out` of the `z_stream`, does not change the library's allocation, and keeps the window allocated with its size. | `BackCallerStep` | As for inflate streams; the window is used by every call. |

## gz* files

The goals of the gz* functions are stated on the files that `zlib.h` lets a program reach (`GzReachable`): returned
by a successful `gzopen`, `gzopen64` or `gzdopen`, then changed only by gz calls with valid arguments and by the
program, which may use the `gzgetc()` macro and change anything that does not belong to the file. A `NULL` file is
also accepted. Every goal holds for every result of `open`, `read`, `write`, `lseek` (one that POSIX allows, see below), `close`,
`malloc`, `strerror` and `vsnprintf`.

| Function | Premise | Lean | Reason |
| --- | --- | --- | --- |
| `gzread`, `gzfread`, `gzgets`, `gzwrite`, `gzfwrite`, `gzputs` | The caller's buffer (or string) lies outside the file's own blocks (its `gz_state`, path, message, buffers and inflate or deflate state). | `OutsideGz` | The library's memory is not the caller's; a buffer with no reason to overlap it. |
| `gzprintf`, `gzvprintf` | The arguments match the format. | `vsnprintf` oracle (`Runtime/Gz.lean`) | `zlib.h` describes the format as that of `printf`; a mismatch is undefined in `vsnprintf` itself. |
| Every gz function (it matters to `gzoffset`, `gzoffset64`) | `lseek` returns `-1` or an offset that is not negative. | `GzWF` | POSIX: `lseek` returns the resulting offset or `-1`. Linux lets a few device files with unsigned offsets (`/dev/mem`, `/proc/<pid>/mem`) reach offsets of `2^63` and more, which come back as negative numbers; `gzoffset64` subtracts the buffered input from the offset, which overflows within that many bytes of `2^63`. Reads at such offsets fail, so input is buffered there only when the program itself moves the descriptor there, behind the file's back, after a read. |
| Every gz function (what a call may change) | Besides the file's own memory, its fresh blocks, the caller's output buffer and the file system, a call may add static strings: a string literal of the gz* files at its first use, and the text of each `strerror` call. Static strings already there do not change. | `GzFrame` | In C these strings are static data that exist before the call; the model makes each one when it is first used. |
| Every gz function | The read results deliver finitely many bytes, and the inputs (files, delivered bytes) are below `2^62` bytes. | `GzWF` | On an endless input `gzread` may wait forever, as any reader would; the bound only keeps the model's loop fuel from being the limit. |

## Behaviour of the verified source

- `crc32_combine`, `crc32_combine64`, `crc32_combine_gen` and `crc32_combine_gen64` return 0 for a
  negative `len2`.
- `adler32` and `adler32_z` return 1 for a `NULL` buffer of any length.
