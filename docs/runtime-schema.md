# Runtime schema: the structs of zlib on the object heap

This page says how each struct of zlib is represented in the Lean model: one row per field, with
the C type, the Lean type and the reason. The Lean records and the tables of this page are
generated together from the headers
`zlib.h`, `zutil.h`, `inftrees.h`, `inflate.h`, `deflate.h`, `trees.h`, `gzguts.h` and `crc32.h` of the verified source
(zlib commit `99623ef7097352da7993ba614161fd6a311e046e`) through clang's JSON AST dump, in the default x86_64 Linux build
(`./configure --static`, LP64, `-D_LARGEFILE64_SOURCE=1`).

## How C types map to Lean types

| C | Lean | Why |
| --- | --- | --- |
| `char`, `short`, `int`, `long` and the unsigned forms | `Int8`, `Int16`, `Int32`, `Int64`, `UInt8` .. `UInt64` | LP64: `long` and pointers are 64 bits; plain `char` is signed on x86_64 |
| `enum` type | `UInt32` (`Int32` if an enumerator is negative); the enumerators become constants `X` of that type, and `X_i` of type `Int32` | gcc picks `unsigned int` for the object of an enum type without negative values. The constant itself has type `int` in C: `X` is for a comparison with such an object, `X_i` where the constant meets an `int` |
| `T *` where `T` is a byte, `void` | `BPtr = Ptr BRef`: null, or an array and an offset | a byte buffer is a block of the `bytes` table; `void *` is only ever a byte buffer or opaque in zlib |
| `T *` where `T` is a wider scalar | `WPtr`, `IPtr`, ... (`Ptr` of the reference type of that element) | the same, for the `words` table or for an array inside a struct |
| `T *` where `T` is an array element struct (`ct_data`, `code`) | `CtDataPtr`, `CodePtr` | a pointer into an array of structs is the array and an index, never an address |
| `S *` where `S` is a single struct (`z_stream`, `gz_header`, `deflate_state`, ...) | `Option SRef`; `none` is null | `SRef` is a table entry or the struct inside its owner |
| `struct internal_state *` | `Option StateRef` (a deflate state or an inflate state) | `z_stream.state` is cast to both in the C |
| array field `T f[N]` | `Array T` field | an array that is part of a struct is copied with the struct, as in C; a pointer to it is a constructor of the reference type of `T` |
| struct field `S f` | a nested record `S` | value semantics; `&s->f` is the constructor `in_<owner>_<f>` of `SRef` |
| `union` whose members have one type | one field | `ct_data` is `ush` for both members: they are the same bits |
| function pointer | `FnPtr` (null or a name) | only the default allocator is modelled; any other function is a fault when called |
| static table or instance | a field of `Statics` in the heap, a reference constructor `st_<name>` | read-only: a store through it is a fault; its content is set by the translation |

## What the schema does not model

* **Pointer to pointer, and the address of a scalar field** (`&state->lenbits`, `&state->next` in the call of
  `inflate_table`). The translation passes such out-parameters as results. The generator rejects a struct field of
  type pointer to pointer; the headers have none.
* **Bit-fields and unions with members of different types.** The generator rejects them; there are none in the headers.
* **`opaque` pointers to caller data** (`z_stream.opaque`, `voidpf`) are `BPtr`; a caller object that is not a byte
  block is not representable. zlib never dereferences it.
* **Structs that are defined in `.c` files** (`struct config_s` in `deflate.c`, the `FILE` of the C library).
* **Uninitialised pointers.** A fresh record (`allocK`, `X.garbage`) has null pointers. In C a pointer read from
  uninitialised memory is indeterminate. In the model it is a valid NULL: using it is a null dereference, but
  `p == NULL`, `free(p)` and a copy of it succeed. So a missing write of a pointer field does not show in the model,
  and the runtime does not check it. That the C writes each pointer field before it reads it is **to confirm** by
  source review; no theorem states it. See [trusted base](trusted-base.md), item 2.
  Integers are arbitrary; see [safety](spec/safety.md), uninitialised memory.
* **The lengths of array fields.** `Array` fields have any length. `X.WellFormed` says that every array has the
  declared length, and `Heap.RecordsWellFormed` that every record of the heap does; a theorem carries it as a
  hypothesis (`Heap.WellFormed` adds the static tables). `X.garbage` and `X.zeroed` are well-formed, and the lemmas
  `Heap.RecordsWellFormed.set_*`, `clear_*` and `*.put_*_wf` show that stores keep it.
* **The content of the static tables.** `Statics` holds the arrays; `Statics.WellFormed` says that each has the
  declared length. Their values are fixed by the translation of `trees.c`, `inffixed.h`, `crc32.c` (each from a
  generator that reads the C source). A theorem that needs the values states them as a hypothesis. The generator
  does not compare them with the C.
* **Tables.** The tables of the heap are `Tbl`s (an `Array` read as a function of the block number), so that the
  primitives that write can update in place; see [trusted base](trusted-base.md), item 2.
* **Macros that share a name with an enumerator.** `COPY` is both an enumerator of `inflate.h` (16195) and a macro of
  `gzguts.h` (1). The enumerator keeps the name `COPY`; the macro is the constant `GZ_COPY`.
* **Allocation.** `allocK` faults if the next block number is already in use, so the heap must be `Fresh`
  (`Fresh.slotUsed_next` gives, from `Fresh h`, the hypothesis that the lemma `allocK_some` asks for).
  A direct store (`stK`) of a record whose arrays have the wrong length is not a fault.
* **A cast between the two kinds of state** is a fault at the cast; in C it is a fault only at the access.

The static objects that are not declared in a header are
`lenfix`, `distfix`, `extra_lbits`, `extra_dbits`, `extra_blbits`, `static_l_desc`, `static_d_desc`, `static_bl_desc`.

## Fields

The tables below answer how one C field is stored in Lean. Each group opens with what the struct is for; the rows
give the field name, the element type and the form of reference. A Lean type gives only the width: `UInt32` says a
counter has 32 bits, and whether it counts bytes, bits or table entries follows from the role of the field in the
algorithm.


### `z_stream` (Lean `ZStream`, table `streams` of the heap)

The call record shared by the application and the codec. `next_in` and `next_out` point at the next byte to read and to write; `avail_in` and `avail_out` count, in bytes, what may still be read and written in this call. After a call that was given five bytes of output room and wrote three, the output pointer has advanced by three and `avail_out` has gone from 5 to 2. The running totals, the check value and the pointer to the internal state are in this record too.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `next_in` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `avail_in` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `total_in` | `uLong` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `next_out` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `avail_out` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `total_out` | `uLong` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `msg` | `char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `state` | `struct internal_state *` | `Option StateRef` | opaque `struct internal_state *`: a deflate state or an inflate state (`StateRef`) |
| `zalloc` | `alloc_func` | `FnPtr` | function pointer: null or the name of the function (an allocator other than the default is not modelled) |
| `zfree` | `free_func` | `FnPtr` | function pointer: null or the name of the function (an allocator other than the default is not modelled) |
| `opaque` | `voidpf` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `data_type` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `adler` | `uLong` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `reserved` | `uLong` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`ZStreamRef`): `tab`, `in_gzstate_strm`.

### `gz_header` (Lean `GzHeader`, table `gzheaders` of the heap)

The optional header fields of gzip. `extra`, `name` and `comment` are data pointers; when a header is read, the matching `*_max` field is the capacity the caller supplies, in bytes. The actual length of a header field, the capacity that may be copied and the storage a pointer refers to are three separate conditions.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `text` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `time` | `uLong` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `xflags` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `os` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `extra` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `extra_len` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `extra_max` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `name` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `name_max` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `comment` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `comm_max` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `hcrc` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `done` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`GzHeaderRef`): `tab`.

### `deflate_state` (Lean `DeflateState`, table `dstates` of the heap)

The compressor's working storage, kept across calls. `window` holds the recent history and the input still to be processed; `strstart` is the array index of the current position and `lookahead` the number of unprocessed bytes from there. `head` and `prev` index earlier positions that may match; `sym_buf` holds the symbols already chosen; `pending_buf` holds compressed bytes not yet delivered. `bi_buf` holds bits that do not yet fill a byte, and `bi_valid` counts, in bits, how many of them are valid. Window and matching, symbol records and bit output are separate stages that follow one another.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `strm` | `z_streamp` | `Option ZStreamRef` | pointer to a `z_stream`: `ZStreamRef` (a table entry, or the struct inside its owner), `none` is null |
| `status` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `pending_buf` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `pending_buf_size` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `pending_out` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `pending` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `wrap` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `gzhead` | `gz_headerp` | `Option GzHeaderRef` | pointer to a `gz_header`: `GzHeaderRef` (a table entry, or the struct inside its owner), `none` is null |
| `gzindex` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `method` | `Byte` | `UInt8` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `last_flush` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `w_size` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `w_bits` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `w_mask` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `window` | `Bytef *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `window_size` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `prev` | `Posf *` | `WPtr` | pointer into an array of `UInt16`: `WPtr` |
| `head` | `Posf *` | `WPtr` | pointer into an array of `UInt16`: `WPtr` |
| `ins_h` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `hash_size` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `hash_bits` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `hash_mask` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `hash_shift` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `block_start` | `long` | `Int64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `match_length` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `prev_match` | `IPos` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `match_available` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `strstart` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `match_start` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `lookahead` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `prev_length` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `max_chain_length` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `max_lazy_match` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `level` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `strategy` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `good_match` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `nice_match` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `dyn_ltree` | `struct ct_data_s[573]` | `Array CtData` | array of structs inside a struct: an `Array` of records; a pointer to it is a constructor of `CtDataRef` |
| `dyn_dtree` | `struct ct_data_s[61]` | `Array CtData` | array of structs inside a struct: an `Array` of records; a pointer to it is a constructor of `CtDataRef` |
| `bl_tree` | `struct ct_data_s[39]` | `Array CtData` | array of structs inside a struct: an `Array` of records; a pointer to it is a constructor of `CtDataRef` |
| `l_desc` | `struct tree_desc_s` | `TreeDesc` | struct inside a struct: a nested record (value semantics); its address is the constructor `in_dstate_l_desc` of `TreeDescRef` |
| `d_desc` | `struct tree_desc_s` | `TreeDesc` | struct inside a struct: a nested record (value semantics); its address is the constructor `in_dstate_d_desc` of `TreeDescRef` |
| `bl_desc` | `struct tree_desc_s` | `TreeDesc` | struct inside a struct: a nested record (value semantics); its address is the constructor `in_dstate_bl_desc` of `TreeDescRef` |
| `bl_count` | `ush[16]` | `Array UInt16` | array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `WRef` |
| `heap` | `int[573]` | `Array Int32` | array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `IRef` |
| `heap_len` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `heap_max` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `depth` | `uch[573]` | `Array UInt8` | array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `BRef` |
| `sym_buf` | `uchf *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `lit_bufsize` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `sym_next` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `sym_end` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `opt_len` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `static_len` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `matches` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `insert` | `uInt` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `bi_buf` | `ush` | `UInt16` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `bi_valid` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `bi_used` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `high_water` | `ulg` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `slid` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`DeflateStateRef`): `tab`.

### `inflate_state` (Lean `InflateState`, table `istates` of the heap)

The decompressor's record for resuming. `mode` says whether it is reading a header, building tables, decoding, copying or finishing; `hold` and `bits` keep the bits read but not yet consumed. `length` and `offset` are the byte length and the backward distance of one copy from the history. For the history window, `wsize` is the capacity, `whave` the number of history bytes present and `wnext` the index of the next write. The table pointers and the code-length array let a call after a pause continue the same decoding.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `strm` | `z_streamp` | `Option ZStreamRef` | pointer to a `z_stream`: `ZStreamRef` (a table entry, or the struct inside its owner), `none` is null |
| `mode` | `inflate_mode` | `UInt32` | enum: the enumerators are constants of this type (gcc: `unsigned int` unless negative) |
| `last` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `wrap` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `reqwrap` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `havedict` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `flags` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `dmax` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `check` | `unsigned long` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `total` | `unsigned long` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `head` | `gz_headerp` | `Option GzHeaderRef` | pointer to a `gz_header`: `GzHeaderRef` (a table entry, or the struct inside its owner), `none` is null |
| `reqbits` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `wbits` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `wsize` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `whave` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `wnext` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `window` | `unsigned char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `hold` | `unsigned long` | `UInt64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `bits` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `length` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `offset` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `extra` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `lencode` | `const code *` | `CodePtr` | pointer into an array of `code`: `CodePtr` (null, or an array and an index) |
| `distcode` | `const code *` | `CodePtr` | pointer into an array of `code`: `CodePtr` (null, or an array and an index) |
| `lenbits` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `distbits` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `ncode` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `nlen` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `ndist` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `have` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `next` | `code *` | `CodePtr` | pointer into an array of `code`: `CodePtr` (null, or an array and an index) |
| `lens` | `unsigned short[320]` | `Array UInt16` | array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `WRef` |
| `work` | `unsigned short[288]` | `Array UInt16` | array inside a struct: an `Array` field, so copying the struct copies it; a pointer to it is a constructor of `WRef` |
| `codes` | `code[1444]` | `Array Code` | array of structs inside a struct: an `Array` of records; a pointer to it is a constructor of `CodeRef` |
| `sane` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `back` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `was` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`InflateStateRef`): `tab`.

### `gz_state` (Lean `GzState`, table `gzstates` of the heap)

The file layer keeps the descriptor and the codec in one handle. `fd` is the underlying file; `in` and `out` are the internal buffers; `size` and `want` count, in bytes, the actual and the requested base capacity. `strm` is the embedded stream record. The logical position is about the uncompressed data and the descriptor position about the compressed bytes of the file; the two are not interchangeable.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `x` | `struct gzFile_s` | `GzFile` | struct inside a struct: a nested record (value semantics); its address is the constructor `in_gzstate_x` of `GzFileRef` |
| `mode` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `fd` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `path` | `char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `size` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `want` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `in` | `unsigned char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `out` | `unsigned char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `direct` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `junk` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `how` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `again` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `start` | `off64_t` | `Int64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `eof` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `past` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `level` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `strategy` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `reset` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `skip` | `off64_t` | `Int64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `err` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `msg` | `char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `strm` | `z_stream` | `ZStream` | struct inside a struct: a nested record (value semantics); its address is the constructor `in_gzstate_strm` of `ZStreamRef` |

Reference constructors (`GzStateRef`): `tab`.

### `gzFile_s` (Lean `GzFile`, only a field of another struct)

These three fields are the prefix of the handle that the public interface can see: `have` is the number of bytes that can be read directly from the buffer, `next` points at the next byte, and `pos` is the logical position in the uncompressed data. They share their storage with the `gz_state` that contains them; they are not a second, independent buffer.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `have` | `unsigned int` | `UInt32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `next` | `unsigned char *` | `BPtr` | pointer into a byte block: `BPtr` (block or array of the heap, offset); null is a constructor |
| `pos` | `off64_t` | `Int64` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`GzFileRef`): `in_gzstate_x`.

### `tree_desc` (Lean `TreeDesc`, only a field of another struct)

A tree descriptor joins the dynamic working tree of one set of symbols with the static parameters of the format. `dyn_tree` points at the tree nodes, `max_code` is the largest symbol number in use, and `stat_desc` points at the parameters shared by that kind of symbol. Symbol numbers count table entries; code lengths count bits.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `dyn_tree` | `ct_data *` | `CtDataPtr` | pointer into an array of `ct_data`: `CtDataPtr` (null, or an array and an index) |
| `max_code` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `stat_desc` | `const static_tree_desc *` | `Option StaticTreeDescRef` | pointer to a `static_tree_desc`: `StaticTreeDescRef` (a table entry, or the struct inside its owner), `none` is null |

Reference constructors (`TreeDescRef`): `in_dstate_l_desc`, `in_dstate_d_desc`, `in_dstate_bl_desc`.

### `static_tree_desc` (Lean `StaticTreeDesc`, static instances only)

These read-only parameters say, for one kind of code, how many symbols it allows, what its longest code length is, and which symbols carry extra bits. `elems` counts symbols and `max_length` counts bits; `extra_bits` and `extra_base` locate the number of extra bits.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `static_tree` | `const ct_data *` | `CtDataPtr` | pointer into an array of `ct_data`: `CtDataPtr` (null, or an array and an index) |
| `extra_bits` | `const intf *` | `IPtr` | pointer into an array of `Int32`: `IPtr` |
| `extra_base` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `elems` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `max_length` | `int` | `Int32` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

Reference constructors (`StaticTreeDescRef`): `st_static_l_desc`, `st_static_d_desc`, `st_static_bl_desc`.

### `ct_data` (Lean `CtData`, element of arrays)

One small node has different roles during construction. The same bits of `fc` are first the frequency `freq` and later the code word `code`; `dl` is first the parent node number `dad` and later the code length `len`. The representation stores the same bits; an invariant of the algorithm has to say which reading applies at the current stage.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `fc` | `union { ush freq; ush code }` | `UInt16` | union whose members all have type `UInt16`: one field (the members are the same bits) |
| `dl` | `union { ush dad; ush len }` | `UInt16` | union whose members all have type `UInt16`: one field (the members are the same bits) |

### `code` (Lean `Code`, element of arrays)

One entry of a decoding table. `bits` is the number of bits consumed when the entry is selected, `op` says whether it is a literal, a length or distance, a link to a subtable, or the end-of-block or invalid class, and `val` holds the corresponding value or offset. The width of an entry does not give its meaning; it is read according to the class in `op`.

| Field | C type | Lean type | Why |
| --- | --- | --- | --- |
| `op` | `unsigned char` | `UInt8` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `bits` | `unsigned char` | `UInt8` | scalar: LP64 (`char` is signed, `long` is 64 bits) |
| `val` | `unsigned short` | `UInt16` | scalar: LP64 (`char` is signed, `long` is 64 bits) |

### Reference types of arrays

| Lean type | Elements | Constructors |
| --- | --- | --- |
| `IRef` / `IPtr` | `Int32` | `dstate_heap`, `st_base_dist`, `st_base_length`, `st_extra_lbits`, `st_extra_dbits`, `st_extra_blbits` |
| `WRef` / `WPtr` | `UInt16` | `blk` (table `words`), `dstate_bl_count`, `istate_lens`, `istate_work` |
| `URef` / `UPtr` | `UInt32` | `st_crc_table`, `st_x2n_table` |
| `BRef` / `BPtr` | `UInt8` | `blk` (table `bytes`), `dstate_depth`, `st_dist_code`, `st_length_code` |
| `CodeRef` / `CodePtr` | `Code` | `istate_codes`, `st_lenfix`, `st_distfix` |
| `CtDataRef` / `CtDataPtr` | `CtData` | `dstate_dyn_ltree`, `dstate_dyn_dtree`, `dstate_bl_tree`, `st_static_dtree`, `st_static_ltree` |

### String literals

`strTable` lists the 178 string literals of the library sources: the `*.c` and `*.h` files of the
top directory of the verified source, comments excluded, adjacent literals joined, plus the empty string. They are the
error messages (`zutil.c`, `inflate.c`, `inffast.c`, `inftrees.c`, `trees.c`, `deflate.c`, `gz*.c`), the `z_errmsg`
texts, `ZLIB_VERSION`, the copyright strings and the format strings. The set is closed: `strLitRef` of a text that is
not in the table is a fault. A literal is `BRef.str i`: read-only, always live, never freed, in no table of the heap.

```
""
"\n    "
"\n#else /* W == 4 */\n\nlocal const z_crc_t FAR crc_braid_table[][256] = {\n"
"\n#else /* W == 4 */\n\nlocal const z_word_t FAR crc_big_table[] = {\n    "
"\n#endif\n"
"\n#if N == %d\n"
"\n#if W == 8\n\nlocal const z_crc_t FAR crc_braid_table[][256] = {\n"
"\n#ifdef W\n\n#if W == 8\n\nlocal const z_word_t FAR crc_big_table[] = {\n    "
"\nbit length overflow\n"
"\nbl code %2d "
"\nbl counts: "
"\nbl tree: sent %lu"
"\ncd %3d "
"\ncomprlen %lu(%lu) "
"\ndist data: dyn %lu, stat %lu"
"\ndist tree: sent %lu"
"\ndyn trees: dyn %lu, stat %lu"
"\ngen_codes: max_code %d "
"\nlit data: dyn %lu, stat %lu"
"\nlit tree: sent %lu"
"\nlocal const z_crc_t FAR x2n_table[] = {\n    "
"\nn %3d %c l %2d c %4x (%x) "
"\nnode %d(%d), sons %d(%d) %d(%d)"
"\nopt %lu(%lu) stat %lu(%lu) stored %lu lit %u "
"\nstatic const code distfix[%u] = {"
"\n};"
"\n};\n\n"
"    "
"   It is part of the implementation of this library and is"
"   subject to change. Applications should only use zlib.h."
"   {"
" '%c' "
" (last)"
" * Generated automatically by makefixed()."
" */"
" 3_6?"
" deflate 1.4 Copyright 1995-2026 Jean-loup Gailly and Mark Adler "
" inflate 1.4 Copyright 1995-2026 Mark Adler "
" l %2d v %4x "
" start %u, match %d, length %d\n"
"%1u%s"
"%2u%s"
"%5u%s"
"%c"
"%s"
"%s\n"
"%s%s%s"
"%s0x%016llx%s"
"%s0x%08lx%s"
"(%02x %02x)"
"+r"
",\n"
", "
"/* WARNING: this file should *not* be used by applications."
"/* crc32.h -- tables for rapid CRC calculation\n * Generated automatically by crc32.c\n */\n\nlocal const z_crc_t FAR crc_table[] = {\n    "
"/* header created automatically with -DGEN_TREES_H */\n\n"
"/* inffixed.h -- table for decoding fixed codes"
"1.4"
": "
"<fd:%d>"
"C"
"Can't open trees.h"
"Code too clever"
"[FLUSH]"
"\\[%d,%d]"
"_tr_tally: bad match"
"already enough lookahead"
"bad compressed size"
"bad d_code"
"buffer error"
"code %d bits %d->%d\n"
"compressed data error"
"const uch ZLIB_INTERNAL _dist_code[DIST_CODE_LEN] = {\n"
"const uch ZLIB_INTERNAL _length_code[MAX_MATCH-MIN_MATCH+1]= {\n"
"crc32.h"
"crc32b %w0, %w0, %w1"
"crc32x %w0, %w0, %x1"
"ctx=stm"
"data error"
"file error"
"header crc mismatch"
"hidden"
"incompatible version"
"inconsistent bit counts"
"incorrect data check"
"incorrect header check"
"incorrect length check"
"inflate.c too far\n"
"inflate:         distance %u\n"
"inflate:         end of block\n"
"inflate:         length %u\n"
"inflate:         literal '%c'\n"
"inflate:         literal 0x%02x\n"
"inflate:       code lengths ok\n"
"inflate:       codes ok\n"
"inflate:       stored end\n"
"inflate:       stored length %u\n"
"inflate:       table sizes ok\n"
"inflate:     dynamic codes block%s\n"
"inflate:     fixed codes block%s\n"
"inflate:     stored block%s\n"
"inflate:   check matches trailer\n"
"inflate:   dictionary set\n"
"inflate:   length matches trailer\n"
"inflate:   zlib header ok\n"
"inflate: allocated\n"
"inflate: end\n"
"inflate: reset\n"
"insufficient memory"
"internal error: deflate stream corrupt"
"internal error: inflate stream corrupt"
"invalid bit length repeat"
"invalid block type"
"invalid code -- missing end-of-block"
"invalid code lengths set"
"invalid distance code"
"invalid distance too far back"
"invalid distances set"
"invalid length"
"invalid literal/length code"
"invalid literal/lengths set"
"invalid match"
"invalid stored block lengths"
"invalid window size"
"local const ct_data static_dtree[D_CODES] = {\n"
"local const ct_data static_ltree[L_CODES+2] = {\n"
"local const int base_dist[D_CODES] = {\n"
"local const int base_length[LENGTH_CODES] = {\n"
"lost buf"
"match[2]?"
"mbc=60"
"memory"
"more < 2"
"mrs=512"
"need dictionary"
"need lookahead"
"no flush?"
"no future"
"not enough codes"
"not enough room for search"
"out of memory"
"out of room to push characters"
"pendingBuf overflow"
"position overflow"
"r"
"request does not fit in a size_t"
"request does not fit in an int"
"requested length does not fit in int"
"rfm=fix"
"scan[2]?"
"stalled write on gzprintf"
"state corrupt"
"static const code lenfix[%u] = {"
"stdio error (consult errno)"
"stream end"
"stream error"
"string length does not fit in int"
"too many codes"
"too many length or distance symbols"
"tr_static_init: 256 + dist != 512"
"tr_static_init: dist != 256"
"tr_static_init: length != 256"
"trees.h"
"unexpected end of file"
"unknown compression method"
"unknown header flags set"
"unknown win32 error (%ld)"
"w"
"wild scan"
"zcfree: ptr not found"
"{%u,%u,%d}"
"{{%2u},{%2u}}%s"
"{{%3u},{%3u}}%s"
"}%s"
"};\n"
"};\n\n#endif\n"
"};\n\n#endif\n\n#endif\n"
"};\n\nlocal const z_word_t FAR crc_braid_big_table[][256] = {\n"
```

### Static objects

| Field of `Statics` | C object | Elements | Source |
| --- | --- | --- | --- |
| `dist_code` | `_dist_code` | 512 x `UInt8` | header |
| `length_code` | `_length_code` | 256 x `UInt8` | header |
| `base_dist` | `base_dist` | 30 x `Int32` | header |
| `base_length` | `base_length` | 29 x `Int32` | header |
| `crc_table` | `crc_table` | 256 x `UInt32` | header |
| `static_dtree` | `static_dtree` | 30 x `CtData` | header |
| `static_ltree` | `static_ltree` | 288 x `CtData` | header |
| `x2n_table` | `x2n_table` | 32 x `UInt32` | header |
| `lenfix` | `lenfix` | 512 x `Code` | inffixed.h (included by inftrees.c; copy verbatim) |
| `distfix` | `distfix` | 32 x `Code` | inffixed.h (included by inftrees.c; copy verbatim) |
| `extra_lbits` | `extra_lbits` | 29 x `Int32` | trees.c |
| `extra_dbits` | `extra_dbits` | 30 x `Int32` | trees.c |
| `extra_blbits` | `extra_blbits` | 19 x `Int32` | trees.c |
| `static_l_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |
| `static_d_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |
| `static_bl_desc` | `static_tree_desc` | `StaticTreeDesc` | trees.c |

The three descriptors are read from `trees.c` by the generator. Their members `(static_tree, extra_bits, extra_base, elems, max_length)` are:

* `static_bl_desc` = (`(const ct_data *)0`, `extra_blbits`, 0, 19, 7)
* `static_d_desc` = (`static_dtree`, `extra_dbits`, 0, 30, 15)
* `static_l_desc` = (`static_ltree`, `extra_lbits`, 257, 286, 15)

`bl_order` (`local const uch bl_order[BL_CODES]` in `trees.c`) is not a field of `Statics`: it is only indexed, never
addressed, so the translation of `trees.c` holds it as a plain constant.
