# Model limits

This page lists the limits of the model that a caller of zlib cannot act on. They are of three
kinds: conditions on the model's heap that goals state as premises; choices in how the runtime
represents C memory and library calls; and limits of functional and model theorems that no
required safety goal depends on. The duties of a caller are on another page:
[deviations](deviations.md). What is trusted is summarised in the [trusted base](trusted-base.md),
whose item 2 this page details.

Each limit is a place where the model could differ from C. None is permission to narrow a public
theorem silently.

## Names used on this page

| Name | Meaning |
| --- | --- |
| block | One allocation in the model's heap, named by a number |
| `nextBlk` | The number the next allocation gets. Numbers are never reused after a free |
| `Fresh` | No block at or above `nextBlk` is live |
| `Uniq` | A block number holds an object of at most one of the heap's tables |
| `allocOk` | The allocation oracle: for each allocation attempt, whether it succeeds |
| `Heap.garbage` | The garbage function: the value of each integer cell of freshly allocated memory |
| `Tbl` | The table type of the heap: an array read as a total function of the block number |
| `Space.get`, `put`, `modify` | Read an array of the heap, replace it, or change it in place |
| `copyK` | The copy of a whole record, the model of `memcpy` on one struct |
| `strLitRef` | The pointer to a C string literal |

## Conditions on the model that goals state

These rows are premises of goals. A C program meets each of them without doing anything; they
exist because a Lean statement quantifies over every model heap, including heaps no C program
can produce.

| Area | What the goals state | Consequence |
| --- | --- | --- |
| Heap well-formedness (`Fresh`, `Uniq`, `LibraryGlobals`, `CrcGlobals`) | The heap an init, open, `compress*` or `uncompress*` call starts on has no live block at or above `nextBlk` (`Fresh`), at most one object per block number (`Uniq`), and the constant tables of the selected build (`LibraryGlobals`). The CRC goals ask only for the two CRC tables (`CrcGlobals`), and the refusal of `inflate` only for `Fresh`. A caller edit between calls keeps all three (`Rebuffer`, `GzCallerFrame`). | These are conditions on the model's heap, not duties that `zlib.h` puts on a caller. They are premises all the same. `Fresh` does not say that block numbers below `nextBlk` are unique across tables; `Uniq` does. |
| Loop fuel | Every translated loop runs for at most `2^64` iterations; exhausting the bound is `Fault.outOfFuel`. | A safety goal that concludes a normal return proves that the bound is never reached. Where the C can loop without a bound that the proof can derive, the goal carries a premise that bounds it: the [callback input total](deviations.md#callback-decoder) and the [gz read budget](deviations.md#gzip-file-interface). |
| CRC address and word access | `addrOf` observes only low address bits. Heap byte blocks retain the aligned-origin convention; static and embedded byte objects have arbitrary stable residues. Word loads assemble bytes. | General ABI layout, arbitrary raw-block origins and the C cast's aliasing semantics remain outside this abstraction. The public checksum domain is unchanged. The [static-address regression](../tests/verification/regressions/crc-static-address.lean) keeps the input of an earlier counterexample of the model as a positive check. |
| Null pointer arithmetic | `Ptr.add` allows null plus zero; `Ptr.diff` faults on nulls, while the compressor helper `Compress.ptrDiff` permits null minus null. | These model permissions do not establish C definedness. The [safety specification](spec/safety.md#null-pointers-and-pointer-differences) distinguishes the operations and language rules. The [allocation regression](../tests/regression/compress-allocation/README.md) preserves that distinction for zero-capacity null destinations. |
| External error strings | `strerror` returns a read-only view that is tagged with an epoch, a number that each `strerror` call changes. It consumes no allocation attempt and no live block owned by the library. The next `strerror` call invalidates earlier views. | The model selects sequential calls and fixed-locale text. Concurrent calls, locale changes and reuse of an earlier pointer identity are outside this model. Copying text and preserving a borrow are separate proof obligations. This is not a complete correspondence with libc. |

## How the runtime represents C

`ZlibF/Runtime/` defines what a translated run means, so a no-fault theorem is a statement about
these definitions. The two tables list the choices a reviewer has to know.

### Memory and library operations

The heap has a separate table for each kind of object. Freed block numbers are never reused.
An allocator writes at `nextBlk` only if that number is unused in its table; otherwise it faults.
`Fresh` protects future numbers. The initial heap must also have unique block numbers across
tables below `nextBlk`; `Fresh` alone does not express that condition, and `Uniq` does.

| Operation | Model behaviour requiring review |
| --- | --- |
| `memcpy`, `zmemcpy` | Reject null pointers even for zero length, overlapping ranges and read-only destinations. Whole-record copies use `copyK`, which rejects copying an object onto itself. A bare load/store record pair does not check overlap. |
| `memmove` | Checks the same ranges and writability, but permits overlap and copies from the original source. |
| `memset`, `zmemzero` | `Ptr.fill` counts elements and assigns a value; it represents byte `memset` or zero filling only in the stated uses. `Ptr.memset` replicates a byte. Whole-record zeroing stores the explicit zero record. |
| `strlen` | Requires a NUL inside the represented block. |
| Allocation | Fresh integers come from the arbitrary garbage function; fresh pointer fields are NULL. A `malloc` request above `PTRDIFF_MAX` bytes returns NULL. Otherwise the `allocOk` oracle determines failure. Every `malloc` call consumes one oracle number. Automatic local objects bypass that oracle and do not consume an allocator attempt. |
| `free` | NULL is a no-op. Otherwise the argument must be the start of a live writable allocation of the represented kind. There is no allocation-origin tag. |
| String literals | `strLitRef` denotes a static read-only NUL-terminated entry in the generated closed `strTable`. It is always live, has stable identity and is never freed. Unknown literal text faults. Borrowed external error text has a separate read-only view and lifetime. |

The runtime and translations provide particular models of the external operations they use,
not general libc models. Runtime error text and the gzip external helper implement the
fixed-locale, sequential borrowed-view behaviour of the row "External error strings" above.
Allocation, formatting, `errno` and `abs` also require their stated correspondence review;
placement outside `Runtime/` does not reduce their semantic role.

### Representation gaps and proof obligations

| Choice or gap | Consequence for a C claim |
| --- | --- |
| Uninitialised pointers become NULL | Equality, copying and freeing NULL can succeed without a prior write. Every pointer read needs a write-before-read argument. The init translations explicitly zero the two allocated stream-state records; this is not a general property of fresh records or automatic `z_stream` storage. Closing the gap requires initialisation tracking or a distinct uninitialised value for all pointer forms, with checked operations and corresponding translation changes. |
| One garbage value per cell | Integer theorems quantify over every `Heap.garbage`, indexed by allocation attempt and cell position. Repeated reads of a cell nevertheless agree. Proofs must not rely on that agreement where C permits unstable unspecified values. |
| Array extents are predicates | `WellFormed`, `Heap.RecordsWellFormed` and `Statics.WellFormed` must establish C lengths. Generated preservation lemmas retain them. Static contents must match the defining C translation; the runtime does not compare them with C. |
| Pointer equality is structural | Different objects compare unequal; equality of dangling pointers does not fault. Proofs must not rely on outcomes that C does not guarantee, including equality at adjacent object boundaries. Relational comparison requires the same live array. |
| Null arithmetic is partly permitted | `Ptr.add NULL 0` returns NULL. `Ptr.diff` rejects null arguments, but `Compress.ptrDiff` returns zero for two nulls. These choices require a separate definedness argument for the corresponding C calls. The comment on `Ptr.diff` in the source attributes null subtraction to C23, which is inaccurate; see the [operation and language comparison](spec/safety.md#null-pointers-and-pointer-differences). |
| Address and layout model is partial | There is no general ABI address, effective-type or record-byte-view model. CRC observes low address bits: heap byte blocks retain aligned origins; static and embedded byte origins have arbitrary stable residues. The residues are metadata of the heap, not writable bytes: no store changes them. Byte-assembled word loads do not settle the C cast's aliasing semantics. Scalar-cell adapters may omit aliases. `z_stream` records live in their own table, so a record that partly overlaps a buffer or another record cannot be expressed ([deviations](deviations.md#stream-calls-inflate-and-deflate), row "Copy destination"). |
| Read-only marking is partial | Byte blocks, named static tables and instances can be read-only. Word blocks and records in tables cannot represent that qualifier. |
| Pointer construction checks are partial | `Ptr.add` checks its result, not whether a manually constructed starting offset was valid. Translation review must exclude invalid uses of the public `Ptr.ref` constructor. |
| Object origin is not tracked | A caller block created by `allocBytes` can be freed by translated code. Frame and ownership clauses must prevent this where the API forbids it. A wrong-kind state cast faults earlier than the corresponding C access. |

The [runtime review](checking/runtime-review.md) is historical evidence about these choices,
not independent approval of the current definitions.

### Table updates

`Tbl` wraps an array and reads as a total function of the block number. Missing entries return
the default (`none` or `false`). The update `upd` has proved same-key, different-key and
repeated-update rules, from `Tbl.get_set`.

The primitives that write use `Space.modify`, which takes an array out of its table, changes it
and puts it back, so that no chain of earlier arrays is kept. `Space.modify_eq` states that this
equals the simpler functional operation `put`. The trusted review must cover `Tbl.get_set`,
`Tbl.modify_eq` and the `modify` and `modify_eq` of every generated `Space` instance. The
operation lemmas reason with `put`; that the executable runs fast does not establish their
correspondence. See the [table-update review](checking/runtime-tables-review.md).

## Functional and model statements

The rows below limit functional goals, API models and internal lemmas. No required safety goal
depends on them. They stay listed because the theorems they limit stay registered. Functional
goals are not required for the safety results ([scope](progress.md#scope)).

| Area | Present limit | Consequence |
| --- | --- | --- |
| Focused function manuals | Entries may require valid handles, separated buffers, checksums of actual strings, generated operators or a stated call order | These are explicit prose scopes. They do not reduce the broader Lean public targets. |
| Compressor length cell in the API model | The functional models `Concrete.compress2_z` and `Concrete.compress2` use an optional scalar input and returned stored value | This row is about the functional model only. Aliasing the cell with input or output is absent there. Null-cell effects remain different for `_z` and compatibility wrappers. The translation has the same scalar cell, and that does limit required safety goals: see [deviations](deviations.md#whole-buffer-utilities-and-checksums), row "Whole-buffer compression". |
| Counted decompression cells | Draft adapters keep input length, output length and data ranges separate | Aliasing the cells with data or each other is outside these adapters. Early and late memory failures retain distinct scalar effects. |
| Compressor data relation | `Compress2` describes data with a coarse rejection flag | `Compress2Z` and `Compress2Wrapper` express pointer shapes, error ordering and length stores. A data-model theorem alone is not an entry-point refinement. |
| Bound arithmetic | Both lengths are 64 bits on LP64 | `Goal.compress_bound_value` covers every `UInt64`, without a smaller numeric premise. Other ABIs need size-conversion statements. The numeric formula alone is not output adequacy. |
| Deflate dictionary order | The zlib branch of `DeflSetDict` rejects a dictionary after `started` | C can accept a dictionary after stream end. A refinement may use the rejection only within the documented ordering. `deflate_valid` is a model theorem, not a theorem about all such C executions. |
| Ordinary byte-format epochs | One initial preset dictionary interprets an ordinary stream | Raw dictionary replacement after decoding starts has a constructor-derived marker. Its exact window effect is a functional statement and is not planned. Sequence safety of those histories is proved: `Goal.inflate_sequence_safety` is registered and covers `inflateSetDictionary` at any point of a history. A single initial dictionary cannot describe the entire advanced history. |
| Advanced operation combinations | Priming, headers and recovery retain concrete per-entry targets | The target set is not a completed operational refinement of every combination. A proof may not choose or clear history eligibility markers to avoid obligations. |
| Fast decoder helpers | Local execution and bit-origin lemmas assume raw byte blocks for input and output (distinct, or disjoint ranges of one block), a window block other than the output block, six input bytes, 258 output bytes, entry bits below eight and sane mode | These are internal premises for construction and init invariants to establish. They do not restrict or prove the public inflate goal. |
| Accepted-window inflate initialization | `inflate_init2_valid_public` assumes `Api.inflWbits wb.toInt = some (wrap, bits)` | It retains the existing initialization contract, including all allocation outcomes, ABI/version refusal and null-stream refusal, for accepted raw/zlib/gzip/automatic window parameters. Invalid window arguments are excluded explicitly; the fixed `Goal.inflateInit2_` and its recorded cleanup-contract issue are unchanged. |
| Gz file data | Functional gz contracts (`FileData`, `CloseContract`, `GzWriterFormat`, read and write values) and the registered goals `Goal.gzoffset64`, `Goal.gzoffset` and `Goal.gzrewind` (premise `RegularOs fs`) are stated for the world in which every OS call behaves as a regular file (`RegularOs`) | They describe regular files. An oracle `lseek` may return without moving the descriptor, as on some Linux devices; there the offset and rewind values do not hold ([regression](../tests/verification/regressions/gz-offset-regular-world.lean)). The safety goals do not use these contracts. The safety of `gzoffset64`, `gzoffset` and `gzrewind` on every world is part of `Goal.gz_sequence_safety`, which is registered and has no `RegularOs` premise. File-system permissions, parent directories, links, ownership and locking are not represented; the oracle's failures cover their effect on each call. |

The premises of the intermediate deflate theorems, and of the local open, close and priming
lemmas, narrow lemmas and never a public goal. They are kept in
[internal deflate proof scopes](history/deviations-internal-scopes.md).
