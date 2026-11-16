# Model limits

This page lists the limits of the model that a caller of zlib cannot act on. They are of three
kinds: conditions on the model's heap that goals state as premises; choices in how the runtime
represents C memory and library calls; and limits of functional and model theorems that no
safety goal depends on. Each limit is a place where the model could differ from C. The duties
of a caller are on another page: [deviations](deviations.md). What is trusted is summarised in
the [trusted base](trusted-base.md), whose item 2 this page details.

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

The first two rows are premises of goals. A C program meets them without doing anything; they
exist because a Lean statement quantifies over every model heap, including heaps no C program
can produce. The other three rows are choices of the model that the goals are stated over.

| Area | What the model does | What follows |
| --- | --- | --- |
| Heap well-formedness (`Fresh`, `Uniq`, `LibraryGlobals`, `CrcGlobals`) | The heap an init, open, `compress*` or `uncompress*` call starts on has no live block at or above `nextBlk` (`Fresh`), at most one object per block number (`Uniq`), and the constant tables of the selected build (`LibraryGlobals`). The CRC goals ask only for the two CRC tables (`CrcGlobals`), and the refusals of `inflate` and `inflateSync` only for `Fresh`. A caller edit between calls keeps all three (`Rebuffer`, `GzCallerFrame`). | These are premises about the model's bookkeeping. `zlib.h` puts no such duty on a caller, and no C caller can break them. |
| Loop fuel | Every translated loop runs for at most `2^64` iterations; exhausting the bound is `Fault.outOfFuel`. | A safety goal that concludes a normal return proves that the bound is never reached. Where the C can loop without a bound that the proof can derive, the goal has a premise that bounds it: the [callback input total](deviations.md#callback-decoder) and the [gz read budget](deviations.md#gzip-file-interface). |
| CRC address and word access | `addrOf` observes only the low bits of an address. A heap byte block starts at an aligned address; a static or embedded byte object has an arbitrary, stable residue, which is metadata of the heap that no store changes. A word load assembles eight bytes. | Not modelled: general ABI layout, an arbitrary origin of a raw block, and the aliasing semantics of the C cast to `z_word_t *`. The domain of the checksum goals is not narrowed by this. A [checked example](../tests/verification/regressions/crc-static-address.lean) reads a 47-byte static table through both CRC entries. |
| Null pointer arithmetic | `Ptr.add NULL 0` returns `NULL`. `Ptr.diff` faults on a null argument; the compressor helper `Compress.ptrDiff` returns zero for two nulls. | That the model permits an operation does not show that the C is defined: C17 and C23 leave `NULL - NULL` undefined. The [safety specification](spec/safety.md#null-pointers-and-pointer-differences) compares the operations with the language rules, and a [regression](../tests/regression/compress-allocation/README.md) covers a `NULL` destination of zero capacity. |
| External error strings | `strerror` returns a read-only view tagged with an epoch, a number that each `strerror` call changes. It consumes no allocation attempt and no live block owned by the library. The next `strerror` call invalidates earlier views. | The model is of sequential calls in a fixed locale. Not modelled: concurrent calls, a change of locale, and the reuse of an earlier pointer identity. |

## How the runtime represents C

The runtime defines what a translated run means, so a no-fault theorem is a statement about
these definitions.

### Memory and library operations

The heap has a separate table for each kind of object. Freed block numbers are never reused.
An allocator writes at `nextBlk` only if that number is unused in every table (`Heap.slotUsed`);
otherwise it faults.

| Operation | What the model does |
| --- | --- |
| `memcpy`, `zmemcpy` | Reject null pointers even for zero length, overlapping ranges, and read-only destinations when the length is not zero. Whole-record copies use `copyK`, which rejects copying an object onto itself. A bare load/store record pair does not check overlap. |
| `memmove` | Checks the same ranges and writability, with the same exception for a zero length, but permits overlap and copies from the original source. |
| `memset`, `zmemzero` | `Ptr.fill` counts elements and assigns a value; it rejects a null pointer even for zero length, and a read-only destination when the length is not zero. It stands for a byte `memset` or for zero filling only in the uses that say so. `Ptr.memset` replicates a byte. Whole-record zeroing stores the explicit zero record. |
| `strlen` | Requires a NUL inside the represented block. |
| Allocation | Fresh integers come from the arbitrary garbage function; fresh pointer fields are NULL. A `malloc` request above `PTRDIFF_MAX` bytes returns NULL. Otherwise the `allocOk` oracle determines failure. Every `malloc` call consumes one oracle number. Automatic local objects bypass that oracle and do not consume an allocator attempt. |
| `free` | NULL is a no-op. Otherwise the argument must be the start of a live writable allocation of the represented kind. There is no allocation-origin tag. |
| String literals | `strLitRef` denotes a static read-only NUL-terminated entry in the generated closed `strTable`. It is always live, has stable identity and is never freed. Unknown literal text faults. |

The models of allocation, formatting, `errno`, `abs` and `strerror` cover the uses zlib makes of
them. They are not general models of libc, and that they agree with libc is reviewed, not
proved.

### Representation gaps and proof obligations

| Choice or gap | What follows for a claim about the C |
| --- | --- |
| Uninitialised pointers become NULL | Comparing, copying and freeing such a pointer can succeed in the model without a prior write. A claim about the C needs that every pointer is written before it is read; no theorem states this, and it is **to confirm** by source review. The init translations zero the two allocated stream-state records explicitly; this is not a general property of fresh records or of an automatic `z_stream`. |
| One garbage value per cell | Integer theorems quantify over every `Heap.garbage`, indexed by allocation attempt and cell position. Repeated reads of one cell agree in the model; C does not guarantee that for an indeterminate value, and no program checks that no proof relies on it. |
| Array extents are predicates | The length of an array is not part of its type: `WellFormed`, `Heap.RecordsWellFormed` and `Statics.WellFormed` state the C lengths, and generated lemmas show that operations keep them. No program compares the contents of the static tables with the C. |
| Pointer equality is structural | Pointers to different objects compare unequal, and comparing a dangling pointer for equality does not fault. C guarantees neither, in particular not at the boundary of adjacent objects; no program checks that no proof relies on it. A relational comparison requires the same live array. |
| Address and layout model is partial | There is no general model of ABI addresses, of effective types or of a record as bytes. For eight public functions the result cell is a value and not memory ([deviations](deviations.md#stream-calls-inflate-and-deflate), rows "Result cells" and "Whole-buffer compression"). `z_stream` records live in their own table, so a record that partly overlaps a buffer or another record cannot be expressed ([deviations](deviations.md#stream-calls-inflate-and-deflate), row "Copy destination"). |
| Read-only marking is partial | Byte blocks, named static tables and instances can be read-only. Word blocks and records in tables cannot represent that qualifier. |
| Pointer construction checks are partial | `Ptr.add` checks its result, not whether the offset it starts from was valid. That no translation builds a pointer with an invalid offset through the constructor `Ptr.ref` is reviewed, not checked. |
| Object origin is not tracked | Translated code can free a caller block created by `allocBytes`. Where the API forbids that, the frame and ownership clauses of a goal are what exclude it. A state cast to the wrong kind faults earlier than the corresponding C access. |

### Table updates

`Tbl` wraps an array and reads as a total function of the block number. Missing entries return
the default (`none` or `false`). The update `upd` has proved same-key, different-key and
repeated-update rules, from `Tbl.get_set`.

The primitives that write use `Space.modify`, which takes an array out of its table, changes it
and puts it back, so that no chain of earlier arrays is kept. `Space.modify_eq` states that this
equals the simpler functional operation `put`, which the proofs reason with. Trusted by review:
`Tbl.get_set`, `Tbl.modify_eq`, and the `modify` and `modify_eq` of every generated `Space`
instance.

## Functional and model statements

The rows below limit functional goals, API models and internal lemmas. No safety goal depends
on them. [Progress](progress.md) says which functional goals are planned.

| Area | Limit | What follows |
| --- | --- | --- |
| API manual entries | The Pre of an entry may ask for valid handles, separated buffers, checksums of actual strings, generated operators or a stated call order | The entry describes ordinary use. The Lean goal of the function is the wider statement and is not narrowed by it. |
| Compressor length cell in the API model | The functional models `Concrete.compress2_z` and `Concrete.compress2` take the length cell as an optional scalar and return the stored value | The models say nothing about a cell that aliases the input or the output. The translation has the same scalar cell, which limits the safety goals: [deviations](deviations.md#whole-buffer-utilities-and-checksums), row "Whole-buffer compression". |
| Counted decompression cells | The functional models of `uncompress*` (`Uncompress2`) keep input length, output length and data ranges separate | A cell that aliases data or the other cell is outside these models. |
| Compressor data relation | `Compress2` describes the data with a coarse rejection flag; `Compress2Z` and `Compress2Wrapper` express pointer shapes, error ordering and length stores | A theorem about the data model alone says nothing about an entry point. |
| Bound arithmetic | Both lengths are 64 bits on LP64 | `Goal.compress_bound_value` covers every `UInt64`. It states the numeric formula; that the bound is enough room for the output is a separate statement. Other ABIs need statements about the size conversions. |
| Deflate dictionary order | The zlib branch of the model `DeflSetDict` rejects a dictionary after `started` | The C can accept a dictionary after the stream has ended. `deflate_valid` is a theorem about the model, not about those C executions. |
| Preset dictionary in the byte format | The format relation interprets an ordinary stream with one initial preset dictionary | Not described: the effect on the window of replacing the dictionary of a raw stream after decoding has started; that functional statement is not planned. The safety of such a history is proved: `Goal.inflate_sequence_safety` covers `inflateSetDictionary` at any point. |
| Priming, headers and recovery | Each of these functions has its own functional goal | No functional goal describes every combination of them in one history. |
| Fast decoder helpers | The lemmas about `inflate_fast` assume raw byte blocks for input and output (distinct, or disjoint ranges of one block), a window block other than the output block, six input bytes, 258 output bytes, fewer than eight bits on entry and a sane mode | These are premises of internal lemmas, which the proof of the public goal establishes. They do not restrict the public inflate goal. |
| Accepted-window inflate initialization | The lemma `inflate_init2_valid_public` assumes an accepted `windowBits`: `Api.inflWbits wb.toInt = some (wrap, bits)` | `Goal.inflateInit2_` has no such premise: its theorem `inflate_init2_public` covers every `windowBits` and uses the lemma for the accepted values. |
| Gz file data | The functional gz contracts (`FileData`, `CloseContract`, `GzWriterFormat`, read and write values) and the goals `Goal.gzoffset64`, `Goal.gzoffset` and `Goal.gzrewind` are stated for the world in which every OS call behaves as a regular file (`RegularOs`) | An oracle `lseek` may return without moving the descriptor, as on some Linux devices; there the offset and rewind values do not hold ([regression](../tests/verification/regressions/gz-offset-regular-world.lean)). The safety of these three functions on every world is part of `Goal.gz_sequence_safety`, which has no `RegularOs` premise. Not represented: permissions, parent directories, links, ownership and locking; the failures of the oracle cover their effect on each call. |

The premises of the intermediate deflate theorems, and of the local open, close and priming
lemmas, narrow lemmas and never a public goal.
