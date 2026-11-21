# Status of the results

This page says, for each result and for each public function of zlib, whether it is done. It is
the only page that states a status. Its main point: the three safety results are done, for all
99 goals that make them up, and so is the round trip of the default zlib stream, with its 14
goals.

A result, a goal or a function has one of two states.

- **Done**: a Lean theorem whose statement is exactly the goal exists and passes every check of
  the project. [What a done result rests on](checking.md) says what that amounts to.
- **Not done**: there is no such theorem. "Not planned" is added when no theorem is intended.

For what the results mean, read [the overview](overview.md). For the theorem of each function
and the calls it covers, read [coverage by function](coverage.md) and
[deviations](deviations.md).

## Results {#scope}

Safety means no undefined behaviour, no memory error, no leak, and termination. The results are
about the default x86_64 Linux build of zlib 1.4.0.1-motley with the six patches. Each holds under the
premises of its goals; [the overview](overview.md#the-claim) gives them in short, and
[deviations](deviations.md) by function. A call sequence is the history of one stream, one gzip
file handle or one callback decoder.

| # | Result | Goals | State |
| ---: | --- | --- | --- |
| 1 | `inflate` is safe on every input and every split of the buffers, also over its call sequences. | `Goal.inflate_safety`, `Goal.inflate_sequence_safety` | done |
| 2 | `deflate` is safe on every input and every split of the buffers, also over its call sequences. | `Goal.deflate_safety`, `Goal.deflate_sequence_safety` | done |
| 3 | Every other documented public function is safe: `compress*` and `uncompress*`, the other stream functions, the checksums, the gzip file interface and the callback decoder `inflateBack`. | every other goal of the tables [below](#functions) | done |
| 4 | The round trip of the default zlib stream: `uncompress(compress(x)) = x` when `compress` has `compressBound` room; and compressing with `deflateInit` at the default level and `deflate` calls with any flush value, finished by `deflate(Z_FINISH)` calls, and then decompressing with `inflateInit` gives back the input, for every split of the buffers. | `Goal.compress_uncompress_roundtrip`, `Goal.compress_uncompress_roundtrip_witness`, `Goal.compress_completes`, `Goal.compress_z_completes`, `Goal.uncompress_completes`, `Goal.stream_roundtrip_total`, `Goal.deflate_finish_ends`, `Goal.inflate_chain_ends`, `Goal.stream_roundtrip`, `Goal.deflate_completes_default`, `Goal.deflate_bound_default`, `Goal.inflate_completes_default`, `Goal.default_inflate_progress`, `Goal.default_inflate_completes` | done |

Result 4 is a functional result. It is about the stream that `deflateInit` makes at the default
level and `inflateInit` reads, with no preset dictionary, where every allocation succeeds. Its
encoder histories are `deflateInit`, then `deflate` calls and changes of the buffer fields; a
history with `deflateParams`, a reset or another level is not part of it. The calls that finish
the stream and the `inflate` calls have output room.
[The round trip](proof/roundtrip.md) states each goal with its premises, and
[its table](#round-trip) below says what each goal is.

## Every public function {#functions}

Each documented function of the default build has its own safety goal. The page of each function
in the [API reference](/api.html) shows the statement of its goal.

### Decompression streams {#inflate-streams}

| Function | Goal | State |
| --- | --- | --- |
| `inflate` | `Goal.inflate_safety` | done |
| `inflateCopy` | `Goal.inflateCopy_safety` | done |
| `inflateEnd` | `Goal.inflateEnd_safety` | done |
| `inflateGetDictionary` | `Goal.inflateGetDictionary_safety` | done |
| `inflateGetHeader` | `Goal.inflateGetHeader_safety` | done |
| `inflateInit2_` | `Goal.inflateInit2__safety` | done |
| `inflateInit_` | `Goal.inflateInit__safety` | done |
| `inflateMark` | `Goal.inflateMark_safety` | done |
| `inflatePrime` | `Goal.inflatePrime_safety` | done |
| `inflateReset` | `Goal.inflateReset_safety` | done |
| `inflateReset2` | `Goal.inflateReset2_safety` | done |
| `inflateSetDictionary` | `Goal.inflateSetDictionary_safety` | done |
| `inflateSync` | `Goal.inflateSync_safety` | done |

### Compression streams {#deflate-streams}

| Function | Goal | State |
| --- | --- | --- |
| `deflate` | `Goal.deflate_safety` | done |
| `deflateBound` | `Goal.deflateBound_safety` | done |
| `deflateBound_z` | `Goal.deflateBound_z_safety` | done |
| `deflateCopy` | `Goal.deflateCopy_safety` | done |
| `deflateEnd` | `Goal.deflateEnd_safety` | done |
| `deflateGetDictionary` | `Goal.deflateGetDictionary_safety` | done |
| `deflateInit2_` | `Goal.deflateInit2__safety` | done |
| `deflateInit_` | `Goal.deflateInit__safety` | done |
| `deflateParams` | `Goal.deflateParams_safety` | done |
| `deflatePending` | `Goal.deflatePending_safety` | done |
| `deflatePrime` | `Goal.deflatePrime_safety` | done |
| `deflateReset` | `Goal.deflateReset_safety` | done |
| `deflateSetDictionary` | `Goal.deflateSetDictionary_safety` | done |
| `deflateSetHeader` | `Goal.deflateSetHeader_safety` | done |
| `deflateTune` | `Goal.deflateTune_safety` | done |
| `deflateUsed` | `Goal.deflateUsed_safety` | done |

### Whole buffers and library information {#buffers-and-library}

| Function | Goal | State |
| --- | --- | --- |
| `compress` | `Goal.compress_safety` | done |
| `compress2` | `Goal.compress2_safety` | done |
| `compress2_z` | `Goal.compress2_z_safety` | done |
| `compressBound` | `Goal.compressBound` | done |
| `compressBound_z` | `Goal.compressBound_z` | done |
| `compress_z` | `Goal.compress_z_safety` | done |
| `uncompress` | `Goal.uncompress_safe` | done |
| `uncompress2` | `Goal.uncompress2_safe` | done |
| `uncompress2_z` | `Goal.uncompress2_z_safe` | done |
| `uncompress_z` | `Goal.uncompress_z_safe` | done |
| `zlibCompileFlags` | `Goal.zlibCompileFlags_safety` | done |
| `zlibVersion` | `Goal.zlibVersion_safety` | done |

### Checksums {#checksums}

| Function | Goal | State |
| --- | --- | --- |
| `adler32` | `Goal.adler32_safety` | done |
| `adler32_combine` | `Goal.adler32_combine_safety` | done |
| `adler32_combine64` | `Goal.adler32_combine64_safety` | done |
| `adler32_z` | `Goal.adler32_z_safety` | done |
| `crc32` | `Goal.crc32_safety` | done |
| `crc32_combine` | `Goal.crc32_combine_safety` | done |
| `crc32_combine64` | `Goal.crc32_combine64_safety` | done |
| `crc32_combine_gen` | `Goal.crc32_combine_gen_safety` | done |
| `crc32_combine_gen64` | `Goal.crc32_combine_gen64_safety` | done |
| `crc32_combine_op` | `Goal.crc32_combine_op_safety` | done |
| `crc32_z` | `Goal.crc32_z_safety` | done |

### Callback decoding {#callback-decoding}

| Function | Goal | State |
| --- | --- | --- |
| `inflateBack` | `Goal.inflateBack_safety` | done |
| `inflateBackEnd` | `Goal.inflateBackEnd_safety` | done |
| `inflateBackInit_` | `Goal.inflateBackInit__safety` | done |

### Gzip files {#gzip-files}

| Function | Goal | State |
| --- | --- | --- |
| `gzbuffer` | `Goal.gzbuffer_safety` | done |
| `gzclearerr` | `Goal.gzclearerr_safety` | done |
| `gzclose` | `Goal.gzclose_safety` | done |
| `gzclose_r` | `Goal.gzclose_r_safety` | done |
| `gzclose_w` | `Goal.gzclose_w_safety` | done |
| `gzdirect` | `Goal.gzdirect_safety` | done |
| `gzdopen` | `Goal.gzdopen_safety` | done |
| `gzeof` | `Goal.gzeof_safety` | done |
| `gzerror` | `Goal.gzerror_safety` | done |
| `gzflush` | `Goal.gzflush_safety` | done |
| `gzfread` | `Goal.gzfread_safety` | done |
| `gzfwrite` | `Goal.gzfwrite_safety` | done |
| `gzgetc` | `Goal.gzgetc_safety` | done |
| `gzgetc_` | `Goal.gzgetc__safety` | done |
| `gzgets` | `Goal.gzgets_safety` | done |
| `gzoffset` | `Goal.gzoffset_safety` | done |
| `gzoffset64` | `Goal.gzoffset64_safety` | done |
| `gzopen` | `Goal.gzopen_safety` | done |
| `gzopen64` | `Goal.gzopen64_safety` | done |
| `gzprintf` | `Goal.gzprintf_safety` | done |
| `gzputc` | `Goal.gzputc_safety` | done |
| `gzputs` | `Goal.gzputs_safety` | done |
| `gzread` | `Goal.gzread_safety` | done |
| `gzrewind` | `Goal.gzrewind_safety` | done |
| `gzseek` | `Goal.gzseek_safety` | done |
| `gzseek64` | `Goal.gzseek64_safety` | done |
| `gzsetparams` | `Goal.gzsetparams_safety` | done |
| `gztell` | `Goal.gztell_safety` | done |
| `gztell64` | `Goal.gztell64_safety` | done |
| `gzungetc` | `Goal.gzungetc_safety` | done |
| `gzvprintf` | `Goal.gzvprintf_safety` | done |
| `gzwrite` | `Goal.gzwrite_safety` | done |

`gzvprintf` is undocumented in `zlib.h`. It has a safety goal because `gzprintf` goes through it.
`Goal.compressBound` and `Goal.compressBound_z` are the full contracts of two pure functions with
no heap and no fault; they stand for the safety goals of these two functions.

### Goals about more than one function {#other-goals}

| Statement | Goal | State |
| --- | --- | --- |
| Every call sequence of an inflate stream is safe. | `Goal.inflate_sequence_safety` | done |
| Every call sequence of a deflate stream is safe. | `Goal.deflate_sequence_safety` | done |
| Every call sequence of the callback decoder is safe, for every caller protocol. | `Goal.inflate_back_sequence_safety` | done |
| Every history of a gzip file handle is safe, for every file-system world. | `Goal.gz_sequence_safety` | done |
| The inflate functions refuse a `NULL` or inconsistent stream without a fault. | `Goal.inflate_refusal` | done |
| The deflate functions refuse a `NULL` or inconsistent stream without a fault. | `Goal.deflate_refusal` | done |
| The gzip file functions refuse a `NULL` handle without a fault and change nothing. | `Goal.gz_refusal` | done |
| The premises of the inflate goals can be met: initialisation succeeds on a concrete heap. | `Goal.inflate_initialisation_domain` | done |
| The premises of the deflate goals can be met: initialisation succeeds on a concrete heap. | `Goal.deflate_initialisation_domain` | done |
| The premises of the callback-decoder goals can be met: initialisation succeeds on a concrete heap. | `Goal.inflate_back_initialisation_domain` | done |
| The premises of an `inflateBack` call can be met together, with concrete callbacks and a concrete caller protocol. | `Goal.inflateBack_call_domain` | done |
| The premises of the gzip file goals can be met: two concrete histories of a handle exist, one reading and one writing. | `Goal.gz_sequence_nonvacuity` | done |

### The round trip of the default zlib stream {#round-trip}

| Statement | Goal | State |
| --- | --- | --- |
| `uncompress(compress(x)) = x`: `compress` with `compressBound` room returns `Z_OK`, and `uncompress` of the bytes it wrote, with room for the source, returns `Z_OK` and gives back the source and its length. | `Goal.compress_uncompress_roundtrip` | done |
| The premises of `Goal.compress_uncompress_roundtrip` can be met, on concrete heaps with a non-empty source. | `Goal.compress_uncompress_roundtrip_witness` | done |
| `compress` with `compressBound` room returns `Z_OK`, and what it wrote is a zlib stream that decodes to the source and asks for no preset dictionary. | `Goal.compress_completes` | done |
| The same for `compress_z`. | `Goal.compress_z_completes` | done |
| `uncompress` of a zlib stream that asks for no preset dictionary, with room for its decoding, returns `Z_OK`, writes the decoding and stores its length. | `Goal.uncompress_completes` | done |
| The stream round trip with the completion of both sides: `Goal.deflate_finish_ends` and `Goal.inflate_chain_ends` together. | `Goal.stream_roundtrip_total` | done |
| After any `deflate` calls on a default stream, every continuation by `deflate(Z_FINISH)` calls with output room ends after a bounded number of calls, with all input consumed and an output that decodes to the input. | `Goal.deflate_finish_ends` | done |
| A default decoder given a complete default stream, in any chunks and with output room, ends after a bounded number of `inflate` calls, having written exactly the input of the encoder. | `Goal.inflate_chain_ends` | done |
| When a `deflate` call sequence and an `inflate` call sequence on default streams both reach `Z_STREAM_END`, and the decoder read a prefix of what the encoder wrote, the decoder wrote exactly the input of the encoder. | `Goal.stream_roundtrip` | done |
| After `deflate` calls with `Z_NO_FLUSH` or `Z_FINISH` only, one `deflate(Z_FINISH)` call given all the remaining input and more room than the bound of the whole input leaves returns `Z_STREAM_END`, and the whole output decodes to the whole input. | `Goal.deflate_completes_default` | done |
| On a new default stream, one `deflate(Z_FINISH)` call given all the input and at least `deflateBound` bytes of room returns `Z_STREAM_END` and writes a stream that decodes to the input. | `Goal.deflate_bound_default` | done |
| A default decoder that has read part of a complete default stream, given the rest of it and room for the rest of the decoding, returns `Z_STREAM_END` and writes the rest of the input of the encoder. | `Goal.inflate_completes_default` | done |
| A default decoder on any zlib stream the format accepts: each `inflate` call given more of the stream and output room ends the stream with exactly its decoding, or consumes input or writes output; a stream that asks for a preset dictionary gives `Z_NEED_DICT`. | `Goal.default_inflate_progress` | done |
| A default decoder given the whole rest of a zlib stream the format accepts and room for the rest of its decoding ends the stream in one call, or returns `Z_NEED_DICT` for a stream that asks for a preset dictionary. | `Goal.default_inflate_completes` | done |

## Not planned {#not-planned}

No theorem is intended for these.

| Group | What it covers | Reason |
| --- | --- | --- |
| Functional correctness, except result 4 | What a function computes beyond safety: the round trip, and that `inflate` reads a stream the format accepts to its end, in other configurations (other levels, strategies, window sizes and wrappers, preset dictionaries), through the gzip file interface or through `inflateBack`; what `inflate` does with a stream the format rejects; the bytes the gzip file functions read or write; what `inflateBack` delivers; the full contracts of the four kinds of call sequence (`Goal.inflate_sequence`, `Goal.deflate_sequence`, `Goal.inflate_back_sequence`, `Goal.gz_sequence`); statements about the abstract models only. | The safety results do not need it. The statements about the gzip file interface would also rest on a hand-made model of the file system and of descriptors, and on formatted output that the model takes from the C contract of `vsnprintf` without computing it. A functional fact that a safety proof depends on is proved as part of that proof. |
| Other build configurations | Every configuration except the default x86_64 Linux build. | Each one repeats the whole proof for a different platform model. |
| Undocumented functions | `zError`, `inflateSyncPoint`, `get_crc_table`, `inflateUndermine`, `inflateValidate`, `inflateCodesUsed`, `inflateResetKeep`, `deflateResetKeep`, `gzopen_w`: nine of the ten functions that `zlib.h` declares under "undocumented functions (not part of the zlib API)". The tenth is `gzvprintf`, above. | They are not part of the zlib API. No safety goal is stated for them: not done, not planned. |

Many functions have a theorem for their functional contract all the same, among them eight of
the nine undocumented functions (all but `gzopen_w`, which is not in the default build). The
page of each function in the [API reference](/api.html) says whether its functional
contract is done. A functional contract that is not done is not planned: the only functional
result is result 4, and it is not the contract of one function.
