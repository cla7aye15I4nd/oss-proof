# Proof reference: component, page, theorem

The pages in this section explain, for one C file each, why the theorems about it hold. This
page is the map: which page explains which theorem. A reader who knows the C should be able to
follow each page with the matching file under `zlib/` open, without reading Lean.

Every safety goal named on these pages is done: it has a theorem of exactly its type, and
Lean's kernel has checked the proof. [Progress](../progress.md) lists every result. What each
theorem assumes is on its page and in [deviations](../deviations.md); what the model itself
assumes is in the [trusted base](../trusted-base.md) and in
[model limits](../model-limits.md).

For a first reading, follow the [overview](../overview.md). Terms are in the
[glossary](../glossary.md).

## Theorems, lemmas and readings

The pages name theorems and lemmas. The theorem of a goal has exactly the goal as its type. A
lemma is a step inside the proof of such a theorem; a page says so where it names one. Lean's
kernel has checked both.

Differential tests compare the translation with the compiled C. They are evidence that the
translation is faithful, not proof.

The prose on these pages is an explanation, not a checked object. Where a page states a reading
of the C that no theorem states, it marks it **to confirm**. The pages that follow
[one outline](#the-shape-of-a-component-page) collect these in a section "Readings of the C
that no theorem states".

## Required and not required

The required results are safety results: no undefined behaviour, no memory error, no leak, and
termination, for every documented public function of the default x86_64 Linux build, over its
call sequences. The two `compressBound` contracts state the value of the bound; they serve as
the safety goals of those two functions.

Functional results say what a function computes: a checksum value, the decoded bytes. They are
not required for the safety results. Many have theorems, and each page lists them in a section
of their own. Two of them, `Goal.inflate` and `Goal.deflate`, are used by safety proofs of
other functions.

Other build configurations and the functions that `zlib.h` lists as undocumented are not
required; [progress](../progress.md#not-planned) gives the reasons.

## What a sequence theorem covers

A *sequence* theorem is about every permitted series of calls on one stream, not about one
call. For example:

```c
deflateInit(&strm, level);
while (more_input) {
    strm.next_in = in;   strm.avail_in = n;      /* the caller edits four fields */
    strm.next_out = out; strm.avail_out = m;
    deflate(&strm, Z_NO_FLUSH);                  /* any return value */
}
deflate(&strm, Z_FINISH);
deflateEnd(&strm);
```

`deflate_sequence_safety` covers this program for every level, every buffer size and every
input, and every other program made of `deflateInit2_`, the `deflate*` calls and such edits.
It says that each call returns without a fault, that the memory it changed is the memory it was
entitled to change, and that `deflateEnd` at any point frees everything.

## The map

| C file | Page | Required safety theorems |
| --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`, `adler32_z_safety`, `adler32_combine_safety`, `adler32_combine64_safety` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`, `crc32_z_safety`, `crc32_combine_safety`, `crc32_combine64_safety`, `crc32_combine_gen_safety`, `crc32_combine_gen64_safety`, `crc32_combine_op_safety` |
| `zutil.c` | [Utilities and allocation](zutil.md) | `zlibVersion_safety`, `zlibCompileFlags_safety` |
| `inftrees.c` | [Decode tables](inftrees.md) | No public function. Internal: `inflate_table_safe`, `inflate_table_decoder_safe` |
| `inffast.c` | [Fast decoding](inffast.md) | No public function. Internal: `inflate_fast_safe` |
| `inflate.c` | [Stream decoding](inflate.md) | Sequence: `inflate_sequence_safety_public`. One per function: `inflate_safety` and nine more. Also `inflateInit__safety`, `inflateInit2__safety`, `inflateCopy_safety`, `inflate_refusal`, and the non-vacuity theorem `inflate_initialisation_domain_public` |
| `deflate.c` | [Stream compression](deflate.md) | Sequence: `deflate_sequence_safety`. One per function: `deflate_safety` and twelve more. Also `deflateInit__safety`, `deflateInit2__safety`, `deflate_copy_safety`, `deflate_refusal`, and the non-vacuity theorem `deflate_initialisation_domain_public` |
| `trees.c` | [Trees and block output](trees.md) | No public function. Its lemmas serve `deflate_sequence_safety`. Theorems about internal steps: `tinyOverlayAt_256`, `tinyOverlayAt_128` (the bound on the shared buffer for the two smallest `memLevel` values), `gen_bitlen_safe`, `pqdownheap_safe` |
| `infback.c` | [Callback decoder](callbacks.md) | Sequence: `inflate_back_sequence_safety`. One per function: `inflateBackInit__safety`, `inflateBack_safety`, `inflateBackEnd_safety`. Non-vacuity: `back_init_domain_public` |
| `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c` | [Gzip files](gzip.md) | Sequence: `gz_sequence_safety_public`. One per function: `gzread_safety` and 31 more. `NULL` handle: `gz_refusal`. Non-vacuity: `gz_sequence_nonvacuity_public` |
| `compress.c` | [Safety of `compress*`](compress-safety.md) | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety`; for the two bound functions, the theorems named `compressBound` and `compressBound_z` like the functions |
| `uncompr.c` | [Safety of `uncompress*`](uncompress-safety.md) | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` |

The 31 gz functions, `gzvprintf` and the three `inflateBack` functions each have a one-function
safety theorem as well. It applies the sequence theorem of the family to the calls of one
function, and it includes the refusals of that function: a `NULL` handle for a gz function that
takes a handle; a `NULL` stream and a stream record with a `NULL` state for `inflateBack` and
`inflateBackEnd`, and for `inflateBackEnd` also a `NULL` `zfree`. The theorem of
`inflateBackInit_` covers every call `zlib.h` allows and needs no history.

The one-function theorems of `inflate.c` and `deflate.c`, init apart, have the same two parts:
the refusal of a `NULL` or inconsistent stream, and the call on a reachable stream. The two copy
theorems add the refusal of an inconsistent source to that of a `NULL` argument. `inflate_refusal`
and `deflate_refusal` state the refusals of several functions in one statement each
([inflate](inflate.md#refusals), [deflate](deflate.md#refusals)).

Other results of `trees.c` that the page explains are lemmas inside the proof of
`deflate_sequence_safety`, among them the bound on the shared buffer for `memLevel` 3 to 9
(`dynamic_overlay_mid`, `dynamic_overlay_large`). The [trees](trees.md#results) page names
each.

## Other pages of this section

| Page | What it is |
| --- | --- |
| [Proving one function](method.md) | The method: what a proof has to show, invariants, frame, ownership, and what the kernel check and the tests each add |
| [Source notes for the decoder](inflate-source-notes.md), [Source notes for the compressor](deflate-source-notes.md) | Details of the C that the translation has to follow exactly. Readings, not theorems |
| [The default-configuration engine](deflate-default-engine.md) | Functional results about `deflate` for one configuration |
| [Buffer utilities](buffers.md) | Readings of `compress.c`, `uncompr.c` and the bound functions that the two safety pages rely on |

## Functional results

These pages also explain results that are not required for the safety results. Each result
of this table has a theorem.

| Page | Functional results explained |
| --- | --- |
| [Adler-32](adler32.md), [CRC-32](crc32.md) | The checksum values and the combination formulas |
| [Decode tables](inftrees.md), [Fast decoding](inffast.md) | The table entries are the canonical code; a round of the fast loop decodes one token of the format |
| [Stream decoding](inflate.md) | `Goal.inflate`, the full contract of one call (`inflate_public`) |
| [Stream compression](deflate.md) | `Goal.deflate`, the full contract of one call (`Zlib.Deflate.Universal.deflate_safety`) |
| [The default-configuration engine](deflate-default-engine.md) | For the default configuration: the output of a completed stream is a valid zlib stream for its input by the format specification, and a stream can be completed (`DeflateCore.correct`) |

The round trip of the default zlib stream, `deflate` and then `inflate` giving back the input,
is not done. One theorem, `deflate_inflate_roundtrip`, proves a conditional form: if both
histories end with a call that returned `Z_STREAM_END` and the input `inflate` consumed is a
prefix of the bytes `deflate` wrote, then the bytes `inflate` wrote are the bytes `deflate`
read. No theorem says that both sides reach `Z_STREAM_END`.
[Stream compression](deflate.md#functional-results) gives the premises.

## The shape of a component page

The pages for `inflate.c`, `inffast.c`, `inftrees.c`, `deflate.c` and `trees.c` follow one
outline. A page leaves out a section that has no content for its file, and some pages add
sections of their own.

1. **Results.** The theorems and what each states.
2. **Assumptions.** Every premise of the main theorem.
3. **The invariant**, clause by clause in plain words.
4. **Why each step keeps it**, with the theorem that carries each step.
5. **Why the loops end**: the measure that falls.
6. **Where the hard part is.**
7. **Readings of the C that no theorem states.**
8. **Functional results**, where there are any.

The pages for `inftrees.c` and `trees.c` have no invariant section; their argument is in the
section "Why each step is safe". The page for `trees.c` has no section on functional results.

## Reading order

For decompression: [decode tables](inftrees.md), then [fast decoding](inffast.md), then
[stream decoding](inflate.md). Table construction gives the table shape that both decoders
rely on, and the stream decoder establishes the entry conditions of the fast path.

For compression: [stream compression](deflate.md) for the window and the hash chains, then
[trees](trees.md) for tree construction and the buffer that output and symbols share.

The gzip file interface and the callback decoder build on these. Read their pages last.

## Conventions

An interval `[a, b)` includes `a` and excludes `b`. A pointer may point one past the end of an
array; that position may not be read. Unsigned arithmetic wraps as in C. Signed arithmetic is
checked: an overflow is a fault in the model.

Three families of identifiers appear on the pages.

- `U1` to `U12` are the safety obligations: ten kinds of undefined behaviour, termination and
  leaks ([safety](../spec/safety.md)).
- `F1` to `F9` are structural facts that several proofs use
  ([the method](method.md#structural-facts-used-by-several-proofs)).
- `I-*` are internal contracts between functions
  ([internal contracts](../spec/internal-contracts.md)).

A bound that depends on the widths, tables or allocator of the default build holds for that
build only. The integer and pointer rules of the model are in
[translation semantics](../design/translation.md).
