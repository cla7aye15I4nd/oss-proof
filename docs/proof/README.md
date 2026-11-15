# Proof reference: component, page, theorem

The pages in this section explain, for one C file each, why the theorems about it hold. This
page is the map: which page explains which theorem, where the theorem is, and what level it
has. A reader who knows the C should be able to follow each page with the matching file under
`zlib/` open, without reading Lean.

Every required safety goal has a registered theorem of exactly its type. Nothing in the
required set is open. What each theorem assumes is on its page and in
[deviations](../deviations.md); what the model itself assumes is in the
[trusted base](../trusted-base.md) and in [model limits](../model-limits.md).

For a first reading, follow the [overview](../overview.md). Terms are in the
[glossary](../glossary.md).

## Status levels

The pages use three words for the state of a theorem. The [glossary](../glossary.md#status)
defines them, and [checking](../checking/README.md#three-levels) says which checks stand behind
each and where a reader sees it.

- **Checked.** The theorem is on the integration branch `dev`, and the fast gate is green on
  that commit. Lean's kernel has checked the proof. The fast gate is the two jobs `build` and
  `no-sorry` of the workflow `.github/workflows/lean.yml`, which run on every push to `dev` or
  `main` and on every pull request. `build` builds the library and the differential-test
  drivers, searches the sources for forbidden constructs, checks the built environment for
  `unsafe` and `partial` declarations, and applies the patches to the pinned `zlib/`. `no-sorry`
  checks that there is no `sorry` and that every string literal of the translations is in the
  runtime's table of literals, and runs the import check between the specification layers
  (`scripts/check-spec-layers.py`).
- **Registered.** The theorem is checked, its name is listed in `tests/audit/theorems.txt`, and
  the goal it proves is listed in `tests/audit/proved-goals.txt`. The two lines are a claim; the
  acceptance suite is the check that the theorem's type is exactly the goal. It also checks the
  axioms each registered theorem depends on.
- **Accepted.** The theorem is registered, and the acceptance suite is green on a named commit.
  Only an accepted result is reported as final, and always with that commit. The commit is
  `bde170e9` ([progress, Scope](../progress.md#scope)). The four initialisation goals of
  `inflate` and `deflate` were widened after it; they are registered in the wider form and
  accepted in the form they had on that commit.

A theorem that is checked and not registered is a lemma inside the proof of a registered
theorem. The pages say so where they name one. The axiom check of a registered theorem follows
its dependencies, so it covers such lemmas too.

Differential tests belong to the acceptance suite. They compare the translation with the
compiled C. They are evidence that the translation is faithful, not proof.

The prose on these pages is an explanation, not a checked object. Where a page states a reading
of the C that no theorem states, it marks it **to confirm**. Each component page collects these
in a section "Readings of the C that no theorem states".

## Required and not required

The required results are safety results: no undefined behaviour, no memory error, no leak, and
termination, for every documented public function of the default x86_64 Linux build, over its
call sequences. The goals are in `ZlibF/Spec/Safety/`; for the gzip file interface and the
callback decoder they are in `ZlibF/Spec/Public/GzSafety.lean`,
`ZlibF/Spec/Public/GzRefusal.lean` and `ZlibF/Spec/Public/Sequences.lean`.

Functional results say what a function computes: a checksum value, the decoded bytes. They are
not required for the safety results. Many are proved and registered, and each page lists them
in a section of their own. Two of them, `Goal.inflate` and `Goal.deflate`, are used by safety
proofs of other functions. See
[the safety and functional split](../design/safety-functional-split.md).

Other build configurations and the functions that `zlib.h` lists as undocumented are not
required; [progress, Scope](../progress.md#scope) gives the reasons.

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

All modules are under `ZlibF/Proof/`. Every theorem named in this table is registered in
`tests/audit/theorems.txt`.

| C file | Page | Required safety theorems | Module |
| --- | --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`, `adler32_z_safety`, `adler32_combine_safety`, `adler32_combine64_safety` | `public-stateless-safety.lean` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`, `crc32_z_safety`, `crc32_combine_safety`, `crc32_combine64_safety`, `crc32_combine_gen_safety`, `crc32_combine_gen64_safety`, `crc32_combine_op_safety` | `public-stateless-safety.lean` |
| `zutil.c` | [Utilities and allocation](zutil.md) | `zlibVersion_safety`, `zlibCompileFlags_safety` | `public-stateless-safety.lean` |
| `inftrees.c` | [Decode tables](inftrees.md) | No public function. Internal: `inflate_table_safe`, `inflate_table_decoder_safe` | `inftrees.c.lean`, `inftrees.c.decoder-safe.lean` |
| `inffast.c` | [Fast decoding](inffast.md) | No public function. Internal: `inflate_fast_safe` | `inffast.c.final.lean` |
| `inflate.c` | [Stream decoding](inflate.md) | Sequence: `inflate_sequence_safety_public`. One per function: `inflate_safety` and nine more. Also `inflateInit__safety`, `inflateInit2__safety`, `inflateCopy_safety`, `inflate_refusal`, and the non-vacuity theorem `inflate_initialisation_domain_public` | `public-inflate-sequence-safety.lean`, `public-stream-call-safety.lean`, `public-init-safety.lean`, `public-inflate-copy-safety.lean`, `public-stream-refusal.lean`, `public-inflate-init.lean` |
| `deflate.c` | [Stream compression](deflate.md) | Sequence: `deflate_sequence_safety`. One per function: `deflate_safety` and twelve more. Also `deflateInit__safety`, `deflateInit2__safety`, `deflate_copy_safety`, `deflate_refusal`, and the non-vacuity theorem `deflate_initialisation_domain_public` | `public-deflate-goals.lean`, `public-stream-call-safety.lean`, `public-init-safety.lean`, `public-deflate-copy.lean`, `public-stream-refusal.lean`, `public-deflate-init-domain.lean` |
| `trees.c` | [Trees and block output](trees.md) | No public function. Its lemmas serve `deflate_sequence_safety`. Registered: `tinyOverlayAt_256`, `tinyOverlayAt_128` (the bound on the shared buffer for the two smallest `memLevel` values), `gen_bitlen_safe`, `pqdownheap_safe` | `deflate.c.engine.overlay-header-ref.lean`, `trees.c.heap.*.lean` |
| `infback.c` | [Callback decoder](callbacks.md) | Sequence: `inflate_back_sequence_safety`. Non-vacuity: `back_init_domain_public` | `infback.c.safety-fast.lean`, `public-infback-init.lean` |
| `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c` | [Gzip files](gzip.md) | Sequence: `gz_sequence_safety_public`. `NULL` handle: `gz_refusal`. Non-vacuity: `gz_sequence_nonvacuity_public` | `public-gz-sequence-safety.lean`, `public-gz-refusal.lean`, `public-gz-sequence-nonvacuity.lean` |
| `compress.c` | [Safety of `compress*`](compress-safety.md) | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety`; for the bound functions `compressBound`, `compressBound_z` | `public-compress-safe-mid.lean`, `public-compress-bound.lean` |
| `uncompr.c` | [Safety of `uncompress*`](uncompress-safety.md) | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` | `public-uncompress-safe.lean` |

The 31 gz functions and the three `inflateBack` functions are proved safe through their
sequence theorem. They have no separate one-function goal yet. This is not an open proof: the
sequence goals cover every call of these functions, and the manifest
`tests/audit/public-api.json` names the sequence goal as the safety goal of each of them.

Some lemmas of `trees.c` that the page explains are checked and not registered, among them the
bound on the shared buffer for `memLevel` 3 to 9 (`dynamic_overlay_mid`,
`dynamic_overlay_large`). The [trees](trees.md#results) page gives the level of each.

## Other pages of this section

| Page | What it is |
| --- | --- |
| [Proving one function](method.md) | The method: what a proof has to show, invariants, frame, ownership, how a stuck proof is diagnosed |
| [Source notes for the decoder](inflate-source-notes.md), [Source notes for the compressor](deflate-source-notes.md) | Details of the C that the translation has to follow exactly. Readings, not theorems |
| [The default-configuration engine](deflate-default-engine.md) | Earlier functional results about `deflate` for one configuration |
| [Buffer utilities](buffers.md) | Readings of `compress.c`, `uncompr.c` and the bound functions that the two safety pages rely on |
| [Earlier arguments and reference sources](../history/references.md) | A map from an earlier development to the present modules, kept in the history section. A reuse record; it supplies no proof |

Records of corrected statements are in `docs/history/`. Two of them concern an earlier
functional goal about `deflate`, `DeflateCompletes`:
[input after finish](../history/deflate-completion-input.md) and
[null output](../history/deflate-completion-null-output.md).

## Functional results

These pages also explain results that are not required for the safety results. They are
registered.

| Page | Functional results explained |
| --- | --- |
| [Adler-32](adler32.md), [CRC-32](crc32.md) | The checksum values and the combination formulas |
| [Decode tables](inftrees.md), [Fast decoding](inffast.md) | The table entries are the canonical code; a round of the fast loop decodes one token of the format |
| [Stream decoding](inflate.md) | `Goal.inflate`, the full contract of one call (`inflate_public`) |
| [Stream compression](deflate.md) | `Goal.deflate`, the full contract of one call (`Zlib.Deflate.Universal.deflate_safety`) |
| [The default-configuration engine](deflate-default-engine.md) | For the default configuration: a completed stream decodes to its input (`DeflateCore.correct`) |

## The shape of a component page

The pages for `inflate.c`, `inffast.c`, `inftrees.c`, `deflate.c` and `trees.c` follow one
outline. A page leaves out a section that has no content for its file, and some pages add
sections of their own.

1. **Results.** The theorems, their modules and their levels.
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

They name obligations and facts. They are not a status.

A bound that depends on the widths, tables or allocator of the default build holds for that
build only. The integer and pointer rules of the model are in
[translation semantics](../design/translation.md).

The [evidence index](../progress.md) lists every goal with its statement, its theorem and its
dependencies.
