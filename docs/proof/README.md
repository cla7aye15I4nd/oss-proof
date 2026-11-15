# Proof reference: component, page, theorem

Each page in this section explains the argument behind the theorems about one C component.
This page is the map: which page explains which theorem, where the theorem is, and what
status it has.

Three things hold for every page.

- **What is proved.** Every required safety goal of the project has a registered theorem of
  exactly its type. The pages name these theorems and their Lean modules under
  `ZlibF/Proof/`.
- **What is assumed.** Each theorem states its premises. A premise narrower than `zlib.h`
  has a row in [deviations](../deviations.md). The model itself is described in the
  [trusted base](../trusted-base.md).
- **What is open.** Nothing in the required safety set. Functional correctness is not
  planned; [progress](../progress.md#scope) lists what is not planned and why.

For a first reading, follow the [illustrated guide](../overview.md). Terms are in the
[glossary](../glossary.md).

## Status levels

[AGENTS.md](../../AGENTS.md) defines two levels. This section uses them in that sense only.

- **Checked.** The theorem is on `main` and the fast gate is green there: everything builds,
  with no `sorry` and no forbidden construct.
- **Accepted.** The theorem is also listed in `tests/audit/theorems.txt`, and the acceptance
  suite is green on a named commit.

The theorems in the table below are listed in `tests/audit/theorems.txt`. The acceptance
suite is green on commit `bde170e9` ([progress, Scope](../progress.md#scope)), so they are
accepted on that commit. Differential tests are part of that suite. They are evidence of
fidelity, not proof.

A prose argument on these pages is an explanation. It is not a checked theorem. Where a page
reads the C source and the proof does not state that reading, the text is marked
**to confirm**.

## Required and not required

The scope is safety: no undefined behaviour, no memory error, no leak, and termination, for
every documented public function of the default x86_64 Linux build, over its call sequences.
The safety goals are in `ZlibF/Spec/Safety/` and, for the gzip file interface and the
callback decoder, in `ZlibF/Spec/Public/GzSafety.lean`, `ZlibF/Spec/Public/GzRefusal.lean`
and `ZlibF/Spec/Public/Sequences.lean`.

Functional results say what a function computes: a checksum value, the decoded bytes, a
round trip. They are not required. Many were proved before the scope changed, and they stay
registered. A page says for each result whether it is safety or functional. A functional
fact that a safety proof uses stays in scope; `Goal.inflate` and `Goal.deflate`, the full
contracts of one call, are the main examples. See
[the safety and functional split](../design/safety-functional-split.md).

## The map

All module paths are under `ZlibF/Proof/`. "Sequence" means the theorem covers every
permitted history of calls, not one call.

| Component | Page | Required safety theorems | Module |
| --- | --- | --- | --- |
| `adler32.c` | [Adler-32](adler32.md) | `adler32_safety`, `adler32_z_safety`, `adler32_combine_safety`, `adler32_combine64_safety` | `public-stateless-safety.lean` |
| `crc32.c` | [CRC-32](crc32.md) | `crc32_safety`, `crc32_z_safety`, `crc32_combine_safety`, `crc32_combine64_safety`, `crc32_combine_gen_safety`, `crc32_combine_gen64_safety`, `crc32_combine_op_safety` | `public-stateless-safety.lean` |
| `zutil.c` | [Utilities and allocation](zutil.md) | `zlibVersion_safety`, `zlibCompileFlags_safety` | `public-stateless-safety.lean` |
| `inftrees.c` | [Decode tables](inftrees.md) | No public function. Internal: `inflate_table_safe`, `inflate_table_decoder_safe` | `inftrees.c.lean`, `inftrees.c.decoder-safe.lean` |
| `inffast.c` | [Fast decoding](inffast.md) | No public function. Internal: `inflate_fast_safe` | `inffast.c.final.lean` |
| `inflate.c` | [Stream decoding](inflate.md) | Sequence: `inflate_sequence_safety_public`. Per function: `inflate_safety` and the other `inflate*_safety` theorems, `inflateInit__safety`, `inflateInit2__safety`, `inflateCopy_safety`. Refusal: `inflate_refusal`. Non-vacuity: `inflate_initialisation_domain_public` | `public-inflate-sequence-safety.lean`, `public-stream-call-safety.lean`, `public-init-safety.lean`, `public-inflate-copy-safety.lean`, `public-stream-refusal.lean`, `public-inflate-init.lean` |
| `deflate.c` | [Stream compression](deflate.md) | Sequence: `deflate_sequence_safety`. Per function: `deflate_safety` and the other `deflate*_safety` theorems, `deflateInit__safety`, `deflateInit2__safety`, `deflate_copy_safety`. Refusal: `deflate_refusal`. Non-vacuity: `deflate_initialisation_domain_public` | `public-deflate-goals.lean`, `public-stream-call-safety.lean`, `public-init-safety.lean`, `public-deflate-copy.lean`, `public-stream-refusal.lean`, `public-deflate-init-domain.lean` |
| `trees.c` | [Trees and block emission](trees.md) | No public function. Its lemmas serve `deflate_sequence_safety`. The overlay room: `dynamic_overlay_large`, `dynamic_overlay_mid`, `tinyOverlayAt_256`, `tinyOverlayAt_128` | `trees.c.universal-block.lean`, `trees.c.universal-overlay-mid.lean`, `deflate.c.engine.overlay-header-ref.lean` |
| `infback.c` | [Callback decoder](callbacks.md) | Sequence: `inflate_back_sequence_safety`. Non-vacuity: `back_init_domain_public` | `infback.c.safety-fast.lean`, `public-infback-init.lean` |
| `gzlib.c`, `gzread.c`, `gzwrite.c`, `gzclose.c` | [Gzip files](gzip.md) | Sequence: `gz_sequence_safety_public`. `NULL` handle: `gz_refusal`. Non-vacuity: `gz_sequence_nonvacuity_public` | `public-gz-sequence-safety.lean`, `public-gz-refusal.lean`, `public-gz-sequence-nonvacuity.lean` |
| `compress.c` | [Safety of `compress*`](compress-safety.md) | `compress_safety`, `compress_z_safety`, `compress2_safety`, `compress2_z_safety`. Bound functions: `compressBound`, `compressBound_z` | `public-compress-safe-mid.lean`, `public-compress-bound.lean` |
| `uncompr.c` | [Safety of `uncompress*`](uncompress-safety.md) | `uncompress_safe`, `uncompress_z_safe`, `uncompress2_safe`, `uncompress2_z_safe` | `public-uncompress-safe.lean` |

Two further pages belong to the same components.

- [Buffer utilities](buffers.md) reads the C of `compress.c`, `uncompr.c` and the bound
  functions. It records the source decisions that the two safety pages rely on.
- [Proving one function](method.md) explains the method: contracts, invariants, frame,
  ownership and the diagnosis of a stuck proof.

Per-function safety goals for the 31 gz functions and the three `inflateBack` functions are
not stated yet. Until they are, the manifest `tests/audit/public-api.json` names the two
sequence goals as the safety goal of each of these functions.

## Functional results that stay

These pages also explain results that are not required. They were proved earlier and stay
registered.

| Page | Functional results explained |
| --- | --- |
| [Adler-32](adler32.md), [CRC-32](crc32.md) | The checksum values and the combination formulas |
| [Decode tables](inftrees.md), [Fast decoding](inffast.md) | The table entries implement the canonical code; a fast step refines one format token |
| [Stream decoding](inflate.md) | `Goal.inflate`, the full contract of one call (`inflate_public`) |
| [Stream compression](deflate.md) | `Goal.deflate`, the full contract of one call (`Zlib.Deflate.Universal.deflate_safety`) |
| [Deflate completion, null output](../history/deflate-completion-null-output.md), [Deflate completion, input after finish](../history/deflate-completion-input.md) | Two counterexamples to an earlier functional goal, `DeflateCompletes`. They are records of a statement correction, not required results |

[Earlier arguments and reference sources](references.md) maps an earlier development to the
present modules. It is a reuse record. It supplies no proof.

## Reading order

For decompression, read the checksum and allocation pages, then decode tables, the fast
decoder and the stream decoder. The stream decoder establishes the entry conditions of the
fast path. Table construction establishes the predicates that both decoders use.

For compression, read the checksum and allocation pages, then
[stream compression](deflate.md) for the window and the hash chains, then
[trees](trees.md) for tree construction, bit emission and the shared output and symbol
buffer. The bound on that shared buffer is part of memory safety.

The gzip file interface and the callback decoder build on the stream decoder and
compressor. Read their pages last.

## Conventions

Intervals `[a, b)` include `a` and exclude `b`. An array pointer may be formed at its
one-past position; that position may not be read. Unsigned operations wrap as in C. A proof
that needs ordinary arithmetic shows that wrapping does not change the value.

The identifiers `U1`–`U12`, `F1`–`F9` and `I-*` link the reasoning to
[safety](../spec/safety.md), [the method](method.md) and
[internal contracts](../spec/internal-contracts.md). They name obligations. They are not a
status.

A bound derived from the default build's widths, tables or allocator branch holds for that
build only. Shared integer, object and control-flow rules are in
[translation semantics](../design/translation.md). The gzip world is defined in the
[external-I/O model](../design/external-io.md).

The [evidence index](../progress.md) lists every target with its statement, proof and
dependencies.
