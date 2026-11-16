# Safety goals and functional goals

A goal is a Lean proposition about zlib. There are two kinds. A **safety goal** says that a call
returns with no undefined behaviour, no memory error and no leak, and that it terminates. A
**functional goal** says what the call computes. The results of the project are the safety
goals. This page says how the two kinds are kept apart, what form a safety goal has for each
group of functions, and which statements are functional. Which goals are done is on the
[status page](../progress.md).

## A safety goal uses no functional specification

The statement of a safety goal uses the translation of the C, the runtime, and definitions that
both kinds of goal share: calls, histories, frames, parameters, the platform premise, and the
invariants of the streams and of the gzip file handle (`Good`, `DGood`, `GzInv`). It uses no
format model, no API model and no functional contract. The Lean modules are arranged so that
this holds by construction: a module that states a safety goal, or a shared definition, imports
no module of the functional specifications, directly or through other modules. So a reader can
read every safety goal without reading a functional specification.

The goals of both kinds are stated in the specifications, and no module of the specifications
imports a proof module. So the statement of a goal is read in the specifications and in the
translation, the runtime and the mathematics they name, never in a proof. The lemmas about `Good`, `DGood` and `GzInv` are in the
proofs; their definitions are not.

A goal about a public function has the Lean name `ZlibF.Spec.Public.Goal.<name>`, whichever
kind it is.

## Two goals per public function

Each function of `zlib.h` has a safety goal and a functional goal.
[Safety, "Where the goals are"](../spec/safety.md#where-the-goals-are) lists the safety goal of
every function. The safety goals have three shapes.

- **Calls without a stream** (checksums, `zlibVersion`, `zlibCompileFlags`, `compress*`,
  `uncompress*`): on the documented domain the call returns without a fault, writes only the
  declared caller regions, and leaves the live blocks as they were.
- **Stream functions** (the inflate and deflate families): one goal per function. It states one
  more call of that function on every reachable history of a stream, and the refusal of a `NULL`
  or inconsistent stream. The four init functions need no history: their goals cover every call
  `zlib.h` allows (`InitArguments`). `Goal.inflate_refusal` and `Goal.deflate_refusal` state the
  refusals of several functions in one statement each.
- **The gzip file interface and `inflateBack`**: one goal per function as well. Each restricts a
  clause of the sequence goal of its family, `Goal.gz_sequence_safety` or
  `Goal.inflate_back_sequence_safety`, to one function. It also has the refusals of that
  function: a `NULL` handle for a gz function that takes a handle; a `NULL` stream and a stream
  record with a `NULL` state for `inflateBack` and `inflateBackEnd`, and for `inflateBackEnd`
  also a `NULL` `zfree`. `Goal.inflateBackInit__safety` covers every call `zlib.h` allows, as the
  other init goals do. No function shares a safety goal with another.

Special cases:

- `compressBound` and `compressBound_z` have their full contracts, `Goal.compressBound` and
  `Goal.compressBound_z`, as safety goals. Their translations are pure functions with no heap
  and no fault, so a separate safety goal would hold by definition.
- The functions that `zlib.h` lists as undocumented have no safety goal; `gzopen_w` among them
  is not in the default build. The exception is `gzvprintf`, which has `Goal.gzvprintf_safety`.
- The four `uncompress*` goals end in `_safe`; every other one-function safety goal ends in
  `_safety`.

A stream goal is only as strong as its set of reachable histories. Four non-vacuity goals give
a reachable witness for each family: `Goal.inflate_initialisation_domain`,
`Goal.deflate_initialisation_domain`, `Goal.inflate_back_initialisation_domain` and
`Goal.gz_sequence_nonvacuity`. A fifth, `Goal.inflateBack_call_domain`, gives a witness for the
callback protocol: a goal over every protocol is only as strong as the set of protocols.
`Goal.gz_initialisation_domain` is not one of them: it states the functional contract of
`gzopen`.

## What is functional

- The result contract of each function, `Goal.<function>`, those of the gzip file interface
  included.
- The full sequence contracts `Goal.inflate_sequence`, `Goal.deflate_sequence`,
  `Goal.inflate_back_sequence` and `Goal.gz_sequence`. Each joins the sequence safety of its
  family with functional clauses.
- The format model and the API model with their goals. The goals named
  `ZlibF.Spec.Api.Goal.<name>`, for example `ZlibF.Spec.Api.Goal.roundtrip`, are statements about
  the API model, not about the translated C, except `compress_bound_value` and
  `compress2_z_first_alloc_failure`, which are about the translated `compress.c`. The goals named
  `ZlibF.Spec.Token.Goal.<name>` are statements about the token format of the format model.
- Statements about internal functions that use the format model, such as those about the decode
  tables and the fast decoder that speak of decoded bytes, and those about CRC-32 that name
  `crc32Update` of the format model. A statement about an internal function that uses no format
  model is shared, not functional.

No statement was weakened to separate the two kinds: the full contract `Goal.X` is the
functional goal of `X`, and the safety goal is stated beside it.

The round trip of the default zlib stream has no goal definition yet. Its conditional form is a
theorem, `deflate_inflate_roundtrip`, which [architecture](architecture.md#the-layers) states.

[Design](README.md) · [Documentation home](../README.md)
