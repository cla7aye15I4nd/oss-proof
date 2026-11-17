# Documentation

This is the index of the documentation: where to start, and what each part is for. The
documentation says what was formally verified about zlib, what is assumed, and how the proofs
go. The [documentation website](https://www.dataisland.org/zlib-f/) shows the same pages.

## Where to start

- [Overview](overview.md): what is proved, what is assumed, and how the proof is built.
- [Status of the results](progress.md): for each result and each public function, done or not
  done, and what is not planned. It is the only page that states a status.
- [Coverage by function](coverage.md): the safety theorem of each function and its domain.
- [Deviations](deviations.md): what a call must satisfy to be covered, as a checklist by function.
- [What a done result rests on](checking/README.md): what the Lean kernel checked, and what is
  evidence but not proof.
- [Trusted base](trusted-base.md) and [model limits](model-limits.md): what the kernel does not
  check, and where the model could differ from C.
- [Glossary](glossary.md): the terms used in the specifications and proofs.

## Read the zlib articles {#articles}

1. [A complete codec: LZ77 and Huffman](articles/foundations.en.md).
2. [Implementing and optimizing zlib](articles/optimizations.en.md).
3. [Extending zlib: streams and integrity](articles/features.en.md).

Each article is available in English and Chinese. The articles explain zlib itself; formal
verification has its own reference material below.

## Reference {#reference}

- [Specifications](spec/README.md): platform scope, safety, input ranges, public API contracts,
  internal helper contracts and the meaning of the compressed bytes.
- [Model](design/README.md): the translation, memory semantics and external I/O.
- [Proofs](proof/README.md): the verification method and the argument for each C component.
- [The round trip](proof/roundtrip.md): `uncompress(compress(x)) = x` and the round trip of the
  default zlib stream, with their premises.
- [Why a green build is not enough](anti-cheating.md): why a proof that compiles is not enough,
  and what the results are guarded against.
- [Findings](findings.md): confirmed reports about zlib and their scope.
- [Runtime schema](runtime-schema.md): the field and type reference of the model's records.
