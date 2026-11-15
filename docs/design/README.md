# Design: the model, the translation and the external world

The project proves statements about an executable Lean translation of C. This section explains
what that translation is made of, where its connection to C rests on review, and how the
specifications are laid out. It is not a status report; [progress](../progress.md) holds the
status.

The required results are safety results. Architecture, translation and external I/O describe
what every safety proof rests on. The two API-model pages describe functional material, which is
kept and is not required for the safety results. One functional result is planned after the
safety results, the round trip of the default zlib stream: its conditional form is checked, and
completeness and the unconditional form are open ([architecture](architecture.md#the-layers)).

Start with [architecture](architecture.md). Then use the page that answers your question:

| Question | Read |
| --- | --- |
| How do C, the runtime, specifications and proofs fit together? What exactly is trusted? | [Architecture](architecture.md) |
| How is a C statement translated, how can I compare a translation with its C, and which forms in the translations do the accepted normalisations not cover? | [Translation](translation.md) |
| What do the file system, `errno` and `printf` look like in the model? | [External I/O](external-io.md) |
| Where are the safety goals, and what keeps them apart from the functional ones? | [Layout of the specifications](safety-functional-split.md) |
| What do the heap-free API relations describe (functional)? | [API models](api-model.md), [the families in detail](api-model-details.md) |
| Where are the preconditions of internal helpers specified? | [Internal-call specifications](../spec/internal-contracts.md) |
| Which records and pointer kinds exist? | [Generated runtime schema](../runtime-schema.md) |

The [API manual](../spec/api/README.md) describes the public calls. The
[proof guide](../proof/README.md) explains the proofs. [Checking](../checking/README.md) defines
the levels checked, registered and accepted. To judge the scope of a theorem, read
[safety](../spec/safety.md), [trusted base](../trusted-base.md) and
[deviations](../deviations.md).

[Documentation home](../README.md)
