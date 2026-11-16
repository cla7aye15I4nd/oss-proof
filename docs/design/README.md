# Design: the model, the translation and the external world

The project proves statements about an executable Lean translation of C. This section explains
what that translation is made of and where its connection to C rests on review. It is not a
status report; [progress](../progress.md) holds the status.

The required results are safety results. Architecture, translation and external I/O describe
what every safety proof rests on. The two API-model pages describe functional material, which is
not required for the safety results. One functional result is planned: the round trip of the
default zlib stream. Its conditional form has a theorem, which
[architecture](architecture.md#the-layers) states; completeness and the unconditional form are
not done ([progress](../progress.md)).

Start with [architecture](architecture.md). Then use the page that answers your question:

| Question | Read |
| --- | --- |
| How do C, the runtime, specifications and proofs fit together? What exactly is trusted? | [Architecture](architecture.md) |
| How is a C statement translated, how can I compare a translation with its C, and which forms in the translations do the accepted normalisations not cover? | [Translation](translation.md) |
| What do the file system, `errno` and `printf` look like in the model? | [External I/O](external-io.md) |
| What do the heap-free API relations describe (functional)? | [API models](api-model.md), [the families in detail](api-model-details.md) |
| Where are the preconditions of internal helpers specified? | [Internal-call specifications](../spec/internal-contracts.md) |
| Which records and pointer kinds exist? | [Runtime schema](../runtime-schema.md) |

The [API manual](../spec/api/README.md) describes the public calls. The
[proof guide](../proof/README.md) explains the proofs. To judge the scope of a theorem, read
[safety](../spec/safety.md), [trusted base](../trusted-base.md) and
[deviations](../deviations.md).

[Documentation home](../README.md)
