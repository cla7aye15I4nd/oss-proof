# Documentation

This directory holds the sources of the documentation website. This page says where to start
reading and how the sources become the site.

The [documentation website](https://www.dataisland.org/zlib-f/) is the published
reading home. The files here are its content sources. The site is published from the `main`
branch only; pushes to `dev` and pull requests are built and checked, not published. So the site
can be behind `dev`. Every page ends with the commit and date it was built from.

## Where to start

- [Overview](overview.md): what is proved, what is assumed, and how the proof is built.
- [Results and status](progress.md#scope): the one page that records status. The three planned
  safety results, their level (checked, registered, accepted) with the commit, and what is not
  planned. The website shows the same
  facts on its home page and on a status page.
- [Coverage by function](coverage.md): the safety theorem of each function and its domain.
- [Deviations](deviations.md): what a call must satisfy to be covered, as a checklist by function.
- [Trusted base](trusted-base.md) and [model limits](model-limits.md): the six things the kernel
  does not check, and the limits of the model.
- [Glossary](glossary.md): the terms used in the specifications and proofs.
- [Contributing](checking/contributing.md): numbered steps and commands.

## Read the zlib articles {#articles}

1. [A complete codec: LZ77 and Huffman](articles/foundations.en.md).
2. [Implementing and optimizing zlib](articles/optimizations.en.md).
3. [Extending zlib: streams and integrity](articles/features.en.md).

Each article is available in English and Chinese. The algorithm series explains
zlib itself; formal verification has its own reference material below.

## Reference {#reference}

- [Specifications](spec/README.md): platform scope, safety, input ranges, public
  API contracts, internal helper contracts and compressed-byte meaning.
- [Model](design/README.md): translation, memory semantics and external I/O.
- [Implementation arguments](proof/README.md): verification method and detailed
  reasoning for the C components.
- [Checking](checking/README.md): what each check establishes, and how a result becomes accepted.
- [Verification policy](anti-cheating.md): which ways of cheating the acceptance suite stops.
- [Evidence index](progress.md): every target with its statement, proof and dependencies.

[Findings](findings.md) records confirmed source reports and their scope.
[Sanitizer reports](sanitizer-reports.md) lists every sanitizer reproduction and the premise that excludes it.
[Runtime schema](runtime-schema.md) is the field and type reference.

## History {#history}

The pages under `history/` are dated records, kept unchanged. They describe the time they were
written: their states, counts and hours are not current facts. Current status is only in
[progress](progress.md).

- Proof skeletons, the top-down plans of the four core proofs:
  [inflate](history/skeleton-inflate.md), [deflate](history/skeleton-deflate.md),
  [gzip file interface](history/skeleton-gz.md),
  [callback decoder](history/skeleton-inflate-back.md).
- Progress and overview: [progress checkpoints](history/progress-checkpoints.md),
  [earlier work order and readiness notes](history/next-work-and-readiness.md),
  [overview changelog](history/overview-changelog.md).
- Coverage: [review record](history/coverage-review-record.md),
  [earlier open items](history/coverage-open-items.md).
- Specifications: [specification review records](history/specification-review.md),
  [plan of the safety and functional split](history/safety-functional-split-plan.md),
  [internal deflate proof scopes](history/deviations-internal-scopes.md).
- Corrected statements of the earlier goal `DeflateCompletes`:
  [new input after FINISH](history/deflate-completion-input.md),
  [NULL output](history/deflate-completion-null-output.md).
- Proof notes: [earlier proof notes](history/proof-earlier-notes.md),
  [earlier notes on what a functional proof needs](history/proof-functional-notes.md),
  [earlier arguments and reference sources](history/references.md).
- Review records from the time of the lock files:
  [local proof registration checks](history/registration-review.md),
  [public query registration review](history/query-registration-review.md),
  [reviewed recursive execution helpers](history/compiler-helper-review.md).

## Build and preview {#local}

Article sources live in `articles/`. The website builder, interactions, styles and
tests live in `web/`. API return tables live in the same `spec/api/` source files
as their complete contracts. English sources and adjacent `.zh.md` files each
have one maintained version; pages and function views are generated from them.
See the website guide, `web/README.md`, for dependencies and build instructions.
