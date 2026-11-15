# What must be proved

This is the specification section. Read it before the model and proof guides.

The required target is safety: no undefined behaviour, no memory error, no leak, and
termination, for every documented public function of the default x86_64 Linux build.
[Safety](safety.md) defines it and points to the Lean goals. The API and format pages also
describe what each function returns and what the bytes mean. That is functional behaviour:
it is not planned as a proof target, and results already proved for it stay.
[Progress](../progress.md) is the single page for status and remaining work.

## Read in this order

| Order | Document | Question it answers |
| --- | --- | --- |
| 1 | [Safety](safety.md) | What do the required goals state: no fault, termination, frame and leak ledger? Where are they in Lean? |
| 2 | [Platform assumptions](platform.md) | Which system environment, including the per-object size bound, is accepted? |
| 3 | [Input configurations](input-configurations.md) | Which fixed build and nested input ranges does a coverage colour describe? |
| 4 | [API contracts](api/README.md) | What may each caller pass, and what does each entry return or change? Which goal is its safety goal? |
| 5 | [Internal helper contracts](internal-contracts.md) | What must the real caller establish before invoking a helper? |
| 6 | [Compressed-data format](format/README.md) | What do DEFLATE, zlib and gzip bytes mean independently of the implementation? Functional; not a required target. |
| 7 | [Format relations](format/model.md) | How is that byte meaning expressed as mathematical relations? Functional; not a required target. |

API pages describe entry behaviour. Format pages describe byte meaning. Safety is
shared by both engines and every public entry. Each has one canonical home here.

## Documentary and formal statements

The exact statements are Lean propositions under `ZlibF/Spec/`:

| Directory | Content | Required |
| --- | --- | --- |
| `ZlibF/Spec/Safety/` | The safety goals. | Yes. |
| `ZlibF/Spec/Public/` | The definitions both kinds of goal use: calls, histories, frames, the ledger. Also the goals of the gzip file interface and the callback decoder, safety and functional: these modules are not split yet. | The safety goals in it, yes. |
| `ZlibF/Spec/Functional/` | The result contracts, the format and API models, and the round-trip statements. | No. |

The old paths `ZlibF/Spec/Api/` and `ZlibF/Spec/Format/` are one-line re-exports of
`ZlibF/Spec/Functional/Api/` and `ZlibF/Spec/Functional/Format/`.
[The split](../design/safety-functional-split.md) gives the reasons and the import rule.
The remaining files at the top of `ZlibF/Spec/` are internal callee contracts used by proofs.

The [target index](../progress.md) links each goal to its exact statement and proof evidence.
The documentary contracts explain the goals. A change of prose cannot discharge a goal,
change its premises or grant a coverage colour.

Some premises are narrower than the public header. Each is explicit in the goal and has a
row in [deviations](../deviations.md). A narrow internal lemma does not establish a public goal.

## Continue to the model and proofs

The [model guide](../design/README.md) explains how C operations are represented.
The [trusted base](../trusted-base.md) records assumptions and representation gaps.
The [proof guides](../proof/README.md) explain how the specifications are established.
The [checking guide](../checking/README.md) explains acceptance and registration.
