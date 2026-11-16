# The specification: what the theorems state

This section says what is proved, in words and with pointers to the exact Lean statements.
The project proves one property, **safety**, of every documented public function of zlib in
the default x86_64 Linux build: a call has no undefined behaviour and no memory error, it
returns, it writes only the memory its statement names, and it leaks nothing.
[Safety](safety.md) defines the four clauses and shows them on an example.

A **goal** is a Lean proposition about one function or one call sequence. The pages here
describe the goals. They do not record whether a goal is proved: a goal is checked, registered
or accepted, the [glossary](../glossary.md#status) defines the three levels, and
[progress](../progress.md#scope) is the single page for the status.

The API and format pages also describe what each function returns and what the bytes mean.
That is functional behaviour. It is not required for the safety results; the functional
theorems that are already proved stay.

## Read in this order

| Order | Document | Question it answers |
| --- | --- | --- |
| 1 | [Safety](safety.md) | What does "safe" mean, clause by clause? What do the theorems say about a call and about a sequence of calls? What does the caller owe, and where does the model fall short of C? |
| 2 | [Platform assumptions](platform.md) | Which fact about the system do the goals take as a premise? (One: no object of `2^63` bytes or more.) |
| 3 | [API contracts](api/README.md) | What may a caller pass to each function, and what does it return or change? Which goal is its safety goal, and under which premises? |
| 4 | [Internal helper contracts](internal-contracts.md) | What does a helper inside the library need from the function that calls it? |
| 5 | [Input ranges](input-configurations.md) | Which parameter ranges do internal lemmas and the colours of the progress graph refer to? The safety goals cover every input, so this page does not restrict them. |
| 6 | [Compressed-data format](format/README.md) | What do DEFLATE, zlib and gzip bytes mean, independently of the implementation? Functional; not required. |
| 7 | [Format relations](format/model.md) | How is that byte meaning written as mathematical relations? Functional; not required. |

## Where the exact statements are

The exact statements are Lean propositions under `ZlibF/Spec/`:

| Directory | Content | Required |
| --- | --- | --- |
| `ZlibF/Spec/Safety/` | The safety goals of the stream functions, the checksums, the queries and the whole-buffer functions, and the safety goals of the gzip file interface and of the callback decoder: one per function, the sequence goals, the refusal goal and the non-vacuity goals. | Yes. |
| `ZlibF/Spec/Common/` | The definitions that both kinds of goal use: calls, histories, frames, the allocation account, the invariants, the platform premise (`PlatformMemory.lean`). Also statements about internal helpers that do not use the format model. No goal about a public function is here. | It holds no goal of its own. |
| `ZlibF/Spec/Functional/` | The result contracts, the format and API models (`Format/`, `Api/`), the round-trip statements, and statements about internal helpers that use the format model. | No, except `Goal.compressBound` and `Goal.compressBound_z` ([safety, appendix](safety.md#where-the-goals-are)). |

Nothing else is directly under `ZlibF/Spec/`, except the import file `Common.lean`.
[The split](../design/safety-functional-split.md) gives the reasons and the import rules.

[Progress, Target evidence](../progress.md#target-evidence) links each goal to its exact
statement and to the theorem that proves it.

## Prose and Lean

The pages of this section are prose. They explain the goals; they are not the goals.

- When a page and a Lean statement differ, the Lean statement counts.
- Editing a page proves nothing and changes no premise. A goal is proved only by a theorem
  whose type is exactly the goal.
- Some premises are narrower than `zlib.h`. Each is explicit in the goal and has a row in
  [deviations](../deviations.md).
- A lemma about an internal helper, or about one fixed configuration, does not prove a public
  goal.

## Continue to the model and proofs

- The [model guide](../design/README.md) explains how C operations are represented.
- The [trusted base](../trusted-base.md) records what the proofs depend on and the kernel does
  not check.
- The [proof guides](../proof/README.md) explain how the goals are proved.
- The [checking guide](../checking/README.md) explains the checks behind each level.
