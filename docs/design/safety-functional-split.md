# Layout of the specifications: safety and functional

The required goals, the safety goals, are kept apart from the functional goals, so that a
reader can see the whole required target without reading any functional specification. This
page says where each kind of goal is, which import rule keeps them apart, and how the rule is
checked. The plan that led to this layout, with its steps and status, is a
[history page](../history/safety-functional-split-plan.md).

## The three directories

| Directory | Content | Required |
| --- | --- | --- |
| `ZlibF/Spec/Safety/` | Safety goals: the call returns with no `Fault.ub` and no `Fault.outOfFuel`, writes only its frame, and leaks nothing, on the documented domain | Yes |
| `ZlibF/Spec/Public/` | The definitions both kinds of goal use: calls, histories, frames, parameters. Also the goals of the gzip file interface and of `inflateBack`, safety and functional | The safety goals in it: yes |
| `ZlibF/Spec/Functional/` | Result contracts (`Goal.<function>`), the format and API models (`Format/`, `Api/`), and the round-trip statements (`Goal.*_sequence`) | No |

Every goal has the Lean name `ZlibF.Spec.Public.Goal.<name>`, whatever its directory. The
directory shows the kind; the namespace is the same for all.

The functional specifications are still built. A functional goal that has a
[registered](../checking/README.md) theorem is audited in full. A functional goal without one is
reported as open and fails no check. No statement was weakened or deleted to make this layout: a
full contract `Goal.X` is the functional goal of `X`, and the safety goal is stated beside it.

## The import rule

```mermaid
flowchart TD
  Safety["Spec/Safety: safety goals"] --> Public
  Functional["Spec/Functional: contracts, Api, Format, sequences"] --> Public
  Public["Spec/Public: calls, histories, frames, parameters"] --> Base
  Base["Zlib translations, Runtime, internal Spec modules"]
  Safety -. "forbidden, checked" .-> Functional
```

A module under `Spec/Safety/` or `Spec/Public/` does not import a module under
`Spec/Functional/`, directly or through other modules. So `Spec/Safety/`, the safety goals in
`Spec/Public/`, and what they import are the whole required target.

The script `scripts/check-spec-layers.py` walks the imports and fails on such an edge. It runs
in the fast gate (job `no-sorry`). It holds a list of the edges still allowed. The list may only
shrink, and it has one entry:

- `Public/GzState.lean` imports `ZlibF/Spec/Api/Gz.lean`, the old path of the gz model, for the
  gz mode decoder and `GzLooksGzip`.

Three more facts about imports:

- The old paths `ZlibF/Spec/Api*` and `ZlibF/Spec/Format*` are one-line modules that re-export
  the files under `Spec/Functional/`. The check counts them as functional.
- The parameter decoders that safety goals need (return codes, flush values, window and wrapper
  selection) are in `Public/Parameters.lean`, which imports no format module.
- The check forbids only functional imports. Four modules of `Spec/Public/` import a proof
  module, and the check allows that: `GzState` imports `Proof.«gzlib.c.base»`; `GzSafety` imports
  `Proof.«gz.inv-model»`, which defines `GzInv`, `ReadsFinite` and `GzStepPost`; `Initialisation`
  and `Utilities` import `Proof.«inflate.c.base»` and `Proof.«deflate.c.base»`. So part of the
  statement of a goal is read from those proof modules.

The files at the top of `ZlibF/Spec/` (`Inflate*.lean`, `PlatformMemory.lean`,
`ByteAddress.lean`, `Crc32ByteViews.lean`) are statements about internal functions, not public
goals. Three of them import a functional module (`InflateDecodeTableSemantics`,
`InflateFastBodyToken`, `InflateOutputInvariant`). No safety goal imports those three; the check
would fail if one did.

## Two goals per public function

The manifest `tests/audit/public-api.json` gives each function of `zlib.h` a `safety_goal` and a
`functional_goal`. [Safety, "Where the goals are"](../spec/safety.md#where-the-goals-are) lists
the safety goal and its file for every function. The safety goals have three shapes.

- **Calls without a stream** (checksums, `zlibVersion`, `zlibCompileFlags`, `compress*`,
  `uncompress*`): on the documented domain the call returns without a fault, writes only the
  declared caller regions, and leaves the live blocks as they were.
- **Stream functions** (the inflate and deflate families): one goal per function. It states one
  more call of that function on every reachable history of a stream. The four init functions
  need no history: their goals cover every call `zlib.h` allows (`InitArguments`). A `NULL` or
  inconsistent stream is covered by `Goal.inflate_refusal` and `Goal.deflate_refusal`.
- **The gzip file interface and `inflateBack`**: the 31 gz functions and the three `inflateBack`
  functions are proved safe through their sequence goals, `Goal.gz_sequence_safety` and
  `Goal.inflate_back_sequence_safety`. They have no separate one-function goal; the manifest
  names the sequence goal as the safety goal of each.

Special cases in the manifest:

- `compressBound` and `compressBound_z` name their full contracts as safety goals. Their
  translations are pure functions with no heap and no fault, so a separate safety goal would
  hold by definition.
- `safety_goal` is `null` for the functions `zlib.h` lists as undocumented, and for `gzopen_w`,
  which is not in the target build.
- The four `uncompress*` goals end in `_safe`; every other one-function safety goal ends in
  `_safety`. The manifest names each goal in full, so no check guesses a suffix.

A stream goal is only as strong as its set of reachable histories. Four non-vacuity goals give
a reachable witness for each family and are part of the required set:
`Goal.inflate_initialisation_domain`, `Goal.deflate_initialisation_domain`,
`Goal.inflate_back_initialisation_domain` and `Goal.gz_sequence_nonvacuity`.
`Goal.gz_initialisation_domain` is not required: it states the functional contract of `gzopen`,
and the manifest lists it under `not_planned`.

## How the required set is checked

The acceptance audit (`scripts/verification.py`) reads the required set from the manifest: the
safety goal of every documented function of the target build, plus the entries of
`safety_goals` and `nonvacuity_goals`. Each required goal needs a registered theorem of exactly
its type, with allowed axioms only. The list `open_safety` of the manifest is empty, so a missing
theorem fails the audit. [Goals](../checking/goals.md) gives the registries, the required set
and the [rules against silent removal](../checking/goals.md#shrink-only-rules) in full.

## What is not separated

- The goal definitions of the gzip file interface and of `inflateBack` are in `Spec/Public/`,
  not in `Spec/Safety/`: `Public/GzSafety.lean`, `Public/GzRefusal.lean`,
  `Public/Sequences.lean` and `Public/Domains.lean` hold the safety and non-vacuity goals; the
  `Public/Gz*.lean` files, `Public/Back.lean` and `Public/Sequences.lean` also hold the functional
  ones.
- The one allowed import edge above.
- The imports of proof modules above.

[Design](README.md) · [Documentation home](../README.md)
