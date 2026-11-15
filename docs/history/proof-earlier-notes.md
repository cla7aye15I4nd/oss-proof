# Earlier proof notes

This page keeps paragraphs that were removed from the pages under
[`docs/proof/`](../proof/README.md) in November 2026, when every required safety goal had a
registered theorem. They were written while the proofs were
open. They describe plans, earlier developments and unconfirmed experiments. They are not
current facts, and nothing here is a result of this repository. The current argument for each
component is on its proof page.

The text below each heading is unchanged, except that links were adjusted to this directory.

## `gzsetparams` experiment

From the gzip page. The experiment was not reproduced in this repository. It is an
unconfirmed report; [progress](../progress.md) lists it among the reports to recheck.

An additional historical experiment reported `gzsetparams` returning success without applying
level 0 when the output buffer was nearly full. It wrote a variable pseudo-random prefix at
level 6, requested level 0, then wrote 200,000 zero bytes. Some resulting files remained much
smaller than a stored second segment. The proposed mechanism is an ignored `Z_BUF_ERROR`
from `deflateParams`; data remains valid and the effect concerns compression parameters.
The source ignores that result, but this experiment has not been independently reproduced in
this workspace. It remains an unconfirmed report, not a new finding or a patch justification.

## Gzip: the earlier I/O proposal

From the gzip page, section "Review boundary". The second paragraph is out of date: the
model now has the OS-call oracle that it calls a proposal.

C memory obligations include live handles, NUL-terminated path/mode/format strings, readable
or writable caller ranges, non-overlapping `memcpy` ranges and valid variadic argument types.
The runtime permits disjoint slices of one byte allocation; older distinct-block claims were
obsolete. Address-taken local bytes have temporary allocations freed on every return.
Scalar out-parameters and embedded record references use the choices described in
[external-I/O model](../design/external-io.md); those choices need their own alias and framing justification.

The older proposal quantified over arbitrary short I/O and failures, with an explicit OS
oracle and a fairness premise. The current model implements a smaller regular-file world.
Neither reading the source nor comparing that model with selected executions proves the
broader claim. Model limits are part of the public-domain review, not implicit caller promises.

## Overlay bound: earlier routes

From the trees page. The bound is now proved for every `memLevel` by the route that
[the trees page](../proof/trees.md) explains.

Earlier work explored Fibonacci growth along real Huffman paths. A deep
low-frequency leaf forces enough total weight in surrounding subtrees; a
formal depth/frequency theorem can then bound prefix emission cost.
`build_tree_fib_stmt_holds`, recorded in the earlier
`theorems_trees_fib.txt`, was the historical constructor result.
`dynFits_dynOf_of_fib` covered `memLevel` 4 and 5, and `dynFits_of_push` covered
6 through 9 in that earlier development. Reuse requires their exact frequency,
tie-breaking, depth and cost premises to be derived for this translation.
They do not establish the present whole compressor theorem.

For `memLevel` 1, 2 and 3, B is only 128, 256 and 512. The fixed-code slack is
roughly 16 to 64 bytes, and the dynamic description can consume comparable
space. Historical searches found no real-block violation and recorded a
closest case with 47 bytes free. That search is evidence, not a proof. The
historical `lowmem_lp_bound` route used linear-programming dual certificates;
checked certificates did not by themselves complete the required bridge from
real block frequencies and prefixes.

A theorem restricted to `memLevel ≥ 4` must state that premise and appear in
[deviations](../deviations.md). It cannot justify a safety claim over every
configuration permitted by `zlib.h`. The authoritative current treatment of
all overlay cases is in [progress](../progress.md).

The earlier overlay analysis included a checked case analysis for memory
levels 4 through 9 and a relaxation-based analysis for levels 1 through 3.
These different forms of evidence do not prove all actual executions. See
[the tree proof guide](../proof/trees.md) for the mathematical argument.

## Callback decoder: the migrated domain table

From the callback page. The domain of the proved theorem is on
[the callback page](../proof/callbacks.md).

The callback assumptions describe caller-supplied code. They are separate from forbidden
assumptions about library callees. A theorem that calls `inflate_fast` or `inflate_table` still
needs a theorem about that translated function.

| Condition in the migrated arguments | Boundary relative to the API |
| --- | --- |
| Default allocator or a null allocator field that init replaces | Custom allocator implementations are outside this model scope |
| Window represented by a byte block with room for `2^windowBits` bytes from its offset | The caller must supply the valid writable range |
| Callbacks allocate or free no heap blocks | Stronger than the documented lifetime requirement on returned input |
| Input callback alone writes its input blocks | A convenient ownership discipline, not a complete characterisation of every legal callback |
| Callback invariant `R` depends only on its owned blocks | Frames callback effects away from the decoder state |
| `InFinite` bounds input still deliverable | Needed for termination; the API does not promise that a callback eventually ends |

The measure `phi` combines held bits, bytes left and input still deliverable. An indefinitely
productive callback can prevent `inflateBack` from returning without causing C undefined
behaviour. A finite-input theorem must state that premise rather than claim unconditional
termination over every callback allowed by the public interface. All narrower theorem domains
must be explicit and recorded in [deviations](../deviations.md).

A table return classification does not establish bounded canonical links.
A fast theorem with separate output and history arrays does not cover output
inside the callback window. The actual caller must establish the installed-table
and copy premises on the returned heap. The historical missing-whave report
remains **to confirm**; ordinary-inflate examples do not settle this API.

## Stream decoding: the `inflateCopy` pointer comparison

From the inflate page. The comparison is now replaced by patch 0001, with a reproduction
under `docs/findings/inflate-copy-fixed/`.

A relational comparison of pointers to dynamic and static tables needs source
review under the pointer model. Historical references to an `inflateCopy`
`ub.patch` are not a patch authorization: only `patches/README.md` defines the
selected patch set.

The existing source tests whether `lencode` lies within `codes` using `>=` and `<=`.
With fixed tables these are different objects. The translation retains the comparisons and
faults; it does not implement the historical proposal `lencode == codes`. Earlier notes
recorded a sanitizer pointer-pair report for a copied stream stopped inside a fixed block,
and a clean run after that proposed change. That is historical evidence, not a reproduction
performed by this documentation revision or an applied patch.

## Method: proof size

From the method page.

Earlier work measured proof size and explored shorter proofs through generated
verification conditions. Those estimates motivate the method; they establish no
bound on the difficulty or size of the present proofs. Neither a small proof nor
a successful build substitutes for the acceptance conditions.

## Utilities, Adler-32 and CRC-32: earlier models

From the utilities, Adler-32 and CRC-32 pages.

A constant return is still an exact contract: a wrong version pointer or changed
flag bit must fail the function's proof mutant. Earlier documentation classified
these wrappers as complete in a prior model. Present results require the exact
goal, registration, mutation evidence and reviewed CI described in
[checking](../checking/README.md). See [progress](../progress.md) for that
current checkpoint.

Earlier work supplied a Lean argument for the byte algorithm. Reuse requires
checking its statement, machine widths, selected patch, execution relation and
preconditions against the present module. See [the method](../proof/method.md) for
non-vacuity and mutation requirements.

Earlier work used long entry-by-entry proofs and named results
`crc32_z_correct` and `multmodp_eq_gf2`. Those are historical references for the
algebra, not acceptance evidence for the current translated run.
