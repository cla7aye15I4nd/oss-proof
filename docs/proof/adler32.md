# Adler-32: bounded sums and modular refinement

Source: the pinned `zlib/adler32.c`; translation: `ZlibF/Zlib/adler32.c.lean`.
The mathematical contract is `F-adler-incremental` in the
[format guide](../spec/format/README.md). The [API page](../spec/api/checksums.md)
specifies null buffers, wrappers and combination operations.

The Adler-32 functions are safe on their documented domain, and they return the
Adler-32 value. This page explains the argument for `adler32_z`, which the other
entries reduce to.

## What is proved

| Result | Kind | Theorem | Module |
| --- | --- | --- | --- |
| `Goal.adler32_safety`, `Goal.adler32_z_safety`, `Goal.adler32_combine_safety`, `Goal.adler32_combine64_safety` (`ZlibF/Spec/Safety/Checksums.lean`) | Safety, required | `adler32_safety`, `adler32_z_safety`, `adler32_combine_safety`, `adler32_combine64_safety` | `ZlibF/Proof/public-stateless-safety.lean` |
| `Goal.adler32`, `Goal.adler32_z` | Functional, stays | `adler_public`, `adler_z_public` | `ZlibF/Proof/public-adler-update.lean` |
| `Goal.adler32_combine`, `Goal.adler32_combine64` | Functional, stays | `combine_public`, `combine64_public` | `ZlibF/Proof/public-adler-combine.lean` |
| The local execution results behind them | Both | `adler32_z_safe`, `adler32_z_correct`, `adler32_z_correct_ne_one`, `adler32_combine_safe`, `adler32_combine_correct` | `ZlibF/Proof/adler32.c.lean` |

All of these are registered in `tests/audit/theorems.txt` and accepted on commit
`bde170e9` ([progress, Scope](../progress.md#scope)).

A safety goal says that the call returns without a fault and leaves the heap
exactly as it was. Each safety theorem is the full contract of the same function
with the value forgotten. So the value argument below is functional: it was
proved earlier and it stays, but only its no-fault part is required.

## What is assumed

The buffer is a readable range of `len` bytes, or `NULL` with `len = 0`
(`AdlerBufferBytes`). `zlib.h` also admits `NULL` with a nonzero length, where
the C returns 1 without reading. That narrowing has a row in
[deviations](../deviations.md). The combination functions have no premise: they
are safe for every argument, also forged checksums and negative lengths.

## What a byte step preserves

Write `B = 65521` and `NMAX = 5552`. Split the input accumulator into
`a = adler & 0xffff` and `s = (adler >> 16) & 0xffff`. The mathematical step for a
byte `b` is

```
α' = (α + b) mod B
σ' = (σ + α') mod B
```

The unreduced machine step is `a' = a + b; s' = s + a'`. If the machine sums have
not wrapped, `a ≡ α (mod B)` and `s ≡ σ (mod B)` imply the same congruences after
the step. Reduction modulo B then recovers the exact mathematical pair.

The proof therefore has two distinct parts. The safety part: the machine
traverses the right bytes without a fault. The functional part: its sums refine
the modular recurrence on the stated start-value domain.

## Reads and termination

For a non-null buffer into a live byte object, require the whole requested range
`[off, off + len)` to be readable. After consuming `k` bytes, use the invariant
that the cursor is `off + k`, the remaining count is `len₀ - k`, and `k ≤ len₀`.
Each read occurs with `k < len₀`. Each pointer increment ends at or before the
one-past position.

| Branch | Bytes consumed | Measure |
| --- | --- | --- |
| `len == 1` | One byte | No loop |
| `len < 16` | One per byte-loop body | Remaining count before the test |
| Full batch | `347 × 16 = 5552` | Remaining batch count and unrolled-group count |
| Tail | Groups of 16, then single bytes | Remaining count |

A post-decrement test can wrap a local unsigned counter on its final failed
test. The proof models that test exactly; the wrapped value is not a further
body iteration. The measures establish the translated fuel bound as well as
mathematical termination.

The one-byte fast path precedes the null-buffer check. Initialization queries
require `buf == NULL` and `len == 0`; they return 1 without reading memory. Other
calls require a readable nonnull range. The function writes no caller memory and
allocates no blocks.

## Why batches do not wrap on the default build

There are at most 5552 byte steps between reductions. After `j` such steps,
starting from 16-bit components, a convenient bound is

```
a ≤ 65535 + 255 j
s ≤ 65535 + j (65535 + 255 × 5552)
```

For `j ≤ 5552`, this gives `a ≤ 1481295` and `s ≤ 8224215375`, below `2^64`.
The default LP64 `unsigned long` additions therefore agree with ordinary natural
arithmetic. This loose bound is specific to the 64-bit argument; another word
width needs a suitable bound for its own branch.

The 16-byte unrolling preserves the byte-step invariant sixteen times. Applying
it to each full batch and tail, then reducing, gives the result packed as
`a | (s << 16)`. The shift and packing also need their machine-width bounds.

## Exact start-value scope

A normal incremental checksum starts with reduced components. The public
function also accepts an integer accumulator, so a correctness statement must
say how noncanonical components are interpreted.

In the short branch, the low component satisfies
`a ≤ 65535 + 15 × 255 = 69360 < 2B`; one conditional subtraction reduces it.
The high component is reduced modulo B. In the one-byte branch both components
receive only one conditional subtraction. Reducing the high component this way
requires the incoming `s < B`, because the new low component is below B and the
sum is then below `2B`.

Thus the recurrence argument covers arbitrary accumulator words when `len ≠ 1`
(`adler32_z_correct_ne_one`), and the one-byte case when the incoming high
component is below B (`adler32_z_correct`). The null-buffer return is a separate
case. Safety holds for every accumulator word in every branch (`adler32_z_safe`).
The public value goal `Goal.adler32_z` covers every seed: its specification
`adlerValue` describes the one-byte branch as the C computes it.

The distinction is observable. For `adler32_z(0xFFFFFFF0, "\0", 1)`, the masked
low component is 65520 and the high component is 65535. Their sum after the byte
step is 131055. One subtraction leaves 65534, and the function returns
`0xFFFEFFF0`. Full modular reduction would give a high component of 13. The call
is memory-safe; a specification that reduces every arbitrary start word gives a
different value. The counterexample is why the public value is not stated as
full modular reduction.

## Wrappers and combination

`adler32` is `adler32_z` after converting its 32-bit length argument.

The `combine` functions need a separate arithmetic proof. It expands the two
running sums for a concatenation, includes the initial-value correction and shows
that the translated reductions compute the formula. `adler32_combine_correct`
states it: for byte strings `A` and `B` with `|B| < 2^63`,
`adler32_combine64(adler32(A), adler32(B), |B|) = adler32(A ++ B)`, from the
initial value 1. `adler32_combine_safe` shows that the functions never fault, for
every argument. A negative length returns the documented sentinel.
