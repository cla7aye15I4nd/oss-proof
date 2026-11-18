# How to read a contract

Every function has one entry in the manual. An entry has two layers. The **contract** (Pre,
Post, Effects) describes the function in words, as read from the C and `zlib.h`. The **Proof
goals** paragraph says what is proved: the safety goal and its exact conditions. This page
explains the parts of an entry and defines, once, the phrases that every Proof goals
paragraph uses.

## Entry structure

| Part | Meaning |
| --- | --- |
| C signature | The function's C name and parameter types, with declaration macros retained. |
| Purpose | The operation the caller is trying to perform. |
| Domain | Which values, objects and call histories this contract covers. |
| Pre | Conditions required before the call, including any checked rejection cases. |
| Post | The result and guarantees on each stated return path. |
| Effects | Reads, writes, allocations, frees, file operations and borrowed storage. |
| Edges or errors | Cases such as empty input, partial output and refusal that change how to use the result. |
| Proof goals | The required safety goal with the conditions of its Lean statement, and the functional goal, which is not planned. |

The contracts are **focused**: a focused contract describes ordinary correct use, so its Pre
is deliberately narrower than what the function accepts. A case outside Pre that the C still
handles appears under Errors, Edges or "Outside focused scope". Outside Pre does not mean
undefined behaviour in C. The safety goal usually covers those cases as well; **Proof goals**
says exactly what it covers.

An error return does not generally undo work. Output, pointer advances, length cells or file
position can already have changed. Follow the stated return path and effects. In particular,
a decoding allocation failure can follow partial output.

## Reading a Proof goals paragraph

A Proof goals paragraph has the same five items, in this order, on every page of the manual.
An entry whose function has no required goal says so in one sentence in their place.

| Item | Content |
| --- | --- |
| **Goal** | The name of the Lean goal and whether it is required; then the theorem whose type is exactly the goal. Each name links to its Lean source. |
| **Applies when** | The conditions of the goal, in C terms, numbered. The Lean name of each is in parentheses. A call that breaks one is not covered: it is neither proved safe nor claimed to be unsafe. |
| **Covered without condition** | What the goal quantifies over freely, for example every value of a scalar argument, every input byte sequence and every allocation outcome. |
| **Guarantees** | What the goal concludes, always in this order: the call returns; the state after the call; what was written; the allocations. |
| **Not in this goal** | Cases that no clause of the goal covers: those that another goal states, those that no goal covers, and what the functional goal of the function states. A functional goal is marked "not planned", and then either "a theorem proves it" or "not done". |

A goal can have more than one clause. The goals of the stream functions other than init, of the
gzip file functions that take a handle, and of `inflateBack` and `inflateBackEnd`, have a refusal
clause beside the clause for a call on a reachable stream, on a handle or on a history. "Applies
when" then says which clause each condition belongs to, and "Guarantees" keeps its order and
names the case in each item.

A **refused stream** in these paragraphs is one that the stream check of the C rejects without
reading through a bad pointer: `strm` is NULL, or it points to a readable stream record whose
`zalloc`, `zfree` or `state` is NULL, or whose `state` points to a live state of the right kind
that the check rejects (its back pointer is not this record; for inflate its mode is outside
`HEAD` .. `SYNC`; for deflate its status is not one the check accepts). The Lean names are
`RefusedInflate` and `RefusedDeflate`. A record with `zalloc` and `zfree` set whose `state` is a garbage pointer, points
to a freed state, or points to a state of the other kind is not a refused stream and not a reachable
one: no goal covers a call that takes it as its stream, or as the `source` of a copy
([deviations](../../deviations.md#note-2-refused-streams)). The init functions and the `dest` of a
copy do accept such a record.

The paragraphs use the following phrases with a fixed meaning.

| Phrase | Meaning | Lean |
| --- | --- | --- |
| **returns** | The call ends without undefined behaviour and without a memory error, and it terminates. An error code of the C, such as `Z_DATA_ERROR` or `Z_MEM_ERROR`, is a return. The six reading calls of the gzip file interface return under a read budget; without it their goals state only the first two parts ([gzip files](gz-file.md#the-safety-goal)). | the run is `.ok`: neither `Fault.ub` nor `Fault.outOfFuel` |
| **reachable stream** | A stream produced by an init call that returned `Z_OK` (on a library heap, with `zalloc` and `zfree` each `NULL` or the default function), or the destination of a copy that returned `Z_OK`, followed by any sequence of two kinds of step: a permitted call with valid arguments that returned, with any code; and a caller edit of `next_in`, `avail_in`, `next_out`, `avail_out` or of memory the stream does not own. A reachable stream uses the default allocator. | `StreamReachable` |
| **the stream's own blocks** | The state record and the buffers the library allocated for this stream: for inflate the window; for deflate the window, the two hash arrays and the pending buffer. The `z_stream` record itself is the caller's and is named separately. | `StreamOwned` |
| **the handle's own blocks** | For a gzip file handle: the handle record, its path, its error message, its buffers and its codec state. | `GzOwned` |
| **platform size bound** | Every byte object has fewer than `2^63` bytes. A fact of the platform, not a duty of the caller ([platform](../platform.md)). | `ByteObjectsFit` |
| **exact allocation account** | After the call the allocated blocks are those allocated before, plus the new blocks the stream owns, minus the blocks the stream owned and no longer owns. Nothing else is allocated or freed. This is the no-leak clause. For a gzip file handle, read "handle" for "stream". | `LiveChange` |
| **library heap** | A condition on the model's memory, not on the caller: block numbers are consistent (no live object at the next unused number or above it, one object per number) and the library's constant tables are present. | `Fresh`, `Uniq`, `LibraryGlobals` |
| **every allocation outcome** | The goal holds whichever `malloc` calls fail. | the goal quantifies over the heap, and the allocation oracle is part of it |
| **world** | What the gzip file functions see outside the process: the files, the open descriptors, `errno`, and the result of each system call. "In every world" includes every permitted result of every `open`, `read`, `write`, `lseek` and `close`. | `Fs`, well formed by `FileSystem` |

[Safety](../safety.md) explains the four clauses behind "Guarantees", with an example. The
[glossary](../../glossary.md) defines goal, history and refusal.
[Coverage by function](../../coverage.md) gives the theorem of every function in one table.

## Domain and effects are independent

A **Restricted domain** requires more than values of the parameter types. A pointer must
usually name live storage; a handle needs a legal call history; a checksum combination
may require an operator produced for the correct length.

A **Full type domain** covers every value of the parameter types in the selected build,
including specified refusals. A function covering every scalar value can still have a
restricted overall domain because its pointers must refer to valid storage. Finite versus
infinite, or bounded versus unbounded, is not the distinction.

| Effect | Meaning |
| --- | --- |
| Pure computation | Computes a result without reading caller memory or changing state. It may use fixed library constants or tables. |
| Read-only | Reads caller memory or stream state and preserves it. A borrowed result remains library-owned. |
| Stateful | May write caller destinations or library state, allocate or free storage, invoke callbacks, or perform file I/O. |

These labels describe different properties. A pure computation can have a restricted domain.
A query that writes an optional scalar result has a write effect even if its stream is unchanged.

## Example: combine two CRCs

`crc32_combine_op` avoids reading the original strings again:

```text
Domain: Restricted domain.
Pre: crc1 is the CRC of A; crc2 is the CRC of B;
     op was generated for the representable nonnegative length of B.
Post: the result is the CRC of A followed by B.
Effects: pure computation.
```

The CRC of A means `crc32` on A, started at zero. A and B are ordinary byte sequences;
no special CRC type is required. The generated operator and correct length matter even
though the call reads no caller memory. See the [checksum entries](checksums.md) for
zero and negative-length cases, and the [format relations](../format-model.md) for agreement
with the standard.

## Shared reading rules

Unless an entry states otherwise:

- The build is the default LP64 Linux static build with the default allocator.
- A readable or writable range contains the stated number of bytes for the whole call.
- A length fits its parameter type.
- A live handle was initialized, has not been closed, and is used sequentially; the caller
  does not modify the state the library owns.

**What a contract says.** Under Pre, the call terminates without undefined behaviour,
satisfies Post, and changes only the memory named under Effects. Allocation failure, partial
results and cleanup are part of that. [Shared stream rules](streams.md) give the common
ownership rules.

**What is proved.** Safety only: the goal named under **Proof goals**, under the conditions
listed there. The contract and the goal can differ:

- Where the goal's conditions are narrower than `zlib.h`,
  [deviations](../../deviations.md) has a row.
- Post describes functional behaviour: return values, output bytes, state changes. It is read
  from the C. It is **to confirm** where no theorem states it, and it is not
  required for the safety results.

[Progress](../../progress.md) says which goals are done.
