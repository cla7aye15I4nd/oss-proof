# Platform assumption: object size

The goals take one premise about the system: **no byte object has `2^63` bytes or more.** It
is a fact of the target platform, the default x86_64 Linux LP64 build, where no allocator
returns an object larger than `PTRDIFF_MAX`. It is not something a caller has to check. This
page states the premise, says why it is needed, and lists the goals that carry it.

Properties of the operating system, the compiler and the hardware are not proved; the
[trusted base](../trusted-base.md) lists them.

## The premise

Every byte object in the model has fewer than `2^63` bytes: buffers the caller provides,
blocks the library allocates, static arrays, and byte arrays embedded in a record.

The Lean predicate is `ZlibF.PlatformMemory.ByteObjectsFit` in
[PlatformMemory.lean](../../../ZlibF/Spec/Common/PlatformMemory.lean):

```text
for every byte object reference ref and array a:
    Space.get h ref = some a  implies  a.size < 2^63
```

| The premise says | The premise does not say |
| --- | --- |
| Each single object is below `2^63` bytes. | Anything about the sum of all allocations, or about the total length a stream processes over many calls. |
| | That a pointer is valid, initialised or in bounds. Those are separate [safety obligations](safety.md#the-obligations). |

**Why it is needed.** The difference of two pointers into one object is a `ptrdiff_t`, a
signed 64-bit integer. In an object of `2^63` bytes or more that difference can overflow,
which is undefined behaviour. With the premise, every such difference fits. The entry proofs
of the fast decoder (`inflate_fast`) derive their size facts from it.

**Where it holds without being assumed.** The model's allocator refuses a request of `2^63`
bytes or more, so every block the library allocates fits (`ByteObjectsFit.allocB`,
[Proof/PlatformMemory.lean](../../../ZlibF/Proof/PlatformMemory.lean)). For the caller's memory,
and for the heap a history starts from, the premise is assumed.
[Deviations](../deviations.md) has the row "Platform byte-object scope".

## Which goals carry it

A goal that needs the premise states it explicitly, on the heap the call starts from and on
each heap the caller hands back. A goal that does not state it holds without it.

| Goals | Where the premise is |
| --- | --- |
| One call on a stream: `Goal.<function>_safety`, `Goal.inflate_sequence_safety`, `Goal.deflate_sequence_safety` | On the heap of the call (`StreamCallDomain`, and clause 2 of `StreamSequenceSafety`). |
| An inflate history (`StreamReachable .inflate`) | Also at every earlier call of the history and after every caller edit. |
| A deflate history (`StreamReachable .deflate`) | Not on earlier heaps. A deflate stream is reachable whether or not the earlier heaps had the bound. So the deflate goals cover more histories. |
| `compress*`, `uncompress*` | A premise of `CompressorSafety`, `UncompressCountedSafe` and `UncompressSingleSafe`. |
| Gzip file interface | On the heap of each open and after every caller edit (`GzHistory`; also `GzOpenSafe` and `GzDopenSafe`). |
| Callback decoder | On the heap of each `inflateBack` call (`BackSafeReachable`, `Goal.inflate_back_sequence_safety`). The callbacks must keep it (`BackPlatform`). |
| Checksums, `zlibVersion`, `zlibCompileFlags`, init, End, copy, refusals | Not stated: these goals hold without it. `inflateEnd` and `inflateCopy` start from an inflate history, which carries it as the second row says. |

The premise is the same for every [input range](input-configurations.md). It is not a
compression parameter.

## What the premise does not cover

The model's treatment of null-pointer arithmetic is a separate limit. It is described in
[safety, null pointers](safety.md#null-pointers-and-pointer-differences) and in the
[trusted base](../trusted-base.md).
