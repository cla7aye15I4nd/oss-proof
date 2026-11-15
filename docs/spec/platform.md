# Accepted platform assumptions

The scope is the default x86_64 Linux/LP64 static build with the default allocator.
This page states the one environment premise the goals take: no byte object has `2^63`
bytes or more. Properties of the operating system, compiler and hardware are not proved;
the [trusted base](../trusted-base.md) lists them.

## Byte-object size

Every represented byte object has fewer than `2^63` bytes. This bound is accepted
as part of the system environment. It is the LP64 `PTRDIFF_MAX` object-size limit: no allocator
returns a larger object. It covers caller-provided storage, raw byte blocks, static arrays
and embedded byte-array views.

The exact predicate is `ZlibF.PlatformMemory.ByteObjectsFit` in
[PlatformMemory.lean](../../ZlibF/Spec/PlatformMemory.lean):

```text
for every represented byte reference ref and array a:
    Space.get h ref = some a  implies  a.size < 2^63
```

It bounds each object separately. It does not bound the sum of allocations or
the total length processed across repeated calls. It is shared by the default,
common and all-supported [input ranges](input-configurations.md); it is not an
extra colour or a compression parameter.

## Where the goals use it

The premise is explicit in every safety goal that needs it. It is stated on the heap a call
starts from, and on each heap the caller hands back.

| Goals | Where the premise is |
| --- | --- |
| One call on a stream (`Goal.<function>_safety`, `Goal.inflate_sequence_safety`, `Goal.deflate_sequence_safety`) | `StreamCallDomain` and clause 2 of `StreamSequenceSafety`: on the heap of the call. An inflate history (`StreamReachable .inflate`) also has it at every call and after every caller edit. A deflate history does not carry it. |
| `compress*`, `uncompress*` | A premise of `CompressorSafety`, `UncompressCountedSafe` and `UncompressSingleSafe`. |
| Gzip file interface | `GzHistory`: on the heap of each open and after every caller edit. `GzOpenSafe` and `GzDopenSafe` take it too. |
| Callback decoder | `BackSafeReachable` and `Goal.inflate_back_sequence_safety`: on the heap of each `inflateBack` call. `BackPlatform` asks the callbacks to keep it. |
| Checksums, queries, init, end, copy, refusals | Not needed and not stated. |

The bound gives a signed 64-bit range for the difference of two valid offsets in one object.
The fast decoder's entry proofs derive their object-size facts from it.

The library's own allocations keep the premise: the runtime allocator refuses a request above
`PTRDIFF_MAX`, so a new block fits (`ByteObjectsFit.allocB`,
[Proof/PlatformMemory.lean](../../ZlibF/Proof/PlatformMemory.lean)). For caller storage and for
an arbitrary heap it is assumed, not derived. [Deviations](../deviations.md), row "Platform
byte-object scope", records it.

A goal that does not state the premise holds without it. This page adds no hypothesis to any
statement.

## Other pointer obligations

The size bound does not establish that a pointer is live, initialized, in the
same object as another pointer, or within valid offsets. Those are separate
[safety obligations](safety.md). The runtime's null-arithmetic choices remain
recorded in the [model comparison](safety.md#null-pointers-and-pointer-differences)
and [trusted base](../trusted-base.md).
