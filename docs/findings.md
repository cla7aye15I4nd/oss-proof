# Findings: what the project found in zlib

This page lists what the project found in zlib itself. It keeps three groups apart: issues
confirmed by a sanitizer on the real C, issues that are undefined only by the letter of the C
standard, and two broken promises of `deflateBound` that are not memory errors. Each issue has
its own page with the call sequence, the run command, the output, the severity and the fix. Later
sections keep observations that are not confirmed, and behaviour that is not a zlib bug.

The pinned source is commit `99623ef7` of upstream `develop`, zlib 1.4. Upstream state is given
as of 2026-11-15. [Sanitizer reports](sanitizer-reports.md) lists every sanitizer reproduction,
including caller mistakes that are not zlib issues. [Patches](../patches/README.md) describes the
six patches the verified source applies.

Differential tests, sanitizer runs and model runs are evidence, not proof about the C.

## Confirmed issues in the pinned source

An issue is **confirmed** when it has all three: a call sequence, a reproduction, and a run of
the real C in which a sanitizer reports it.

| Issue | Where it bites | Evidence | Upstream state |
| --- | --- | --- | --- |
| [`inflateCopy` compares unrelated pointers](findings/inflate-copy-fixed/README.md) | `inflateCopy` of a stream that has decoded a fixed block and no dynamic block after it. Documented use. No wrong result observed. | AddressSanitizer pointer-pair check, `inflate.c:1383` | [PR #1369](https://github.com/madler/zlib/pull/1369): the maintainer answered "Applied" on 2026-11-06; not on `develop`. Patch 0001 here. |
| [`gzseek` after an initial `gzungetc`](findings/gzseek-pushback-overflow/README.md) | `gzungetc` at position 0, then `gzseek`: signed overflow in `gzseek64`. Documented use. | UndefinedBehaviorSanitizer, `gzlib.c:395`, `403`, `424` | [PR #1361](https://github.com/madler/zlib/pull/1361), open, not answered. Patch 0002 here. |
| [`gzread` copies from a stale `x.next`](findings/gzread-transparent-stale-next/README.md) | Transparent read; `read()` returns some bytes, then fails: heap read outside the output buffer. Documented use. | AddressSanitizer, `gzread.c:369` | [PR #1363](https://github.com/madler/zlib/pull/1363), open, not answered. Patch 0003 here. |
| [gz position overflow, reading](findings/gzread-pos-overflow/README.md) | Transparent read after a seek to near 2^63 on a device whose `lseek` succeeds without moving (Linux `/dev/zero`). Documented use. | UndefinedBehaviorSanitizer on x86_64 Linux, in `gz_read`, `gzgetc` and the `gzgetc()` macro | Not submitted. Local patch 0004 here. |
| [gz position overflow, writing](findings/gzwrite-pos-overflow/README.md) | Transparent write after a forward seek to near 2^63 on a sink that accepts it (`/dev/null`). Documented use. | UndefinedBehaviorSanitizer, `gzwrite.c:230`, `352` | Not submitted. Local patch 0004 here. |
| [`deflateCopy` after `deflateResetKeep`](findings/deflate-copy-pending-prev/README.md) | A later `deflate` on the copy reads outside the window. It needs a direct call of `deflateResetKeep`, which zlib.h lists as not part of the API: not a bug of the documented API. | AddressSanitizer, `deflate.c:1511`; valgrind, `deflate.c:1555` | Not reported. A [report draft](findings/deflate-copy-pending-prev-report.md) exists. No patch: the proofs exclude the call ([deviations](deviations.md)). |

Confidence is high for each diagnosed sequence. The first five are inside the documented use of
zlib.h. Patches 0004 and 0005 are local: they have not been submitted upstream.

## Undefined by the letter of C, no sanitizer report

These two are undefined behaviour by the wording of the C standard. No sanitizer reports either,
and no misbehaviour was observed, so they do not meet the definition of confirmed. Each page shows
the evaluation with a probe compiled into the real C.

| Issue | Where it bites | Evidence | Upstream state |
| --- | --- | --- | --- |
| [`x.next` is never written by `gz_reset`](findings/gz-reset-next-uninitialised/README.md) | `gzseek` or `gzdirect` before any output exists does `x.next += 0` on a field that was never written. | Probe run; reading of the C | Not submitted. Local patch 0005 here. |
| [`x.next` left in the caller's buffer](findings/gz-next-dangling-after-direct-read/README.md) | After a large `gzread` into a buffer the caller then frees, `gzseek` or `gzdirect` does `x.next += 0` on the dangling pointer. | Probe run; reading of the C | Not submitted. Local patch 0005 here. |

## Broken promises of `deflateBound`, not memory errors

`zlib.h` promises that one `deflate` call with `Z_FINISH`, the whole input and an output buffer
of the size `deflateBound` returned ends with `Z_STREAM_END`. In the two cases below, reproduced
on the pinned C, that call returns `Z_OK`: the bound is too small. Neither is undefined
behaviour, and the sanitizers report nothing, so they do not meet the definition of confirmed
above, which asks for a sanitizer report. The first is patched locally (patch 0006); the second is
not patched.

| Issue | Where it bites | Evidence | Upstream state |
| --- | --- | --- | --- |
| [`deflateBound` is too small for `Z_FIXED` at levels 1 to 3](findings/deflatebound-fixed-far-matches/README.md) | `windowBits` 15 with `memLevel` 8, strategy `Z_FIXED`, levels 1 to 3. For 1,000,000 input bytes the bound is 1,000,318 and the stream needs up to 1,008,570 bytes. `compress`, `compress2` and `compressBound` use the default strategy and are not affected. | A reproduction on the pinned C, with and without AddressSanitizer and UndefinedBehaviorSanitizer. The scope comes from a test of the promise on the real C over the parameters. A system zlib 1.2.12 fails at every level 1 to 9. With patch 0006 the reproduction and a search for inputs with far matches end at every level. | Not reported. Whether upstream knows it is not yet checked with upstream. Local patch 0006 here: not submitted. |
| [`deflateBound` with a gzip extra field of length 2^32 − 2 or 2^32 − 1](findings/deflatebound-extra-len/README.md) | `deflateBound` computes `2 + extra_len` at 32 bits, so the sum wraps for these two lengths, and the bound is about 64 KiB too small. | A C driver that calls `deflateBound` with these lengths, on the pinned C | Known upstream (discussion in upstream PR 1360). |

Each finding page says what the case means for the functional statements. Without patch 0006,
the completeness statement `DeflateCompletes` is false for the first case, because it quantifies
over every strategy. The value goals `Goal.deflateBound` and `Goal.deflateBound_z` are false for
the two lengths of the second case; both are not done and not planned.

## The position overflow through `gz_look`

This is not a further defect of upstream zlib. It says why the fix of the position overflow
(patch 0004) also bounds `gz_look`. Bounding the reading functions alone is not enough:
`gz_look`'s transparent branch buffers input too, and without a bound there a reader can return
with `x.pos + x.have` above `GZ_OFF_MAX`, after which the `gzgetc()` macro overflows
([finding](findings/gz-position-copy-overflow.md)).

Evidence: a run of the Lean model on a constructed state
([model check](../tests/verification/regressions/gz-position-copy-overflow.lean)), and a reading
of the C. It is not reproduced under a sanitizer: the history needs about 2^63 decoded bytes. In
the pinned source without any patch, the same history overflows earlier, in `gz_read`: that is
the confirmed issue "gz position overflow, reading".

## Records that are not zlib bugs

They are listed so that they are not mistaken for one.

| Record | What it is | Where |
| --- | --- | --- |
| `gzprintf` with the string returned by `gzerror` | A documentation gap. Passing the string that `gzerror` returned to `gzprintf` on the same handle is a use after free: `gzprintf` frees the handle's message before it formats. zlib.h says that later `gzerror` calls may invalidate the string and that closing the file makes it unavailable (`zlib.h:1793`); it does not mention `gzprintf`. The gz safety goal keeps the `gzprintf` strings apart from the handle's own blocks ([deviations](deviations.md#gzip-file-interface), row "Gz printf strings"). | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` and stale hash entries | A data error (a wrong match), not a memory error, after a direct `deflateResetKeep`. Whether it is a zlib bug is not yet checked with upstream: the function is not part of the documented API. | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

<a id="earlier-library-observations"></a>

## Unconfirmed observations

These observations of the library's behaviour are not confirmed: no reproduction is kept for any
of them. Readings of C that a proof has not confirmed are marked **to confirm**.

| Observation | What was observed | Scope |
| --- | --- | --- |
| `gzsetparams` can record a change that the inner compressor did not accept | Two independent runs: 16640–16660 random bytes at level 6, a request for level 0, then 200000 zero bytes produced a still-compressed file of about 16.9 KB. The mechanism is **to confirm**. | Normal parameter changes; valid data can still be produced. |
| `crc32_combine_op` may not terminate for an arbitrary operator | Two runs with the operator `1UL << 32` timed out. What is proved is about the translation: `crc32_combine_op_diverges` shows that it runs out of fuel on the call `crc32_combine_op(1, 2, 1UL << 32)` ([CRC proof](proof/crc32.md)). | An operator not produced by `crc32_combine_gen`. The documented generated-operator domain is distinct; this is not evidence of failure within that domain. |
| Clearing an error after failed `gzflush(..., Z_FINISH)` can precede lost output | Further writes and a successful close left an empty file. | Error recovery and writer lifetime. This does not alter the separately proved clearing effect of `gzclearerr`. |
| `gzseek` past end can disagree with `gztell` and retain EOF | On a five-byte gzip file, seeking five bytes forward returned 10 while telling returned 5 and EOF stayed set; a transparent file differed. | Logical position after end of input. Whether this violates the public contract needs separate review. |
| Small inflate windows can make success depend on output splitting | A 20000-byte stream was accepted with enough output room in one call but rejected with 100-byte calls for smaller windows. The [inflate API](spec/api/inflate-stream.md) states the window domain. This is the documented limit of small windows, not an upstream defect. | A window smaller than the stream needs. It cannot be used to claim arbitrary small windows decode every valid stream. |

## Caller-domain questions

The [compressor-side analysis](proof/deflate.md) and the [inflate analysis](proof/inflate.md)
record these cases. Their classification depends on what the public API permits; none is promoted
here to a confirmed defect.

| Case | Question and evidence boundary |
| --- | --- |
| Null length pointers in `compress2` and `uncompress2` | Compatibility wrappers read scalar cells before the `_z` checks. A [reproduction](../tests/regression/compress-allocation/README.md) shows the null read. A diagnosed null read does not establish that the caller was permitted to pass NULL. |
| `deflateCopy(&s, &s)` | Reported loss of the old owned state. The copy safety goals assume that the destination is not the source record ([deviations](deviations.md), row "Copy destination"). |
| `inflateGetHeader(strm, NULL)` | Reported null dereference. The safety goal of `inflateGetHeader` assumes a non-`NULL` header ([deviations](deviations.md#stream-calls-inflate-and-deflate), row "Header arguments"). |
| `gz_header` extra buffer during inflate | EXTRA's `zmemcpy` is undefined when the `extra` buffer overlaps the unread input, and writes past `extra_max` when the caller lowers `extra_len` inside the extra field. Both are [reproduced](../tests/regression/inflate-gzip-extra/README.md) with sanitizers. zlib.h does not say whether either layout is permitted; `Goal.inflate_safety` excludes both through `ActiveHeader` ([deviations](deviations.md), row "Inflate gzip extra field"). |
| `deflateSetDictionary` and `total_in` | Dictionary bytes contribute to the counter. Whether “input bytes” in the documentation includes them is a question of its meaning, apart from what the code does. |
| Late `deflatePrime` and `deflateSetHeader` | C may accept calls outside the documented order; a later header dereference can then be invalid. Acceptance alone does not make the sequence documented use. |
| `deflateResetKeep` and preset-dictionary output | A retained history can make the next stream request a dictionary. This needs the documented reset semantics, not an assumption that every reset is a fresh history. |

## Behaviour of zlib that a specification must respect

These records are about the real C. They are not safety findings and not zlib bugs; each one
is a behaviour that a specification of zlib has to allow. The linked tests ran the real C, and
the linked model check ran the Lean model; they are evidence, not proof.

| Behaviour | Evidence | Meaning |
| --- | --- | --- |
| A late memory failure of `inflate` can follow output | A truncated zlib prefix returns `Z_MEM_ERROR` with one output byte and both stored counts ([test](../tests/regression/compress-allocation/README.md)). | A memory error does not imply empty output. A failure at init and a late failure have different effects on the counts. |
| The input a call has consumed need not all belong to a valid stream | On the raw bytes `73 04 42 00`, one call emits `A`, and the next rejects an impossible distance without consuming more input ([test](../tests/regression/inflate-deferred-distance/README.md)). | A specification that asks every consumed byte to belong to a valid stream is too strong. |
| A negative priming value keeps its low bits | Calls of `inflatePrime` across signed values and boundary bit counts ([test](../tests/regression/inflate-prime/README.md)). | A negative value is not treated as zero. Finite agreement is not a general refinement proof. |
| The automatic stream record of `compress*` consumes no allocation attempt | Observations of the failing allocation index, the buffers and the live blocks ([test](../tests/regression/compress-allocation/README.md)). | A model of `compress*` must not count the automatic record as an allocation that can fail. Pointer subtraction with a `NULL` destination remains a separate question of C definedness. |
| A CRC input may be static data | A 47-byte read of a static table through both CRC entries ([model check](../tests/verification/regressions/crc-static-address.lean)). | The checksum caller domain includes static storage. General ABI and aliasing limits remain ([model limits](model-limits.md)). |
| Gz state can keep a pointer into a caller buffer | After direct decompression the state does arithmetic by zero on a pointer into a buffer the caller may have freed. No sanitizer reports it. The [finding](findings/gz-next-dangling-after-direct-read/README.md) shows the zero advance with a probe. | The model faults on arithmetic with a dangling pointer. The local patch 0005 removes the zero advance; see the second table of this page. |

The [trusted base](trusted-base.md) and [model limits](model-limits.md) state where the model
differs from C, including fresh pointers that read as `NULL` and one fixed value per
uninitialised integer cell.
