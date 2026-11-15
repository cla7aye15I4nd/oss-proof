# Findings and evidence register

This page lists what the project found in zlib itself. It keeps four groups apart: issues
confirmed by a sanitizer on the real C, issues that are undefined only by the letter of the C
standard, two broken promises of `deflateBound` that are not memory errors, and one gap that was
found in the project's own patch. Each issue has its own page with
the call sequence, the run command, the output, the severity and the fix. Later sections keep
older observations that are not confirmed.

The pinned source is commit `757f0527` of upstream `develop`. Upstream state was read on
2026-11-14. [Sanitizer reports](sanitizer-reports.md) lists every retained sanitizer reproduction,
including caller mistakes that are not zlib issues. [Patches](../patches/README.md) describes the
five patches the verified source applies. Open investigations are only in [progress](progress.md).

Differential tests, sanitizer runs and model runs are evidence, not proof about the C.

## Confirmed issues in the pinned source

An issue is **confirmed** when it has all three: a call sequence, a retained reproduction, and a
run of the real C in which a sanitizer reports it.

| Issue | Where it bites | Evidence | Upstream state |
| --- | --- | --- | --- |
| [`inflateCopy` compares unrelated pointers](findings/inflate-copy-fixed/README.md) | `inflateCopy` of a stream that has decoded a fixed block and no dynamic block after it. Documented use. No wrong result observed. | AddressSanitizer pointer-pair check, `inflate.c:1383` | [PR #1369](https://github.com/madler/zlib/pull/1369): the maintainer answered "Applied" on 2026-11-06; not on `develop`. Patch 0001 here. |
| [`gzseek` after an initial `gzungetc`](findings/gzseek-pushback-overflow/README.md) | `gzungetc` at position 0, then `gzseek`: signed overflow in `gzseek64`. Documented use. | UndefinedBehaviorSanitizer, `gzlib.c:395`, `403`, `424` | [PR #1361](https://github.com/madler/zlib/pull/1361), open, not answered. Patch 0002 here. |
| [`gzread` copies from a stale `x.next`](findings/gzread-transparent-stale-next/README.md) | Transparent read; `read()` returns some bytes, then fails: heap read outside the output buffer. Documented use. | AddressSanitizer, `gzread.c:369` | [PR #1363](https://github.com/madler/zlib/pull/1363), open, not answered. Patch 0003 here. |
| [gz position overflow, reading](findings/gzread-pos-overflow/README.md) | Transparent read after a seek to near 2^63 on a device whose `lseek` succeeds without moving (Linux `/dev/zero`). Documented use. | UndefinedBehaviorSanitizer on x86_64 Linux, in `gz_read`, `gzgetc` and the `gzgetc()` macro | Not submitted. Local patch 0004 here. |
| [gz position overflow, writing](findings/gzwrite-pos-overflow/README.md) | Transparent write after a forward seek to near 2^63 on a sink that accepts it (`/dev/null`). Documented use. | UndefinedBehaviorSanitizer, `gzwrite.c:230`, `352` | Not submitted. Local patch 0004 here. |
| [`deflateCopy` after `deflateResetKeep`](findings/deflate-copy-pending-prev/README.md) | A later `deflate` on the copy reads outside the window. It needs a direct call of `deflateResetKeep`, which zlib.h lists as not part of the API: not a bug of the documented API. | AddressSanitizer, `deflate.c:1511`; valgrind, `deflate.c:1555` | Not reported. A [report draft](findings/deflate-copy-pending-prev-report.md) exists. No patch: the proofs exclude the call ([deviations](deviations.md)). |

Confidence is high for each diagnosed sequence. The first five are inside the documented use of
zlib.h. Patches 0004 and 0005 are local: the project owner approved them on 2026-11-12, and they
have not been submitted upstream.

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
above, which asks for a sanitizer report. No patch is applied for either.

| Issue | Where it bites | Evidence | Upstream state |
| --- | --- | --- | --- |
| [`deflateBound` is too small for `Z_FIXED` at levels 1 to 3](findings/deflatebound-fixed-far-matches/README.md) | `windowBits` 15 with `memLevel` 8, strategy `Z_FIXED`, levels 1 to 3. For 1,000,000 input bytes the bound is 1,000,318 and the stream needs up to 1,008,570 bytes. `compress`, `compress2` and `compressBound` use the default strategy and are not affected. | `repro.c` on the pinned C, with and without AddressSanitizer and UndefinedBehaviorSanitizer. The scope comes from the statement test `tests/goals/deflate-bound`. A system zlib 1.2.12 fails at every level 1 to 9. | Not reported. Whether upstream knows it is not yet checked with upstream. |
| [`deflateBound` with a gzip extra field of length 2^32 − 2 or 2^32 − 1](findings/deflatebound-extra-len/README.md) | `deflateBound` computes `2 + extra_len` at 32 bits, so the sum wraps for these two lengths, and the bound is about 64 KiB too small. | `tests/goals/deflate-bound/bound.c`, mode `extra`, on the pinned C | Known upstream (discussion in upstream PR 1360). |

Each finding page says what the case means for the functional statements. According to them,
`DeflateCompletes` is false as stated for the first case, because it quantifies over every
strategy; and the value goals `Goal.deflateBound` and `Goal.deflateBound_z` are false for the two
lengths of the second. Neither value goal has a theorem
(`tests/audit/proved-goals.txt`).

## A gap found in the project's own patch

This was a defect of the first version of the local patch 0004, not a further defect of upstream
zlib.

| Issue | Where it bites | Evidence | State |
| --- | --- | --- | --- |
| [Position overflow after a transparent look](findings/gz-position-copy-overflow.md) | With the first version of patch 0004, `gz_look`'s transparent branch buffered input without the bound, so a reader could return with `x.pos + x.have` above `GZ_OFF_MAX`, and the `gzgetc()` macro then overflows. | A run of the Lean model on a constructed state, and a reading of the C. Not reproduced under a sanitizer: the history needs about 2^63 decoded bytes. | Closed by the second version of patch 0004 (2026-11-13). Model regression: `tests/verification/regressions/gz-position-copy-overflow.lean`. |

In the pinned source without any patch, the same history overflows earlier, in `gz_read`: that
is the confirmed issue "gz position overflow, reading".

## Labels used in other pages

The [gz proof notes](proof/gzip.md) and the history pages name six of these reports by label.

| Label | Issue |
| --- | --- |
| R-1 | `gzseek` after an initial `gzungetc` |
| R-2 | `gzread` copies from a stale `x.next` |
| R-3 | `x.next` is never written by `gz_reset` |
| R-4 | `x.next` left in the caller's buffer |
| F-1 | gz position overflow, reading |
| W7 | gz position overflow, writing |

## Records that are not zlib bugs

They are listed so that they are not mistaken for one.

| Record | What it is | Where |
| --- | --- | --- |
| `gzprintf` with the string returned by `gzerror` | A documentation gap. Passing the string that `gzerror` returned to `gzprintf` on the same handle is a use after free: `gzprintf` frees the handle's message before it formats. zlib.h says that later `gzerror` calls may invalidate the string and that closing the file makes it unavailable (`zlib.h:1793`); it does not mention `gzprintf`. The gz safety goal keeps the `gzprintf` strings apart from the handle's own blocks ([deviations](deviations.md#gzip-file-interface), row "Gz printf strings"). | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` and stale hash entries | A data error (a wrong match), not a memory error, after a direct `deflateResetKeep`. Whether it is a zlib bug is not yet checked with upstream: the function is not part of the documented API. | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

## Earlier library observations

These observations come from earlier work and are not confirmed. Each row says what is retained. Four other earlier observations became confirmed issues and are in the first table
(`inflateCopy`, `gzseek` after `gzungetc`, the stale `x.next`, the position overflow). Readings of
C that a proof has not confirmed are marked **to confirm**.

| Observation | Retained source and confidence | Reported scope |
| --- | --- | --- |
| `gzsetparams` can record a change that the inner compressor did not accept | Earlier findings text reported two independent runs: 16640–16660 random bytes at level 6, a request for level 0, then 200000 zero bytes produced a still-compressed file of about 16.9 KB. The [earlier proof notes](history/proof-earlier-notes.md#gzsetparams-experiment) keep the experiment and the proposed mechanism as an unconfirmed report; the [gzip proof guide](proof/gzip.md) only points there. | Normal parameter changes; valid data can still be produced. The [contract review](checking/contract-review.md) requires a successful valid change to reach the inner compressor. |
| `crc32_combine_op` may not terminate for an arbitrary operator | Earlier findings text reported two timeout runs for `1UL << 32`; the [CRC page](proof/crc32.md#the-hang-of-crc32_combine_op-outside-its-domain) treats `crc32_combine_op(1, 2, 1UL << 32)` as a report about the C, not as a retained run. No reproduction is retained. What is proved is about the translation: `crc32_combine_op_diverges` shows that it runs out of fuel on that call. | An operator not produced by `crc32_combine_gen`. The documented generated-operator domain is distinct; this is not evidence of failure within that domain. |
| Clearing an error after failed `gzflush(..., Z_FINISH)` can precede lost output | Earlier findings text reported further writes and a successful close with an empty file. The [gz analysis](proof/gzip.md) provides source context; the text that held the reproduction is not retained. Reported observation only. | Error recovery and writer lifetime. This does not alter the separately proved clearing effect of `gzclearerr`. |
| `gzseek` past end can disagree with `gztell` and retain EOF | Earlier findings text reported a five-byte gzip file: seeking five bytes forward returned 10 while telling returned 5 and EOF stayed set; a transparent file differed. The [gz analysis](proof/gzip.md) retains position and pending-skip context. Reported API quirk; no standalone retained reproduction. | Logical position after end of input. Whether this violates the public contract needs separate review. |
| Small inflate windows can make success depend on output splitting | Earlier findings text reported a 20000-byte stream accepted with enough output room in one call but rejected with 100-byte calls for smaller windows. The [inflate API](spec/api/inflate-stream.md) states the window domain. Historical observation of documented small-window limits, not an upstream defect. | A window smaller than the stream needs. It cannot be used to claim arbitrary small windows decode every valid stream. |

## Caller-domain questions recorded earlier

The [compressor-side analysis](proof/deflate.md) and the [inflate analysis](proof/inflate.md)
record these cases. Their classification depends on what the public API permits; none is promoted
here to a confirmed defect.

| Case | Question and evidence boundary |
| --- | --- |
| Null length pointers in `compress2` and `uncompress2` | Compatibility wrappers read scalar cells before the `_z` checks. A null-read witness is retained in the [allocation regression](../tests/regression/compress-allocation/README.md). A diagnosed null read does not establish that the caller was permitted to pass NULL. |
| `deflateCopy(&s, &s)` | Reported loss of the old owned state. The copy safety goals assume that the destination is not the source record ([deviations](deviations.md), row "Copy destination"). |
| `inflateGetHeader(strm, NULL)` | Reported null dereference. The safety goal of `inflateGetHeader` assumes a non-`NULL` header ([deviations](deviations.md#stream-calls-inflate-and-deflate), row "Header arguments"). |
| `gz_header` extra buffer during inflate | EXTRA's `zmemcpy` is undefined when the `extra` buffer overlaps the unread input, and writes past `extra_max` when the caller lowers `extra_len` inside the extra field. Both reproduced with sanitizers in the [extra-field regression](../tests/regression/inflate-gzip-extra/README.md). zlib.h does not say whether either layout is permitted; `Goal.inflate_safety` excludes both through `ActiveHeader` ([deviations](deviations.md), row "Inflate gzip extra field"). |
| `deflateSetDictionary` and `total_in` | Dictionary bytes contribute to the counter. The earlier interpretation of “input bytes” may have excluded them; documentation meaning and operational refinement must be distinguished. |
| Late `deflatePrime` and `deflateSetHeader` | C may accept calls outside the documented order; a later header dereference can then be invalid. Acceptance alone does not make the sequence documented use. |
| `deflateResetKeep` and preset-dictionary output | A retained history can make the next stream request a dictionary. This needs the documented reset semantics, not an assumption that every reset is a fresh history. |

## Model and specification evidence

These records concern the formalisation or its interpretation. They are not library safety findings.
The tests linked below are retained execution or diagnostic evidence; this page does not assert
that they were rerun.

| Record | Retained evidence | Meaning |
| --- | --- | --- |
| Late inflate memory failure can follow output | The [allocation regression](../tests/regression/compress-allocation/README.md) records a truncated zlib prefix returning `Z_MEM_ERROR` with one output byte and both stored counts. Earlier runs also recorded advanced pointers but unchanged stream totals and checksum when window allocation failed. | A memory error does not imply empty output. The [contract review](checking/contract-review.md) records the corrected utility relation and distinct init-failure versus late-failure scalar effects. |
| Consumed lookahead need not all describe a valid stream | The [deferred-distance regression](../tests/regression/inflate-deferred-distance/README.md) retains raw bytes `73 04 42 00`: one call emits `A`, and the next rejects an impossible distance without consuming more input. | The former whole-lookahead specification was too strong. The reviewed supporting-prefix condition is a model correction, not a zlib bug. |
| Negative priming values keep their low bits | The [priming regression](../tests/regression/inflate-prime/README.md) compares actual calls across signed values and boundary bit counts. | Mapping a negative value to zero was a specification error. Finite agreement is not a general refinement proof. |
| Automatic compressor storage must not consume allocation failure | The [allocation regression](../tests/regression/compress-allocation/README.md) retains failure-index, buffer and live-block observations and a mutation of the old translation. | The extra allocation was a translation bug. Null-destination pointer subtraction remains a separate C definedness question. |
| Static CRC input has a represented address | The [positive regression](../tests/verification/regressions/crc-static-address.lean) retains the former counterexample's valid 47-byte static-table read and checks both CRC entries. | The translation-model rejection is repaired without reducing the checksum caller domain. This is not an upstream defect; general ABI and aliasing limits remain. |
| Gz state can retain a pointer into a caller buffer | The [gz analysis](proof/gzip.md) records arithmetic by zero after direct decompression and possible caller freeing. No sanitizer reports it. The [finding](findings/gz-next-dangling-after-direct-read/README.md) shows the zero advance with a probe. | The model faults on arithmetic with a dangling pointer. The local patch 0005 removes the zero advance; see the second table of this page. |

The [runtime review](checking/runtime-review.md) records additional representation gaps, including
model-null fresh pointers and fixed garbage values. The [trusted base](trusted-base.md) states
the current obligations. Historical review conclusions are not complete safety or correctness proofs.
