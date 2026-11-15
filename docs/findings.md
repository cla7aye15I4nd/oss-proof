# Findings and evidence register

This page lists the confirmed issues in the pinned zlib source, then the earlier observations
that are not confirmed. The root `README.md` records each confirmed issue; this page gives the
same facts in one table and keeps the history. [Sanitizer reports](sanitizer-reports.md) lists
every retained sanitizer reproduction. [Progress](progress.md) is the sole list of current
investigations and remaining work.

A confirmed issue has an allowed call sequence, a retained reproduction, and a run of the real C
under a sanitizer. Where the evidence is weaker, the row says exactly what it is. Differential
tests and model runs are evidence, not proof about the C.

## Confirmed issues in the pinned source

The pin is `757f0527` on upstream `develop`. Upstream state was read on 2026-11-14.

| Issue | Description | Reproduction | Confidence and scope | Upstream and verified source |
| --- | --- | --- | --- | --- |
| `inflateCopy` compares unrelated pointers | After a default `inflateInit`, a stream stopped inside a fixed block has `lencode` in a static table. `inflateCopy` compares it relationally with the state's own array: undefined behaviour. | [inflate-copy-fixed](findings/inflate-copy-fixed/README.md), with the sanitizer report | High for the diagnosed sequence. Inside the documented use. | Fix submitted as [PR #1369](https://github.com/madler/zlib/pull/1369); the maintainer answered "Applied" on 2026-11-06. The `develop` head (`99623ef7`) does not contain it yet. Applied here as patch 0001. |
| `gzseek` after an initial `gzungetc` | `gzungetc` at position 0 makes `x.pos` -1. `gzseek64` then overflows signed arithmetic in its range checks. | [gzseek-pushback-overflow](../tests/regression/gzseek-pushback-overflow/README.md) | High: UndefinedBehaviorSanitizer reports three sites. Inside the documented use. | Fix submitted as [PR #1361](https://github.com/madler/zlib/pull/1361), open, not yet answered by the maintainer. Applied here as patch 0002. |
| `gzread` uses a stale `x.next` after a partial read | In transparent mode, `read` supplies some bytes and then fails. `gz_fetch` returns before it sets `x.next`, and the readers copy from the old pointer: a read outside the buffer. | [gzread-transparent-stale-next](../tests/regression/gzread-transparent-stale-next/README.md) | High: AddressSanitizer reports the read. Inside the documented use; it needs a read error after partial data. | Fix submitted as [PR #1363](https://github.com/madler/zlib/pull/1363), open, not yet answered by the maintainer. Applied here as patch 0003. |
| gz position overflow, reading (F-1) | The readers add to the signed position `x.pos` without a bound. On a device whose `lseek` succeeds without moving, a seek to 2^63 − 1 is accepted and the next read overflows. | [finding](findings/gzread-pos-overflow/README.md); [gzread-pos-overflow](../tests/regression/gzread-pos-overflow/README.md) | High: UndefinedBehaviorSanitizer on x86_64 Linux. Scope: such a device (Linux `/dev/zero`), in transparent mode. | Not submitted. Patch 0004 is local and pending upstream (owner's approval of 2026-11-12). |
| gz position overflow, writing (W7) | `gz_write` and `gzputc` add to `x.pos` without a bound. A transparent writer that seeks near 2^63 overflows on the next write. | [finding](findings/gzwrite-pos-overflow/README.md); [gzwrite-pos-overflow](../tests/regression/gzwrite-pos-overflow/README.md) | High: UndefinedBehaviorSanitizer on x86_64 Linux with `/dev/null`. Scope: a transparent position near 2^63. | Not submitted. Patch 0004, local and pending upstream. |
| gz position overflow after a transparent look | With the first version of patch 0004, `gz_look`'s transparent branch buffered input without the room bound, so a reader could return with `x.pos + x.have` past `GZ_OFF_MAX`, and the `gzgetc()` macro then overflows. | [finding](findings/gz-position-copy-overflow.md); model regression `tests/verification/regressions/gz-position-copy-overflow.lean` | Confirmed in the model and by reading the C. Not reproduced under a sanitizer: the history needs about 2^63 decoded bytes. | Patch 0004 covers it: the branch now uses the same room bound. Local and pending upstream. |
| `x.next` advanced by zero when unset or dangling (R-3, R-4) | `gzseek64` and `gz_skip_have` do `x.next += n` with `n == 0` when the field was never written (R-3) or points into a freed caller buffer (R-4). | [R-3](findings/gz-reset-next-uninitialised/README.md), [R-4](findings/gz-next-dangling-after-direct-read/README.md), each with a probe run | Undefined by the letter of C. No sanitizer reports either, and no misbehaviour was observed. | Not submitted. Patch 0005 is local and pending upstream (owner's approval of 2026-11-12). |
| `deflateCopy` after `deflateResetKeep` | `deflateCopy` does not copy two pending `prev` slots; a later `deflate` on the copy follows an uninitialised slot, and `longest_match` reads outside the window. | [finding](findings/deflate-copy-pending-prev/README.md); [deflate-copy-pending-prev](../tests/regression/deflate-copy-pending-prev/README.md) | High for the diagnosed sequence: AddressSanitizer and valgrind on the unmodified pin. Scope: it needs a direct call of `deflateResetKeep`, which zlib.h lists as undocumented, so it is not a bug of the documented API. | Not reported. A [report draft](findings/deflate-copy-pending-prev-report.md) exists. No patch: the proved deflate domain excludes the call ([deviations](deviations.md)). |

Two records are not zlib bugs. They are listed here so that they are not mistaken for one.

| Record | What it is | Where |
| --- | --- | --- |
| `gzprintf` with the string returned by `gzerror` | A documentation gap, not a zlib bug. Passing the string that `gzerror` returned to `gzprintf` on the same handle is a use after free: `gzprintf` frees the handle's message before it formats. zlib.h says only that later `gzerror` calls may invalidate the string. The proved domain keeps the `gzprintf` strings apart from the handle's own blocks ([deviations](deviations.md)). | [gzprintf-error-string](../tests/regression/gzprintf-error-string/README.md) |
| `deflateResetKeep` and stale hash entries | A data error (a wrong match), not a memory error, after a direct `deflateResetKeep`. Whether it is a zlib bug is **to confirm** with upstream: the function is undocumented. | [deflate-resetkeep-stale-hash](findings/deflate-resetkeep-stale-hash/README.md) |

## Earlier library observations

The table records what earlier work reported and what is retained today. A row without a
retained reproduction is unconfirmed. Readings of C still awaiting proof are **to confirm**.

| Observation | Retained source and confidence | Reported scope |
| --- | --- | --- |
| `gzsetparams` can record a change that the inner compressor did not accept | Earlier findings text reported two independent runs: 16640–16660 random bytes at level 6, a request for level 0, then 200000 zero bytes produced a still-compressed file of about 16.9 KB. The [earlier proof notes](history/proof-earlier-notes.md#gzsetparams-experiment) keep the experiment and the proposed mechanism as an unconfirmed report; the [gzip proof guide](proof/gzip.md) only points there. That historical status is not current confirmation. | Normal parameter changes; valid data can still be produced. The [contract review](checking/contract-review.md) requires a successful valid change to reach the inner compressor. |
| `crc32_combine_op` may not terminate for an arbitrary operator | Earlier findings text reported two timeout runs for `1UL << 32`; the [CRC source analysis](proof/crc32.md) records `crc32_combine_op(1, 2, 1UL << 32)` as run. No standalone reproduction is retained here. | An operator not produced by `crc32_combine_gen`. The documented generated-operator domain is distinct; this is not evidence of failure within that domain. |
| `gz_fetch` can retain a stale source pointer after a partial read followed by failure | Now confirmed: see the table above (patch 0003). The [gz analysis](proof/gzip.md) (R-2) and the [translation account](design/external-io.md) retain the cause. | Read error after some data. The ordinary file-world model does not cover every such external read sequence. |
| `gzseek` after `gzungetc` at position zero can overflow signed position arithmetic | Now confirmed: see the table above (patch 0002). The [gz analysis](proof/gzip.md) records it as R-1. | A negative logical position and large seek arithmetic. It cannot justify restricting the broad seek target. |
| `gzread` and `gzwrite` can overflow the signed position `x.pos` | Confirmed: see the table above (F-1 and W7, [patch 0004](../patches/README.md)). | A device whose `lseek` succeeds without moving, or a transparent position near 2^63. |
| Clearing an error after failed `gzflush(..., Z_FINISH)` can precede lost output | Earlier findings text reported further writes and a successful close with an empty file. The [gz analysis](proof/gzip.md) provides source context; the former long function narrative containing the reproduction is no longer present. Reported observation only. | Error recovery and writer lifetime. This does not alter the separately proved clearing effect of `gzclearerr`. |
| `inflateCopy` compares pointers into unrelated objects | Confirmed: see the table above (patch 0001). The [inflate analysis](proof/inflate.md) preserves the earlier report. | Default initialization followed by a stream stopped inside a fixed block. |
| `gzseek` past end can disagree with `gztell` and retain EOF | Earlier findings text reported a five-byte gzip file: seeking five bytes forward returned 10 while telling returned 5 and EOF stayed set; a transparent file differed. The [gz analysis](proof/gzip.md) retains position and pending-skip context. Reported API quirk; no standalone retained reproduction. | Logical position after end of input. Whether this violates the public contract needs separate review. |
| Small inflate windows can make success depend on output splitting | Earlier findings text reported a 20000-byte stream accepted with enough output room in one call but rejected with 100-byte calls for smaller windows. The [inflate API](spec/api/inflate-stream.md) states the window domain. Historical observation of documented small-window limits, not an upstream defect. | A window smaller than the stream needs. It cannot be used to claim arbitrary small windows decode every valid stream. |

## Caller-domain questions recorded earlier

The [compressor-side analysis](proof/deflate.md)
and [inflate analysis](proof/inflate.md) record these cases. Their classification
depends on what the public API permits; none is promoted here to a confirmed defect.

| Case | Historical question and evidence boundary |
| --- | --- |
| Null length pointers in `compress2` and `uncompress2` | Compatibility wrappers read scalar cells before the `_z` checks. A null-read witness is now retained in the [allocation regression](../tests/regression/compress-allocation/README.md). A diagnosed null read does not establish that the caller was permitted to pass NULL. |
| `deflateCopy(&s, &s)` | Reported loss of the old owned state; whether identical source and destination are admitted requires contract review. |
| `inflateGetHeader(strm, NULL)` | Reported null dereference; the null-header caller domain needs review. |
| `gz_header` extra buffer during inflate | EXTRA's `zmemcpy` is undefined when the `extra` buffer overlaps the unread input, and writes past `extra_max` when the caller lowers `extra_len` inside the extra field. Both reproduced with sanitizers in the [extra-field regression](../tests/regression/inflate-gzip-extra/README.md). zlib.h does not say whether either layout is permitted; `Goal.inflate` excludes both through `ActiveHeader` ([deviations](deviations.md)). |
| `deflateSetDictionary` and `total_in` | Dictionary bytes contribute to the counter. The earlier interpretation of “input bytes” may have excluded them; documentation meaning and operational refinement must be distinguished. |
| Late `deflatePrime` and `deflateSetHeader` | C may accept calls outside the documented order; a later header dereference can then be invalid. Acceptance alone does not make the sequence documented use. |
| `deflateResetKeep` and preset-dictionary output | A retained history can make the next stream request a dictionary. This needs the documented reset semantics, not an assumption that every reset is a fresh history. |

## Model and specification evidence

These records concern the formalisation or its interpretation. They are not library safety findings.
The tests linked below are retained execution or diagnostic evidence; this page does not assert
that they were rerun for the documentation change.

| Record | Retained evidence | Meaning |
| --- | --- | --- |
| Late inflate memory failure can follow output | The [allocation regression](../tests/regression/compress-allocation/README.md) records a truncated zlib prefix returning `Z_MEM_ERROR` with one output byte and both stored counts. Earlier runs also recorded advanced pointers but unchanged stream totals and checksum when window allocation failed. | A memory error does not imply empty output. The [contract review](checking/contract-review.md) records the corrected utility relation and distinct init-failure versus late-failure scalar effects. |
| Consumed lookahead need not all describe a valid stream | The [deferred-distance regression](../tests/regression/inflate-deferred-distance/README.md) retains raw bytes `73 04 42 00`: one call emits `A`, and the next rejects an impossible distance without consuming more input. | The former whole-lookahead specification was too strong. The reviewed supporting-prefix condition is a model correction, not a zlib bug. |
| Negative priming values keep their low bits | The [priming regression](../tests/regression/inflate-prime/README.md) compares actual calls across signed values and boundary bit counts. | Mapping a negative value to zero was a specification error. Finite agreement is not a general refinement proof. |
| Automatic compressor storage must not consume allocation failure | The [allocation regression](../tests/regression/compress-allocation/README.md) retains failure-index, buffer and live-block observations and a mutation of the old translation. | The extra allocation was a translation bug. Null-destination pointer subtraction remains a separate C definedness question. |
| Static CRC input now has a represented address | The [positive regression](../tests/verification/regressions/crc-static-address.lean) retains the former counterexample's valid 47-byte static-table read and checks both CRC entries. | The translation-model rejection is repaired without reducing the checksum caller domain. This is not an upstream defect; general ABI and aliasing limits remain. |
| Gz state can retain a pointer into a caller buffer | The [gz analysis](proof/gzip.md) records arithmetic by zero after direct decompression and possible caller freeing (R-4). No sanitizer reports it. The [finding](findings/gz-next-dangling-after-direct-read/README.md) shows the zero advance with a probe. | The model faults on arithmetic with a dangling pointer. The local patch 0005 removes the zero advance; see the table of confirmed issues. |

The [runtime review](checking/runtime-review.md) records additional representation gaps, including
model-null fresh pointers and fixed garbage values. The [trusted base](trusted-base.md) states
the current obligations. Historical review conclusions are not complete safety or correctness proofs.
