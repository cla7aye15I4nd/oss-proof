# Patches

The verified source is zlib 1.4 (upstream commit `99623ef7`) with the six patches of this
directory applied in name order. Every theorem is about that patched source. This page says what
each patch changes, why, and where it stands with upstream.

Each patch fixes an issue of zlib without whose fix a safety statement cannot be proved, or a
promise of `zlib.h` does not hold. Each is as small as the fix allows. A patch that was submitted
upstream matches the submitted fix. A patch marked **local** has not been submitted upstream. A
patch is no longer needed once the upstream branch contains the fix.

| Patch | Fixes | Upstream state (as of 2026-11-15) |
| --- | --- | --- |
| 0001 | [Relational comparison of unrelated pointers in `inflateCopy`](../docs/findings/inflate-copy-fixed/README.md) | Submitted: [PR #1369](https://github.com/madler/zlib/pull/1369). The maintainer answered "Applied" on 2026-11-06; the fix is not yet on `develop` |
| 0002 | [Signed overflow in `gzseek64` after an initial `gzungetc`](../docs/findings/gzseek-pushback-overflow/README.md) | Submitted: [PR #1361](https://github.com/madler/zlib/pull/1361), open |
| 0003 | [Stale `x.next` after a partial transparent read that then fails](../docs/findings/gzread-transparent-stale-next/README.md) | Submitted: [PR #1363](https://github.com/madler/zlib/pull/1363), open |
| 0004 | Signed overflow of the gz position `x.pos`, [reading](../docs/findings/gzread-pos-overflow/README.md) and [writing](../docs/findings/gzwrite-pos-overflow/README.md) | Local: not submitted |
| 0005 | Zero advance of an [unset](../docs/findings/gz-reset-next-uninitialised/README.md) or [dangling](../docs/findings/gz-next-dangling-after-direct-read/README.md) `x.next` | Local: not submitted |
| 0006 | [`deflateBound` too small for `Z_FIXED` at levels 1 to 3](../docs/findings/deflatebound-fixed-far-matches/README.md) | Local: not submitted |

Each linked page gives the call sequence, the run command, the sanitizer's verdict, the scope
and the fix. [Findings](../docs/findings.md) lists them in one table. Patches 0001 to 0004 fix
issues that a sanitizer reports on the real C. Patch 0005 fixes behaviour that is undefined only
by the letter of C. Patch 0006 fixes a broken promise of `zlib.h`, not undefined behaviour.

## 0001-inflate-copy-pointer-equality.patch

Avoid relational comparisons between the static fixed-code table and the state's internal code
array in `inflateCopy`. The [reproduction](../docs/findings/inflate-copy-fixed/README.md)
diagnoses the unpatched C. Without the patch the safety of `inflateCopy` cannot be proved for every
stream.

The patch exactly matches commit `300fea14353d2e2ca61210aca7c48861ded5788c` in
[upstream PR #1369](https://github.com/madler/zlib/pull/1369). The maintainer answered "Applied"
on 6 November 2026 and the pull request is closed. On 2026-11-15 the publicly fetchable `develop`
and `master` heads name `99623ef7097352da7993ba614161fd6a311e046e` ("zlib 1.4"), the commit
the patches apply to. Its `inflate.c` retains the old comparison, so the patch is still needed.

## 0002-gzseek-negative-position-overflow.patch

Avoid signed overflow in `gzseek64` after an initial `gzungetc`, which sets `state->x.pos` to -1:
the `SEEK_CUR` range check evaluated `GZ_OFF_MAX - pos` with a negative `pos`, and a `SEEK_SET`
target near `GZ_OFF_MAX` overflowed in `pos - state->x.pos`. UndefinedBehaviorSanitizer reports
both on the unpatched C. Without the patch the safety of `gzseek64` and `gzseek` cannot be
proved.

The patch is the `gzlib.c` part of [upstream PR #1361](https://github.com/madler/zlib/pull/1361)
at head `ce2248ee9750`. The `test/example.c` part of that pull request is not part of the
verified source. The pull request is open. The
[finding](../docs/findings/gzseek-pushback-overflow/README.md) gives the reproduction, which
builds the unpatched C under the sanitizers and shows the reports gone with the patches.

## 0003-gzread-partial-copy-read-error.patch

In transparent (`COPY`) mode, set `state->x.next = state->out` before `gz_load`. If `read`
supplies some bytes and then fails, `gz_load` leaves the partial count in `x.have` and returns
-1, and `gz_fetch` returned before its assignment of `x.next`. The readers then consumed the
partial bytes through a stale `x.next`: an out-of-bounds read when the previous output buffer was
exhausted. Without the patch the safety of the gz reading calls cannot be proved.

The patch is exactly the change of [upstream PR #1363](https://github.com/madler/zlib/pull/1363)
at head `37627fd3bb47`. The pull request is open. The
[finding](../docs/findings/gzread-transparent-stale-next/README.md) gives the reproduction,
which builds the unpatched C under the sanitizers and shows the report gone with the patches.

## 0004-gz-position-overflow.patch

Local: not submitted upstream.

Keep the uncompressed position `state->x.pos` within `z_off64_t`. Reading: `gz_fetch` fills the
output buffer only with bytes whose position is representable (at least one, to find the end of
the input), and `gz_read` and `gzgets` deliver no byte past `GZ_OFF_MAX`; data beyond it gives
`Z_DATA_ERROR` "position overflow". `gz_look`'s transparent COPY branch also buffers only the
room left, and records the same error when its input goes past it, so that every reading call
returns with `x.pos + x.have <= GZ_OFF_MAX`, as the `gzgetc()` macro needs
([gz-position-copy-overflow](../docs/findings/gz-position-copy-overflow.md)). Writing:
`gz_write`, the fast path of `gzputc` and `gzprintf` refuse a write that would carry the position
past `GZ_OFF_MAX`, with the same error. Findings:
[gzread-pos-overflow](../docs/findings/gzread-pos-overflow/README.md) and
[gzwrite-pos-overflow](../docs/findings/gzwrite-pos-overflow/README.md). Evidence:
UndefinedBehaviorSanitizer reports the signed overflow on x86_64 Linux for both, with
`/dev/zero` and the real `/dev/null`. The overflow after a transparent look, which the
COPY-branch bound covers, is a reading of the C. No run of the real C shows it: the history needs
about 2^63 decoded bytes. For the patched source, theorems about a constructed reader state
near `GZ_OFF_MAX` show that `gzread` leaves nothing buffered past the limit and that the next
`gzgetc` does not fault; no theorem and no retained run shows the fault in a source without the
bound. Without the patch the safety of the gz readers and writers cannot be proved. A draft of an
upstream pull request is in the read-side finding.

## 0005-gz-next-zero-advance.patch

Local: not submitted upstream.

In `gzseek64` and `gz_skip_have`, advance `state->x.next` only when the advance `n` is not zero.
With `n == 0` the field may never have been written (`gz_reset` does not set it) or may point
into a caller buffer that has been freed after a direct `gzread`; arithmetic on either is
undefined in C. No result or state changes. Findings:
[gz-reset-next-uninitialised](../docs/findings/gz-reset-next-uninitialised/README.md) and
[gz-next-dangling-after-direct-read](../docs/findings/gz-next-dangling-after-direct-read/README.md).
Evidence: undefined by the letter of C; no sanitizer reports either. A probe in the
reproductions shows the zero advance on the never-written and on the dangling value, and its
absence with the patch. The model faults on arithmetic with a dangling pointer, so without the
patch the gz reading calls cannot be proved safe. The model does not see the never-written case:
a pointer field in fresh memory is `NULL` there, and `NULL + 0` passes. That case rests on the
reading of the C and on the probe. A draft of an upstream pull request is in the finding about
the unset field.

## 0006-deflatebound-fixed-conservative.patch

Local: not submitted upstream.

In `deflateBound_z`, return one of the conservative bounds also when the strategy is `Z_FIXED`, not
only when `windowBits` or `memLevel` differ from the defaults. The tight default bound counts on a
stored block as the fallback of every block. A block that crosses a window slide has none
(`FLUSH_BLOCK_ONLY` passes `buf = NULL`), and `deflate_fast` (levels 1 to 3) takes 3-byte matches at
any distance, which cost 25 bits with fixed codes. With `Z_FIXED` the output then exceeds the bound,
and one `deflate(Z_FINISH)` call with that room returns `Z_OK`, against the promise of `zlib.h`. The
conservative bound that applies (`fixedlen` for levels 1 to 9, `storelen` for level 0, as for the
other parameter sets) allows 9 bits per byte. No other strategy and no other parameter set changes.
Finding: [deflatebound-fixed-far-matches](../docs/findings/deflatebound-fixed-far-matches/README.md).
Evidence: the reproduction returns `Z_OK` at levels 1 to 3 on the unpatched C and `Z_STREAM_END` at
every level with the patch, with and without AddressSanitizer and UndefinedBehaviorSanitizer; a
search for inputs with far matches finds no failure with the patch. It is a broken API promise,
not a memory error. Without the patch, two statements that quantify over every strategy are
false: the completeness statement of the round trip (`DeflateCompletes`) and the promise of
`deflateBound`.
