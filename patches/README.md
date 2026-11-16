# Patches

The verified source is the pinned `zlib/` submodule plus the `*.patch` files in this
directory, applied in name order. The submodule is never edited.

A patch is allowed only for a confirmed upstream bug that blocks a proof. It must be minimal,
match a fix submitted upstream, and be listed here. A patch approved by the owner may land before
its upstream submission; its entry then says it is local and pending, and it is replaced by the
upstream fix when one exists. Remove a patch once upstream incorporates the fix and the pin moves
past it.

| Patch | Fixes | Upstream state (read on 2026-11-15) |
| --- | --- | --- |
| 0001 | [Relational comparison of unrelated pointers in `inflateCopy`](../docs/findings/inflate-copy-fixed/README.md) | [PR #1369](https://github.com/madler/zlib/pull/1369): the maintainer answered "Applied" on 2026-11-06; not yet on `develop` |
| 0002 | [Signed overflow in `gzseek64` after an initial `gzungetc`](../docs/findings/gzseek-pushback-overflow/README.md) | [PR #1361](https://github.com/madler/zlib/pull/1361), open |
| 0003 | [Stale `x.next` after a partial transparent read that then fails](../docs/findings/gzread-transparent-stale-next/README.md) | [PR #1363](https://github.com/madler/zlib/pull/1363), open |
| 0004 | Signed overflow of the gz position `x.pos`, [reading](../docs/findings/gzread-pos-overflow/README.md) and [writing](../docs/findings/gzwrite-pos-overflow/README.md) | Local and pending: not submitted |
| 0005 | Zero advance of an [unset](../docs/findings/gz-reset-next-uninitialised/README.md) or [dangling](../docs/findings/gz-next-dangling-after-direct-read/README.md) `x.next` | Local and pending: not submitted |
| 0006 | [`deflateBound` too small for `Z_FIXED` at levels 1 to 3](../docs/findings/deflatebound-fixed-far-matches/README.md) | Local and pending: not submitted |

Each linked page gives the call sequence, the run command, the sanitizer's verdict, the scope
and the fix. [Findings](../docs/findings.md) lists them in one table. Patches 0001 to 0004 fix
issues that a sanitizer reports on the real C. Patch 0005 fixes behaviour that is undefined only
by the letter of C. Patch 0006 fixes a broken promise of `zlib.h`, not undefined behaviour. The labels R-1 to R-4, F-1 and W7 below are those of
[the gzip proof notes](../docs/proof/gzip.md).

## 0001-inflate-copy-pointer-equality.patch

Avoid relational comparisons between the static fixed-code table and the
state's internal code array in `inflateCopy`. The retained
[reproduction](../docs/findings/inflate-copy-fixed/README.md) diagnoses the
unpatched C. Without the patch the safety of `inflateCopy` cannot be proved for every stream.

The patch exactly matches commit
`300fea14353d2e2ca61210aca7c48861ded5788c` in
[upstream PR #1369](https://github.com/madler/zlib/pull/1369).
The maintainer answered "Applied" on 6 November 2026 and the pull request is
closed. On 2026-11-15 the publicly fetchable `develop` and `master` heads
name `99623ef7097352da7993ba614161fd6a311e046e` ("zlib 1.4"), which is the pin.
Its `inflate.c` retains the old comparison. Keep this submitted fix until the
applied commit is available on the upstream branch. Then advance the pin and
remove the patch.

## 0002-gzseek-negative-position-overflow.patch

Avoid signed overflow in `gzseek64` after an initial `gzungetc`, which sets
`state->x.pos` to -1: the `SEEK_CUR` range check evaluated `GZ_OFF_MAX - pos`
with a negative `pos`, and a `SEEK_SET` target near `GZ_OFF_MAX` overflowed in
`pos - state->x.pos`. UndefinedBehaviorSanitizer reports both on the unpatched
C. This is R-1 in [the gzip proof notes](../docs/proof/gzip.md) and blocks the
safety proof of `gzseek64` and `gzseek`.

The patch is the `gzlib.c` part of
[upstream PR #1361](https://github.com/madler/zlib/pull/1361) at head
`ce2248ee9750`. The `test/example.c` part of that pull request is not part of
the verified source. The pull request is open. The
[finding](../docs/findings/gzseek-pushback-overflow/README.md) gives the reproduction, which
builds the unpatched C under the sanitizers and shows the reports gone with the patches.

## 0003-gzread-partial-copy-read-error.patch

In transparent (`COPY`) mode, set `state->x.next = state->out` before
`gz_load`. If `read` supplies some bytes and then fails, `gz_load` leaves the
partial count in `x.have` and returns -1, and `gz_fetch` returned before its
assignment of `x.next`. The readers then consumed the partial bytes through a
stale `x.next`: an out-of-bounds read when the previous output buffer was
exhausted. This is R-2 in [the gzip proof notes](../docs/proof/gzip.md) and
blocks the safety proof of the read side.

The patch is exactly the change of
[upstream PR #1363](https://github.com/madler/zlib/pull/1363) at head
`37627fd3bb47`. The pull request is open. The
[finding](../docs/findings/gzread-transparent-stale-next/README.md) gives the reproduction,
which builds the unpatched C under the sanitizers and shows the report gone with the patches.

## 0004-gz-position-overflow.patch

Local and pending upstream: not yet submitted. Approved by the owner on 2026-11-12.

Keep the uncompressed position `state->x.pos` within `z_off64_t`. Reading: `gz_fetch` fills the
output buffer only with bytes whose position is representable (at least one, to find the end of
the input), and `gz_read` and `gzgets` deliver no byte past `GZ_OFF_MAX`; data beyond it gives
`Z_DATA_ERROR` "position overflow". `gz_look`'s transparent COPY branch also buffers only the
room left, and records the same error when its input goes past it, so that every reading call
returns with `x.pos + x.have <= GZ_OFF_MAX`, as the `gzgetc()` macro needs
([gz-position-copy-overflow](../docs/findings/gz-position-copy-overflow.md); this extension was
approved by the owner on 2026-11-13 and is local and pending upstream, like the rest of the
patch). Writing: `gz_write`, the fast path of `gzputc` and `gzprintf`
refuse a write that would carry the position past `GZ_OFF_MAX`, with the same error. Findings:
[gzread-pos-overflow](../docs/findings/gzread-pos-overflow/README.md) (F-1) and
[gzwrite-pos-overflow](../docs/findings/gzwrite-pos-overflow/README.md) (W7). Evidence:
UndefinedBehaviorSanitizer reports the signed overflow on x86_64 Linux for both, with
`/dev/zero` and the real `/dev/null`; reproductions under `tests/regression/`. The overflow after
a transparent look, which the COPY-branch bound covers, is confirmed in the model and by reading
the C; it is not reproduced under a sanitizer. This blocks the
safety proof of the gz readers and writers. A pull request draft is in the read-side finding.

## 0005-gz-next-zero-advance.patch

Local and pending upstream: not yet submitted. Approved by the owner on 2026-11-12.

In `gzseek64` and `gz_skip_have`, advance `state->x.next` only when the advance `n` is not zero.
With `n == 0` the field may never have been written (`gz_reset` does not set it: R-3) or may point
into a caller buffer that has been freed after a direct `gzread` (R-4); arithmetic on either is
undefined in C. No result or state changes. Findings:
[gz-reset-next-uninitialised](../docs/findings/gz-reset-next-uninitialised/README.md) (R-3) and
[gz-next-dangling-after-direct-read](../docs/findings/gz-next-dangling-after-direct-read/README.md)
(R-4). Evidence: undefined by the letter of C; no sanitizer reports either. A probe in the
reproductions shows the zero advance on the never-written and on the dangling value, and its
absence with the patch. The proof rule that a pointer field is written before it is read, and the
model's fault on arithmetic with a dangling pointer, block the gz reader proofs without it. A pull
request draft is in the R-3 finding.

## 0006-deflatebound-fixed-conservative.patch

Local and pending upstream: not yet submitted. Approved by the owner on 2026-11-15.

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
every level with the patch, with and without AddressSanitizer and UndefinedBehaviorSanitizer; the
far-match search of `tests/goals/deflate-bound` finds no failure with the patch. It is a broken API
promise, not a memory error. It blocks the round-trip completeness goal `DeflateCompletes` and the
`deflateBound` promise, which quantify over every strategy.
