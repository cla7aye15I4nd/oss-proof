# Reverted security fixes

Each case undoes one security-relevant fix of zlib (an upstream commit, or one of the patches of
`patches/`) and checks that the defect it fixed comes back, on the real C and in the translation.
`cases.tsv` lists the cases, one row each.

```bash
bash tests/patch-reverts/run.sh                 # every case
bash tests/patch-reverts/run.sh local-0001      # some cases
ZLIB_SRC=$PWD/zlib bash tests/patch-reverts/local-0001/run.sh   # the C side of one case
```

A case is a directory named after the fix (the short commit, or `local-<patch number>`):

| File | What it is |
| --- | --- |
| `revert.patch` | the reverse change to the verified C (the pinned zlib with `patches/*.patch`) |
| `lean.patch` | the same reverse change to the translation, statement by statement |
| `trigger.c` | the documented calls that reach the defect |
| `run.sh`, `report.txt` | the C side: `trigger.c` under ASan and UBSan, with and without the revert (`c-check.sh`); its raw output on x86_64 Linux |
| `model.lean` | the same calls on the translation; it prints what `trigger.c` prints, or the fault |
| `README.md` | the fix, the calls, both verdicts, and whether the calls are inside the domain of the function's safety goal |

`run.sh` passes a case when the sanitizer reports the case's finding with the revert and nothing
without it; when `model.lean` prints exactly the output of `trigger.c` on the unmodified
translation; and when it ends in the case's fault with `lean.patch` applied. A hang (`ba829a4`) is
a run stopped by a time limit, on both sides: the model's loops end in `Fault.outOfFuel` only after
2^64 iterations. It works on copies: the repository is never modified. It needs `cc`, `gcc`,
`patch`, `tar`, `perl` and `lake`; everything it makes is in `tests/build/patch-reverts/`. The
reference platform is x86_64 Linux with GCC, where all cases pass (about four minutes): `local-0004`
needs Linux, and the pointer-pair check of clang reports on the verified source too, so the cases
that use it ask for GCC.

## Fixes that are not cases

Not detectable this way: the defect leaves no trace that a sanitizer and a safety statement can
both see.

| Fix | What it is |
| --- | --- |
| patch 0005 (`x.next += 0` on an unset or dangling pointer) | undefined by the letter of C; the model faults in the dangling case, but no sanitizer reports arithmetic by zero |
| patch 0006 (`deflateBound` under `Z_FIXED`) | a broken promise of `deflateBound`, not a memory error, so neither a sanitizer nor a safety statement detects it |

Candidates of the survey that were passed over:

| Fix | Why |
| --- | --- |
| `bbc2ccf` (missing `return` in `gzvprintf`) | the branch is unreachable at the pin: between calls the pending input stays within the first `size` bytes of the input buffer (the writer invariant of `ZlibF/Spec/Common/GzInv.lean`), so reverting the fix changes nothing |
| `f7d01aa` (`distcode` left at the static table) | confirmed, but at the same place as `local-0001` (the relocation in `inflateCopy`), so it shows nothing new |
| `0db8fd3` (window size 0 for a gzip header with `windowBits` 16 or 32) | the same mechanism as `8179479` |
| `2fd31f0` (an invalid header size stored in `wbits`) | masked by a later fix: it needs a group of four reverts, or the undocumented `inflateResetKeep` |

The replacements are `e3dc0a8`, `8a979f6` and `4346a16`.
