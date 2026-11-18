# oss-proof

Machine-checked Lean 4 proofs about statement-by-statement translations of open-source C libraries:
every covered public function is free of undefined behaviour, memory errors and leaks, writes only
its stated frame, and returns, under the premises each theorem states.

## Libraries

| Library | Source | Build target | Scope & current state | Findings / patches | Status |
| --- | --- | --- | --- | --- | --- |
| [`zlib`](projects/zlib/README.md) | zlib 1.4 (`99623ef7`) + [7 patches](projects/zlib/patches/README.md) | default x86_64 Linux LP64 | 86 / 86 documented functions safe + default zlib stream round trip | [8 issues](https://www.dataisland.org/oss-proof/zlib/en/findings.html), [7 patches](projects/zlib/patches/README.md) | Done |
| [`7zip`](projects/7zip/README.md) | 7-Zip C SDK 26.00 (`d3296e39`) | portable scalar x86_64 Linux LP64 | Top-down container/BCJ2/PPMd7/LZMA2 invariants & strict ISO C17 runtime checked; C translation not done | — | Not done |
| [`libarchive`](projects/libarchive/README.md) | libarchive 3.8 (`432ab464`) | default scalar x86_64 Linux LP64 | Top-down RAR5 & 7-Zip invariants & strict ISO C17 runtime checked; C translation not done | — | Not done |
| [`zstd`](projects/zstd/README.md) | Zstandard 1.5.7 (`756e62a9`) | portable scalar x86_64 Linux LP64 (`libzstd` decoder) | Strict ISO C17 runtime checked; C translation & public decoder proofs not done | — | Not done |
| [`brotli`](projects/brotli/README.md) | Brotli 1.2 (`libbrotlidec` decoder) | portable scalar x86_64 Linux LP64 | Strict ISO C17 runtime checked; C translation & public decoder proofs not done | — | Not done |

## What it rests on

Each C library is translated to Lean statement by statement. Every undefined behaviour reachable in
ISO C17 raises an explicit fault in the translation, and the theorems prove that no fault occurs.
Lean's kernel checks every proof against the exact goal statement using only the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

Six items are trusted and not proved: the Lean kernel and the programs that check axioms and goal
types, the runtime model of memory and pointers, the hand translation from C, the pinned upstream
source and patches, the target build and external-call model, and the goal statements themselves.
Differential tests under AddressSanitizer and UndefinedBehaviorSanitizer compare each translation
byte-for-byte against the real C as evidence of fidelity, not proof.

## Not claimed

Compiler, operating-system and hardware correctness; build configurations, custom allocators or
undocumented entry points outside each theorem's stated domain; and functional correctness beyond
the functional goals explicitly proved for a library.

## Check it yourself

```bash
# Build and kernel-check zlib (largest modules need 8 to 9 GB RAM each)
lake --dir projects/zlib build --wfail ZlibF
(cd projects/zlib && lake env leanchecker --fresh ZlibF.Results)

# Run the shared verification gate (options, forbidden constructs, runtime UB policy, layers, kernel env, coverage, patches)
python3 framework/check_project.py zlib --skip-build
```

## Read more

- [oss-proof portal (English)](https://www.dataisland.org/oss-proof/en/) · [中文门户](https://www.dataisland.org/oss-proof/zh/)
- [zlib × Lean (English)](https://www.dataisland.org/oss-proof/zlib/en/) · [zlib × Lean（中文）](https://www.dataisland.org/oss-proof/zlib/zh/)
- [zlib status](https://www.dataisland.org/oss-proof/zlib/en/progress.html) · [deviations](https://www.dataisland.org/oss-proof/zlib/en/deviations.html) · [trusted base](https://www.dataisland.org/oss-proof/zlib/en/trusted-base.html) · [findings](https://www.dataisland.org/oss-proof/zlib/en/findings.html)
