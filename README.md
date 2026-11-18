# oss-proof

Machine-checked Lean 4 proofs about statement-by-statement translations of open-source C libraries:
every covered public function is free of undefined behaviour, memory errors and leaks, writes only
its stated frame, and returns, under the premises each theorem states.

## Verified libraries

| Library | Source | Build target | Public functions | Findings / patches | Status |
| --- | --- | --- | --- | --- | --- |
| [`zlib`](projects/zlib/README.md) | zlib 1.4 (`99623ef7`) + [7 patches](projects/zlib/patches/README.md) | default x86_64 Linux LP64 | 86 / 86 documented functions safe + default zlib stream round trip | [8 issues](https://www.dataisland.org/oss-proof/zlib/en/findings.html), [7 patches](projects/zlib/patches/README.md) | Done |

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
