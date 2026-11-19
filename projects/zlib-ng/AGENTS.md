# Working rules (`projects/zlib-ng`)

Inherits all rules of [`../../AGENTS.md`](../../AGENTS.md), including the **Strict ISO C17 Undefined
Behaviour Policy** (no `NULL + 0`, no wild/dangling pointer `+ 0`, no `NULL - NULL`, no cross-object
pointer subtraction or comparison, and no `memcpy`/`memset` with `n == 0` on `NULL` or dangling
pointers). On any shared rule the root `AGENTS.md` is authoritative.

Goal: kernel-checked Lean 4 proofs about a faithful translation of zlib-ng 2.3.3 (`zlib-ng/`
submodule), built as the `ZLIB_COMPAT` x86_64 Linux LP64 static library with
`-DZLIB_COMPAT=ON -DWITH_OPTIM=OFF -DWITH_CRC32_CHORBA=OFF -DWITH_RUNTIME_CPU_DETECTION=OFF` (other
options at their defaults). With these options there is no SIMD code and no function table: every
`FUNCTABLE_CALL(name)` is a direct call to the generic C function (`adler32` -> `adler32_c`, `crc32` ->
`crc32_braid`). `WITH_OPTIM=OFF` alone is not enough: with run-time detection off, the default
`WITH_CRC32_CHORBA=ON` makes `crc32` call `crc32_chorba`. `tests/build-zlib-ng.sh` holds the option set
and rejects a library that contains Chorba or function-table symbols. The goal is safety (no
undefined behaviour, no memory error, termination) of every public function of `zlib.h`, plus the
functional theorems stated in `ZlibNgF/Spec/Functional/`.

Read `docs/en/overview.md` first. State the status only in `docs/{en,zh}/progress.md`, as done or
not done.

## Source

- `zlib-ng/` is the upstream submodule (`https://github.com/zlib-ng/zlib-ng`, tag `2.3.3`). Never
  modify it. The verified source is `zlib-ng/` plus `patches/*.patch` applied in name order, each
  listed in `patches/README.md`.
- Translations mirror the C layout: `zlib-ng/X.c` is `ZlibNgF/ZlibNg/X.c.lean`, `zlib-ng/X.h` is
  `ZlibNgF/ZlibNg/X.h.lean`, and `zlib-ng/arch/generic/X.c` is
  `ZlibNgF/ZlibNg/arch/generic/X.c.lean`. Each function keeps its C name, and its docstring starts
  with the C signature.
- Specifications live in `ZlibNgF/Spec/{Common,Safety,Functional}/`; proofs of public goals in
  `ZlibNgF/Proof/public-<name>.lean`; heap-free mathematics in `ZlibNgF/Math/`; the runtime in
  `ZlibNgF/Runtime/`.
- `ZlibNgF/Results.lean` pairs every goal with its theorem or lists it as not done.

## Model notes

- Static tables (`crc_table`, `x2n_table`) live in the heap and are read-only; the goals that read
  them take `CrcGlobals h`, which says they hold the constants of `crc32_braid_tbl.h`.
- Pointer-to-integer conversions (`(uintptr_t)buf`) use `Heap.baseAddr`, and every theorem holds
  for every `baseAddr` oracle.
- The braided CRC kernel reads `z_word_t` words as eight byte loads. The model does not check the
  effective-type rule (ISO C17 §6.5p7) for these word reads.

## Checking

`python3 framework/check_project.py zlib-ng` from the repository root. It includes the public API
coverage check (`scripts/verification.py`): `tests/audit/public-api.json` lists every function that
`zlib-ng/zlib.h.in` declares, each `done` (its own `Goal.<function>_safety` proved and in `required` of
`ZlibNgF/Results.lean`) or `not-done` with a reason. When a function becomes done, change its entry and add
its goals to `required`.

Differential tests: `python3 framework/run_difftest.py zlib-ng`, or
`ZLIB_NG_SRC=$PWD/zlib-ng SAN=1 bash tests/run.sh` from this directory. They compare every translated
public function (and the `zutil.c` allocation helpers) with the real patched C library on generated
inputs, then run the patch reproductions of `tests/regression/` (each shows its defect without its
patch and none with all patches). They are evidence of translation fidelity, not proof. When a new C
file is translated, add a driver (`tests/c/`, `tests/lean/Driver/`, `tests/gen/`, `tests/list.txt`,
`tests/lakefile.toml`).
