#!/usr/bin/env python3
"""Falsify candidate goals, invariants, and strict ISO C17 UB against real C before proving.

Compiles a C test harness against a temporary patched copy of a project's upstream C sources with
ASan + UBSan (`-fsanitize=address,undefined,pointer-subtract,pointer-compare
-fno-sanitize-recover=all`), `ASAN_OPTIONS=detect_invalid_pointer_pair=2`, and an optional strict
ISO C17 wrapper header (`oss_strict_c17.h`) that traps zero-length `memcpy`/`memmove`/`memset`/
`memcmp` on `NULL` pointers (ISO C17 §7.24.1p2).
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework import patches as patch_check
from framework.manifest import REPO, load_project

STRICT_C17_HEADER = r"""/* Auto-generated strict ISO C17 §7.24.1p2 zero-length NULL-pointer trap header. */
#ifndef OSS_STRICT_C17_H
#define OSS_STRICT_C17_H
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static inline void *oss_strict_memcpy(void *dst, const void *src, size_t n, const char *f, int l) {
  if (dst == NULL || src == NULL) {
    fprintf(stderr, "STRICT_C17_UB (%s:%d): memcpy(dst=%p, src=%p, n=%zu)\n", f, l, dst, src, n);
    abort();
  }
  return memcpy(dst, src, n);
}

static inline void *oss_strict_memmove(void *dst, const void *src, size_t n, const char *f, int l) {
  if (dst == NULL || src == NULL) {
    fprintf(stderr, "STRICT_C17_UB (%s:%d): memmove(dst=%p, src=%p, n=%zu)\n", f, l, dst, src, n);
    abort();
  }
  return memmove(dst, src, n);
}

static inline void *oss_strict_memset(void *dst, int c, size_t n, const char *f, int l) {
  if (dst == NULL) {
    fprintf(stderr, "STRICT_C17_UB (%s:%d): memset(dst=NULL, n=%zu)\n", f, l, n);
    abort();
  }
  return memset(dst, c, n);
}

static inline int oss_strict_memcmp(const void *a, const void *b, size_t n, const char *f, int l) {
  if (a == NULL || b == NULL) {
    fprintf(stderr, "STRICT_C17_UB (%s:%d): memcmp(a=%p, b=%p, n=%zu)\n", f, l, a, b, n);
    abort();
  }
  return memcmp(a, b, n);
}

#define memcpy(d, s, n) oss_strict_memcpy((d), (s), (n), __FILE__, __LINE__)
#define memmove(d, s, n) oss_strict_memmove((d), (s), (n), __FILE__, __LINE__)
#define memset(d, c, n) oss_strict_memset((d), (c), (n), __FILE__, __LINE__)
#define memcmp(a, b, n) oss_strict_memcmp((a), (b), (n), __FILE__, __LINE__)
#endif
"""

HARNESS_TEMPLATE = r"""/* Boundary & invariant falsification harness (public API headers only). */
#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Include ONLY the library's documented public header here, e.g.:
 * #include <zlib.h>
 */

static uint64_t rng_state = 0x9e3779b97f4a7c15ULL;
static uint64_t next_u64(void) {
  uint64_t x = rng_state;
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  rng_state = x;
  return x;
}

int main(void) {
  /* 1. Boundary cases: NULL with length 0, lengths 0/1/2/7/8/15/16/256, max sizes. */
  /* 2. Mode / level / strategy sweep (including raw, stored, huffman-only, RLE, flush modes). */
  /* 3. Randomized multi-call sequences checking your candidate invariant after every call. */
  (void)next_u64();
  puts("falsify_spec: 0 counterexamples found");
  return 0;
}
"""


def find_compiler(preferred: str | None = None) -> str:
    for cand in ([preferred] if preferred else []) + ["clang", "gcc", "cc"]:
        if cand and shutil.which(cand):
            return cand
    raise RuntimeError("no C compiler found (install clang or gcc)")


def run_falsifier(
    harness: Path,
    *,
    project_id: str | None = None,
    extra_sources: list[Path] | None = None,
    include_dirs: list[Path] | None = None,
    extra_cflags: list[str] | None = None,
    strict_c17: bool = True,
    compiler: str | None = None,
) -> int:
    cc = find_compiler(compiler)
    with tempfile.TemporaryDirectory(prefix="oss-falsify-") as raw_tmp:
        tmp = Path(raw_tmp)
        strict_hdr = tmp / "oss_strict_c17.h"
        strict_hdr.write_text(STRICT_C17_HEADER)

        inc_args: list[str] = []
        src_args: list[str] = [str(harness)]
        if project_id:
            proj = load_project(project_id, REPO)
            up_cfg = proj.data["upstream"]
            sub_dir = proj.root / up_cfg["submodule"]
            if not (sub_dir / ".git").exists():
                raise RuntimeError(
                    f"[{project_id}] upstream submodule {up_cfg['submodule']} is not initialized"
                )
            patched_src = tmp / "upstream"
            shutil.copytree(sub_dir, patched_src, ignore=shutil.ignore_patterns(".git"))
            layout = up_cfg.get("patch_layout", "flat")
            patches_dir = proj.root / up_cfg.get("patches_dir", "patches")
            if patches_dir.is_dir():
                for p in patch_check.discover(patches_dir, layout):
                    subprocess.run(["git", "apply", str(p)], cwd=patched_src, check=True)
            inc_args.append(f"-I{patched_src}")
            for src in extra_sources or []:
                candidate = patched_src / src if not src.is_absolute() else src
                src_args.append(str(candidate))
        else:
            for src in extra_sources or []:
                src_args.append(str(src))

        for inc in include_dirs or []:
            inc_args.append(f"-I{inc}")

        bin_path = tmp / "falsify_bin"
        cmd = [
            cc,
            "-std=c17",
            "-O1",
            "-g",
            "-Wall",
            "-Wextra",
            "-fsanitize=address,undefined,pointer-subtract,pointer-compare",
            "-fno-sanitize-recover=all",
            *(["-include", str(strict_hdr)] if strict_c17 else []),
            *inc_args,
            *(extra_cflags or []),
            *src_args,
            "-o",
            str(bin_path),
        ]
        print("==> Compiling falsifier:", " ".join(cmd))
        subprocess.run(cmd, check=True)

        env = os.environ.copy()
        env["ASAN_OPTIONS"] = "detect_invalid_pointer_pair=2:detect_leaks=0:halt_on_error=1"
        env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=1"
        print("==> Running falsifier under strict ASan + UBSan")
        res = subprocess.run([str(bin_path)], env=env)
        return res.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scaffold-harness", type=Path, help="Write a starter C falsifier harness to this path")
    parser.add_argument("--run", type=Path, help="Compile and execute this C falsifier harness")
    parser.add_argument("--project", help="Optional project ID whose patched upstream copy is exposed via -I")
    parser.add_argument("--src", action="append", default=[], help="Extra C source file (relative to patched upstream or path)")
    parser.add_argument("-I", "--include", action="append", default=[], help="Extra include directory")
    parser.add_argument("--cflag", action="append", default=[], help="Extra compiler flag")
    parser.add_argument("--no-strict-c17", action="store_true", help="Disable strict zero-length memcpy/memset trap header")
    parser.add_argument("--cc", help="C compiler binary (default: clang/gcc/cc)")
    args = parser.parse_args()

    if args.scaffold_harness:
        args.scaffold_harness.parent.mkdir(parents=True, exist_ok=True)
        args.scaffold_harness.write_text(HARNESS_TEMPLATE)
        print(f"Wrote starter falsifier harness to {args.scaffold_harness}")
        return 0

    if not args.run:
        parser.error("specify --scaffold-harness <path> or --run <harness.c>")

    try:
        return run_falsifier(
            args.run.resolve(),
            project_id=args.project,
            extra_sources=[Path(s) for s in args.src],
            include_dirs=[Path(d).resolve() for d in args.include],
            extra_cflags=args.cflag,
            strict_c17=not args.no_strict_c17,
            compiler=args.cc,
        )
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
