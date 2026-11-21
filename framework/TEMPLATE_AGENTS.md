# Working rules (`projects/<id>`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md) and
[`../../framework/PROOF_PLAYBOOK.md`](../../framework/PROOF_PLAYBOOK.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0` (`p + 0`, `p - 0`, `&p[0]`)** —
  `Ptr.add` MUST check non-null, live allocation, `off <= a.size`, and `0 <= off + k <= a.size`
  even when `k = 0` (start from `framework/lean/StrictPtr.lean`; NEVER copy legacy shortcuts).
- **No `NULL - NULL` and no cross-object pointer subtraction or relational comparison** (`p - q`,
  `<`, `<=`, `>`, `>=` require the same live array object).
- **No out-of-bounds pointer formation**, even without dereference (`virtualStart = buf - extSize`
  on `char *` is `Fault.ub`).
- **No `memcpy` / `memmove` / `memset` / `memcmp` with `n == 0` on `NULL` or dangling pointers**.
- **Every struct pointer field must be written before it is read** (never rely on fresh model
  pointers defaulting to `.null` to excuse an uninitialised C pointer read).
- **Never argue "benign UB"** from C++, C2y, compiler output, or hardware behaviour. When upstream C
  reaches any ISO C17 UB through documented API calls, reproduce/confirm it, record it in
  `docs/{en,zh}/findings.md`, and propose a minimal upstream C patch in `patches/`.

## Scope (`<Package>`)

- **Upstream source:** `<upstream>/` pinned submodule (`<repo-url>`) + `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build (`<compiler-flags>`).
- **Verified translation units:**
  - `<list .c and .h files>`
- **Planned public goals:**
  - Full safety (no `Fault.ub`, no out-of-bounds access, no dangling borrow, no leak, termination)
    of every documented public function in `<public-header>` across every valid call sequence, paired
    with concrete non-vacuity witnesses.
- **Not planned:** `<explicitly list out-of-scope components and functional goals>`.

## Library-specific verification hazards

1. `<Hazard 1: e.g. fast-loop lookahead / wildcopy overlength margins>`
2. `<Hazard 2: e.g. streaming state suspension/resumption across error & reset states>`
3. `<Hazard 3: e.g. zero-copy output borrows or external dictionary lifetimes>`
4. `<Hazard 4: e.g. custom arena / sub-allocator invariants>`

## Local commands

From repository root (Python 3.11+, `LEAN_NUM_THREADS=4` under 16 GB RAM):

```bash
LEAN_NUM_THREADS=4 lake --dir projects/<id> build --wfail <Package> <Package>.Results
python3 framework/check_project.py <id> --skip-build
```
