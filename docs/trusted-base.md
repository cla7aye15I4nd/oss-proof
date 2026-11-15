# Trusted base: what the kernel does not check

The kernel checks a proof against its Lean statement. That the statement says something true of
the selected C source also depends on the six items below. They are reviewed and tested; they
are not proved, and compiling the proofs does not discharge them. Every page of this
documentation lists the same six.

| # | Trusted | Checked by |
| --- | --- | --- |
| 1 | The Lean kernel, three axioms, and the audit programs | The axiom gate and a fresh kernel replay |
| 2 | The runtime: heap, pointers, faults, loops, modelled library calls | Review and semantic regression tests |
| 3 | The hand translation of the C | Review and differential tests against the real C |
| 4 | The selected source: the pin and five patches | The patch register. Each patch has a sanitizer reproduction, except 0005 and one branch of 0004, which rest on a probe run and on the model |
| 5 | The build configuration and the model of the outside world | Review against glibc and POSIX; differential tests |
| 6 | The statements: that each goal says what it should | Review against `zlib.h`; the exact-goal check |

Compiler, operating-system and hardware correctness are outside the proof altogether.
Differential tests are evidence of fidelity, not proof.

Related pages: [safety](spec/safety.md) defines the claim; [deviations](deviations.md) lists the
premises a caller must meet; [model limits](model-limits.md) details item 2;
[verification policy](anti-cheating.md) gives the acceptance rules; [progress](progress.md#scope)
has the level of each result.

## 1. Kernel and permitted axioms

The Lean kernel and `propext`, `Classical.choice` and `Quot.sound` are trusted.
The declaration audit permits only those axioms. Fresh kernel replay checks the compiled
proof closure; execution tests do not replace it.

The audit itself is trusted code and trusted data. `tests/audit/Audit.lean` reads the compiled
modules; it does not elaborate source or run code of the audited modules. `scripts/verification.py`
decides which goals are required from `tests/audit/public-api.json`. The registries
(`tests/audit/theorems.txt`, `goals.txt`, `proved-goals.txt`) and the manifest are edited by hand
and tracked by git alone. `tests/audit/compiler-helpers.txt` lists the compiler-generated
auxiliary declarations (such as `._unsafe_rec`) that the audit exempts from its `unsafe` and
`partial` checks and does not take as roots of the axiom traversal. The
[helper review](checking/compiler-helper-review.md) of them is a historical record.

## 2. Runtime and object schema

`ZlibF/Runtime/` defines what a translated run means. `Space.lean` supplies object references
and updates. `Monad.lean` supplies faults, sequencing and loops. `Ptr.lean` supplies pointer
arithmetic, loads, stores and comparisons. `Libc.lean` models the required library operations;
`Alloc.lean` imports it. `Schema.lean`, `Tables.lean` and `LibcTables.lean` supply generated
records, constants, heap tables and operations for each struct kind. Their generator and the
[runtime schema](runtime-schema.md) are part of this item.

A no-fault theorem is a statement about these definitions. The intended correspondence is that
every undefined behaviour the C can reach becomes `Fault.ub`. Unsigned arithmetic is modular.
Signed arithmetic, shifts and conversions are checked by each translation; item 3 names the one
accepted exception. The correspondence
has limits, and four of them matter to every reader:

- **Uninitialised pointers.** The model has no value for an uninitialised pointer: a pointer field
  in fresh memory reads as `NULL`. Comparing, copying and freeing it can succeed in the model
  where C gives no guarantee. So every proof shows that a pointer field was written before it is
  read; the runtime does not check this.
- **Uninitialised integers.** An integer cell of fresh memory has an arbitrary value, fixed per
  cell by the garbage function. Theorems hold for every garbage function.
- **Loop fuel.** A loop runs for at most `2^64` iterations; exhausting the bound is
  `Fault.outOfFuel`, which a termination proof excludes. One statement allows `outOfFuel`: the
  first half of the gz safety goal. It is partial correctness up to `2^64` iterations of each
  loop, which no real execution reaches. Undefined behaviour that grows with the iterations (a
  signed 64-bit counter advancing by at least 1 per iteration) would occur within `2^63`
  iterations, inside the fuel, so it is not hidden behind `outOfFuel`.
- **In-place table updates.** The primitives that write change a heap table in place
  (`Space.modify`). A lemma (`modify_eq`) states that this equals the functional update the
  proofs reason with; the review of that lemma and of the table type is part of this item.

[Model limits](model-limits.md#how-the-runtime-represents-c) has the full lists under three
headings: "Memory and library operations" (what `memcpy`, `malloc`, `free` and the other modelled
calls check), "Representation gaps and proof obligations" (pointers, array extents, addresses,
read-only marking) and "Table updates".

## 3. Manual translation

The translation in `ZlibF/Zlib/` is written by hand, statement by statement. The kernel does not
check that it corresponds to the C. Review checks evaluation order, checks, arithmetic, storage
lifetime and effects. A mismatch is a translation bug: it is corrected, with a differential test
that catches it, and never hidden by changing a theorem.

The translation differs from a literal statement-by-statement copy in four accepted ways, each
equivalent to the C: an out-parameter of an internal function is passed by value and returned as
a second result; two reads of one location with no store between them are one read; consecutive
assignments to fields of one record are one record update; a signed operation that a preceding
test of the same function keeps in range uses the plain operator. The
[translation rules](design/translation.md) show an example of each and say what evidence each
function needs. The test inventory is `tests/list.txt`.

Differential tests compare finite executions against the real C. They are evidence of fidelity,
not proof. In particular, agreement and a silent sanitizer do not establish that a C expression
has defined semantics.

## 4. Selected source

The verified source is the pinned `zlib/` submodule plus `patches/*.patch` in name order.
The submodule is never edited. A patch is permitted only for a confirmed zlib bug that blocks a
proof; it must be minimal and match a fix submitted upstream. A patch that the owner approves may
land before its submission; the register then marks it as local and pending. A patch is removed
after upstream merges the fix and the pin moves past it.

Five patches are applied. Every theorem is about the patched source, so each patch is part
of what a reader trusts. [The patch register](../patches/README.md) gives the evidence for each.

| Patch | Fixes | Upstream state |
| --- | --- | --- |
| 0001 | Relational comparison of unrelated pointers in `inflateCopy` | Matches upstream PR #1369; not yet on the upstream branch |
| 0002 | Signed overflow in `gzseek64` after `gzungetc` | The `gzlib.c` part of upstream PR #1361, open |
| 0003 | Stale `x.next` after a partial transparent read fails | Upstream PR #1363, open |
| 0004 | Overflow of the gz position `x.pos` | Local, approved by the owner, not submitted |
| 0005 | Arithmetic on an unwritten or dangling `x.next` with a zero advance | Local, approved by the owner, not submitted |

Historical proposals are not part of the verified source merely because notes mention them.

## 5. Configuration and external world

The target is the default x86_64 Linux/LP64 static build with the default allocator.
The [platform scope](spec/platform.md) requires each represented byte
object to have fewer than `2^63` bytes. This is an environment premise; the zlib
proofs establish that the library's operations preserve it. It is the LP64 `PTRDIFF_MAX` object-size
limit, and it holds on every heap of a call history.
Allocation failure remains in scope. Other build configurations and custom allocators would
need their own correspondence arguments; they are not planned ([scope](progress.md#scope)).

**Allocation size.** `malloc` returns NULL for a request above `PTRDIFF_MAX` (`2^63 − 1` bytes),
whatever the allocation oracle says. The call still consumes one oracle number, and the heap
after it is the same as after an oracle failure: the two are indistinguishable to the caller
except through the size. Below the limit the oracle decides. This is glibc 2.43's
behaviour (`malloc/malloc.c`: `_int_malloc` and `__libc_realloc` test `bytes > PTRDIFF_MAX` and
return NULL with `ENOMEM`; `__libc_calloc` first refuses a product that overflows `size_t`).
`errno` is not modelled for `malloc`; no zlib path reads it after an allocation. Only two call
sites can make such a request (`gz_open`'s path copy and `gz_error`'s message); the other
allocations have `unsigned` or fixed sizes. So every library allocation keeps each byte object
below `2^63` bytes (`ByteObjectsFit.allocB`), and the platform premise is needed only for
caller storage.

**Formatting.** `GzFs.snprintf` models the three fixed-format calls of `gzlib.c` (`"%s%s%s"`,
`"%s"`, `"<fd:%d>"`). It writes at most `size - 1` bytes of the full output and a NUL inside
`[dst, dst + size)`, and returns the full length, or -1 past `INT_MAX`. In glibc 2.43 that is
the only failure for `%s` with a `char *` and for `%d` (`stdio-common/vfprintf-process-arg.c`,
`form_string` and `form_integer`; `stdio-common/Xprintf_buffer_done.c`, `EOVERFLOW` past
`INT_MAX`). Its `errno` is not modelled. That is a stated limitation. No caller reads `errno`
before a system call sets it again: the model reads `errno` only in `zstrerror` and `getErrno`,
in `gzwrite.c.lean` (`gz_comp`, after a failed `fsWrite` in an iteration that starts with
`setErrno 0`) and in `gzread.c.lean` (`gz_load`, after a failed `fsRead`; `gzread`, when
`again` was set by `gz_load` in the same call).

`GzFs.vsnprintf` models `gzvprintf`'s call with the caller's format. Any call may fail, through
the world oracle `printfOk`. A failed call returns -1, sets a nonzero `errno` (`printfErrno`;
`EOVERFLOW` past `INT_MAX`) and leaves arbitrary bytes (`printfJunk`) and a NUL inside
`[dst, dst + size)`. glibc writes the terminator on every path (`libio/vsnprintf.c`,
`__printf_buffer_snprintf_init` and `__printf_buffer_snprintf_done`) and writes nothing outside
the buffer. The oracle works in both directions. It may fail where glibc deterministically
succeeds; that widening does no harm to safety. It may succeed where glibc deterministically
fails, for example `%lc` with an invalid wide character, but `%lc` is not represented and faults.
So a goal clause conditioned on `printfOk` describes the model branch, not a claim that glibc
succeeds on that format. The formatter runs before the oracle is consulted, so an unrepresented
conversion faults: conservative. The defaults of the oracle fields (all calls succeed, empty
junk, `EOVERFLOW`) exist for the executable drivers only and carry no meaning for the proofs.
Every goal quantifies over all worlds.

**The gz file world.** `ZlibF/Zlib/gzfs.lean` has two parts. The regular-file part represents
flat paths, regular files, directory markers, descriptor positions and a file-size limit. The
OS-call oracle (fields of `Fs`, numbered by the call counter `nos`) decides for each `read`,
`write`, `lseek`, `close` and `open` call whether it behaves as the regular file, fails with a
chosen errno, or returns a chosen result. Every oracle value is mapped into the POSIX contract of
the call: `read` returns -1 or at most the requested count; a nonempty `write` returns -1 or
between 1 and the count; `lseek` returns -1 or a value in `[0, 2^63 - 1]`, possibly unrelated to
later reads; `close` returns 0 or -1 and releases the descriptor in both cases; `open` returns -1
or any descriptor number below `2^31` that was not open, and fails with `EMFILE` when no
descriptor below `2^31` is free. A failure sets a nonzero errno, and a success may
change errno. The safety goals quantify over every world, hence over every oracle.

The oracle is deliberately wider than any real system: an oracle read or write succeeds whatever
the descriptor's state (closed, wrong access mode); an oracle write does not change the file; an
oracle `lseek` does not move the descriptor; read data is arbitrary; a regular read is still cut
by the read budget. These choices only add behaviours, and must not be narrowed. No proof may
depend on the number `open` returns: the model's descriptor table is not the whole process.

Two OS facts are assumed and not checked: a nonempty `write` never returns 0, and `close`
releases the descriptor even when it reports an error. Both hold on Linux. The first is needed
for termination of `gz_comp`; the real C spins forever on a `write` that returns 0 forever
([observation](progress.md#observations)).

`strerror` (`C.libcErrnoText`) is total over every `Int32`. For a number outside its table it
returns glibc's `"Unknown error N"` (glibc `string/strerror_l.c`, checked on glibc 2.43; glibc's
out-of-memory fallback `"Unknown error"` without the number is not modelled). Its text is at most
37 bytes plus a NUL, read-only, and valid until the next call. For a Linux number that glibc
knows and the table does not, the text differs from glibc's; no safety argument depends on the
text or its length, because `gz_error` sizes its copy from `strlen`.

The read budget (`readBudget`) bounds the bytes a non-negative descriptor number may still
deliver. It is a premise of the termination half of the gz safety goal only
([deviations](deviations.md#gzip-file-interface)). Functional gz contracts are stated for the
world in which every OS call behaves as a regular file (`RegularOs`). `fcntl` has no effect; its
results are ignored by the C.

The gz file world and formatting model are additional trusted semantics. Their supported file
kinds, errors, conversions and external string allocation do not represent every operating-system
or library behaviour. The callback decoder's theorem assumes the caller's protocol for `in` and
`out`: both return, the total input is bounded, and the window is preserved
([deviations](deviations.md#callback-decoder)). Compiler, operating-system and hardware
correctness are outside the proof.

## 6. Statements and authority

A proof can establish an incomplete or wrong specification. So the statements are reviewed: each
goal, its preconditions and the definitions it names are compared with the
[API](spec/api/README.md), the [format](spec/format/README.md) and the selected C. The review also
confirms that init establishes the invariant and that the caller domain has not been reduced.
[Deviations](deviations.md) is the list of the places where a goal asks more of the caller than
`zlib.h` does.

Nothing in the tooling fixes definitions and theorem types: git tracks them, and review decides
whether their meaning is right. The [verification policy](anti-cheating.md) says what the
acceptance suite still defends against. Current results and open work are only in
[progress](progress.md).
