# Trusted base: what the kernel does not check

The kernel checks a proof against its Lean statement. That the statement says something true of
the selected C source also depends on the six items below. They are reviewed and tested; they
are not proved, and compiling the proofs does not discharge them. Wherever this documentation
summarises what is trusted, it lists the same six.

| # | Trusted | Checked by |
| --- | --- | --- |
| 1 | The Lean kernel, three axioms, and the programs that check axioms and statements | The check of the axioms each theorem depends on, and a replay by the kernel in a fresh environment |
| 2 | The runtime: heap, pointers, faults, loops, modelled library calls | Review and semantic regression tests |
| 3 | The hand translation of the C | Review and differential tests against the real C |
| 4 | The selected source: zlib 1.4 and six patches | The [patches page](../patches/README.md). Each patch has a sanitizer reproduction, with three exceptions: 0005 rests on a probe run and a reading of the C; one branch of 0004 rests on a reading of the C; 0006 fixes a broken promise that no sanitizer reports |
| 5 | The build configuration and the model of the outside world | Review against glibc and POSIX; differential tests |
| 6 | The statements: that each goal says what it should | Review against `zlib.h`; the check that a theorem states exactly its goal |

Compiler, operating-system and hardware correctness are outside the proof altogether.
Differential tests are evidence of fidelity, not proof.

Related pages: [safety](spec/safety.md) defines the claim; [deviations](deviations.md) lists the
premises a caller must meet; [model limits](model-limits.md) details item 2;
[why a green build is not enough](anti-cheating.md) says what protects a result;
[progress](progress.md) has the state of each result.

## 1. Kernel and permitted axioms

The Lean kernel and `propext`, `Classical.choice` and `Quot.sound` are trusted. Every
declaration that a theorem depends on is examined, and only those axioms are permitted. The
compiled proofs are replayed by the kernel in a fresh environment; execution tests do not
replace that.

The programs that do this are themselves trusted code, and they work from trusted data. The
program that examines the proofs reads the compiled modules; it does not elaborate source or run
code of the modules it examines. The list of goals, the list of theorems and the list of the
functions of `zlib.h` that it works from are written by hand. The compiler-generated auxiliary
declarations (such as `._unsafe_rec`) are exempt from the `unsafe` and `partial` checks and are
not taken as roots of the axiom traversal.

## 2. Runtime and object schema

The runtime defines what a translated run means. It supplies object references and updates;
faults, sequencing and loops; pointer arithmetic, loads, stores and comparisons; models of the
library operations zlib needs, allocation among them; the text that `strerror` returns
(`libcErrnoText`); the low address bits of a byte pointer, which the CRC code observes; and
records, constants, heap tables and operations for each struct kind. The last group is generated
by a program; the generator and the [runtime schema](runtime-schema.md) are part of this item.

A no-fault theorem is a statement about these definitions. The intended correspondence is that
every undefined behaviour the C can reach becomes `Fault.ub`. Unsigned arithmetic is modular.
Signed arithmetic, shifts and conversions are checked by each translation; item 3 names the
accepted exception and the forms that are not yet decided. The correspondence
has limits, and four of them matter to every reader:

- **Uninitialised pointers.** The model has no value for an uninitialised pointer: a pointer field
  in fresh memory reads as `NULL`. Comparing, copying and freeing it can succeed in the model
  where C gives no guarantee. A proof about the C therefore needs that a pointer field is written
  before it is read. No theorem states this, and none can in this model: a missing write does
  not show, and the runtime does not check it. What the proofs show is narrower: the invariant
  of each kind of state (`InflateInv`, `DInv`, `GzInv`) holds on every reachable stream and on
  every gz handle with a history, and the invariant says what the pointer fields it names hold.
  That the C writes each pointer field before it reads it is **to confirm** by source review.
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

The translation is written by hand, statement by statement. The kernel does not
check that it corresponds to the C. Review checks evaluation order, checks, arithmetic, storage
lifetime and effects. A mismatch is a translation bug: a theorem about a statement that is
translated wrongly says nothing about the C.

The translation differs from a literal statement-by-statement copy in four accepted ways, each
equivalent to the C: an out-parameter of an internal function is passed by value and returned as
a second result; two reads of one location with no store between them are one read; consecutive
assignments to fields of one record are one record update; a signed operation that a preceding
test of the same function keeps in range uses the plain operator. The
[translation rules](design/translation.md#the-accepted-normalisations) show an example of each.

The translations also contain at least six forms that the four do not cover as worded: a value
just stored is used again without a read; an operand is evaluated before the short-circuit test
that guards it in C; a field value is taken from a record loaded before a store; a shift by a
constant count uses the plain operator; the locals of `inflate` that C leaves uninitialised
start at fixed values; and a store is written after a call that follows it in C. Whether each
becomes an accepted normalisation or is changed is not decided.
[Translation](design/translation.md#forms-not-covered-by-the-four-accepted-normalisations) lists
the places found; its tables are examples, not a complete inventory. No place was found to
compute a different value from the C; that is a reading, not a proved fact.

Three parts of this item are easy to miss:

- **Helpers defined in the translation files.** Not every semantic helper is part of the
  runtime. The checked arithmetic and shifts, the integer conversions, the loop and
  control-flow forms, field and table access, the allocator dispatch, local storage, string
  literals and the library stand-ins are defined in the translation files that use them. They
  are trusted in the same way as the runtime.
  [Architecture](design/architecture.md) lists them by kind.
- **The CRC word load.** `crc32.c` reads the buffer through a pointer cast to `z_word_t *`. The
  translation (`loadWord`) reads eight bytes and assembles them little-endian.
  That the two agree, and the aliasing semantics of the cast, are trusted
  ([model limits](model-limits.md#conditions-on-the-model-that-goals-state), row "CRC address
  and word access").
- **Locals of `inflate`.** The translation (`IL.init`) gives the locals `copy`, `len`, `from`,
  `here` and `last`, which C leaves uninitialised, the values 0, NULL and a zero `code`.
  `inflateBack` uses the same record. The rule for an uninitialised integer is an arbitrary
  value; here the value is fixed. Whether `inflate` can read one of these locals before
  assigning it is **to confirm** by source review: a proof about the current translation does
  not show it.

Differential tests compare finite executions against the real C. They are evidence of fidelity,
not proof. In particular, agreement and a silent sanitizer do not establish that a C expression
has defined semantics.

## 4. Selected source

The verified source is zlib 1.4 (upstream commit `99623ef7`) plus the patches, applied in name
order. A patch fixes a zlib issue without whose fix a safety
statement cannot be proved, or a promise of `zlib.h` does not hold. It is as small as the fix
allows, and it matches the fix submitted upstream where one was submitted. A patch marked local
has not been submitted.

Six patches are applied. Every theorem is about the patched source, so each patch is part
of what a reader trusts. [Patches](../patches/README.md) gives the evidence for each.

| Patch | Fixes | Upstream state |
| --- | --- | --- |
| 0001 | Relational comparison of unrelated pointers in `inflateCopy` | Matches upstream PR #1369; not yet on the upstream branch |
| 0002 | Signed overflow in `gzseek64` after `gzungetc` | The `gzlib.c` part of upstream PR #1361, open |
| 0003 | Stale `x.next` after a partial transparent read fails | Upstream PR #1363, open |
| 0004 | Overflow of the gz position `x.pos` | Local: not submitted |
| 0005 | Arithmetic on an unwritten or dangling `x.next` with a zero advance | Local: not submitted |
| 0006 | `deflateBound` too small for `Z_FIXED` at levels 1 to 3 | Local: not submitted |

## 5. Configuration and external world

The target is the default x86_64 Linux/LP64 static build with the default allocator.
The [platform scope](spec/platform.md) requires each represented byte
object to have fewer than `2^63` bytes. This is an environment premise: the LP64 `PTRDIFF_MAX`
limit on the size of one object. Every library allocation keeps it (`ByteObjectsFit.allocB`). An
inflate history states it on every heap on which a call runs and after every caller edit; a
deflate history states it only at the call a goal is about.
[Deviations](deviations.md#build-and-platform) lists where each goal states it.
Allocation failure remains in scope. Other build configurations and custom allocators would
need their own correspondence arguments; they are not planned ([progress](progress.md)).

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
in `gz_comp` (after a failed `fsWrite` in an iteration that starts with `setErrno 0`), in
`gz_load` (after a failed `fsRead`) and in `gzread` (when `again` was set by `gz_load` in the
same call).

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

**The gz file world.** The model of the file system (`Fs`) has two parts. The regular-file part represents
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
for termination of `gz_comp`. **To confirm**: by a reading of the C, a `write` that returned 0
forever would make `gz_comp` loop forever, because neither write loop advances on a count of 0.
No theorem states this: the model has no world with such a `write`.

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

No program fixes definitions and theorem types: review decides whether their meaning is right.
[Why a green build is not enough](anti-cheating.md) says what is still protected when a statement
changes. The state of each result is in [progress](progress.md).
