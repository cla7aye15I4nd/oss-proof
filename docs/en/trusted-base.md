# Trusted base: what the kernel does not check

The kernel checks a proof against its Lean statement. That the statement says something true of
the selected C source also depends on the six items below. They are reviewed and tested; they
are not proved, and compiling the proofs does not discharge them.

| # | Trusted | Checked by |
| --- | --- | --- |
| 1 | The Lean kernel, three axioms, and the programs that check axioms and statements | The build: the kernel checks every proof, and a check of the results examines the type of each theorem and the axioms it depends on. A replay by the kernel in a fresh environment is a command a reader can run |
| 2 | The runtime: heap, pointers, faults, loops, modelled library calls | Review and differential tests |
| 3 | The hand translation of the C | Review and differential tests against the real C |
| 4 | The selected source: zlib 1.4 and six patches | The [patches page](../../patches/README.md). Each patched defect was reproduced with the real C under a sanitizer, with two exceptions: one branch of 0003 rests on a reading of the C; 0006 fixes a broken promise that no sanitizer reports |
| 5 | The build configuration and the model of the outside world | Review against glibc and POSIX; differential tests |
| 6 | The statements: that each goal says what it should | Review against `zlib.h`; the check that a theorem states exactly its goal |

Compiler, operating-system and hardware correctness are outside the proof altogether.
Differential tests are evidence of fidelity, not proof.

Related pages: [safety](spec/safety.md) defines the claim; [deviations](deviations.md) lists the
premises a caller must meet; [model limits](model-limits.md) details item 2;
[why a green build is not enough](anti-cheating.md) says what protects a result;
[progress](progress.md) has the state of each result.

## 1. Kernel and permitted axioms

The Lean kernel and `propext`, `Classical.choice` and `Quot.sound` are trusted. The kernel
checks every proof when the library is built. In the same build a check of the results examines
every declaration that a theorem depends on, and permits only those axioms. Execution tests do
not replace the kernel check.

An independent replay is a command a reader can run: `lake env leanchecker --fresh ZlibF.Results`
has the kernel check the compiled results, and everything they depend on, again in a fresh
environment. It is not run on every change.

The programs that do this are themselves trusted code, and they work from trusted data. The
check of the results is Lean code that runs in the build, on the declarations the build has
just checked. The pairs of goal and theorem and the list of required goals are written by hand;
the check finds the goals themselves, and fails on a goal that is in no list. The list of the
functions of `zlib.h` that the required goals are compared with is written by hand and compared
with the pinned `zlib.h`. The compiler-generated auxiliary declarations (such as `._unsafe_rec`)
are exempt from the `unsafe` and `partial` checks.

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
accepted exception and the further forms the translations contain. The correspondence
has limits, and five of them matter to every reader:

- **Uninitialised pointers.** The model has no value for an uninitialised pointer: a pointer field
  in fresh memory reads as `NULL`, so a missing write does not show. Comparing, copying and
  freeing such a field can succeed in the model where C gives no guarantee. That the C writes
  each pointer field before it reads it is not a theorem, and cannot be one in this model; it
  is **to confirm** by source review. What is proved: the invariant of each kind of state
  (`InflateInv`, `DInv`, `GzInv`) holds on every reachable stream and on every gz handle with a
  history, and it says what the pointer fields it names hold.
- **Uninitialised integers.** An integer cell of fresh memory has an arbitrary value, fixed per
  cell by the garbage function. Theorems hold for every garbage function.
- **Loop fuel.** A loop runs for at most `2^64` iterations; exhausting the bound is
  `Fault.outOfFuel`, which a termination proof excludes. One statement allows `outOfFuel`: the
  first half of the gz safety goal, which is partial correctness up to `2^64` iterations of each
  loop. Undefined behaviour that grows with the iterations (a signed 64-bit counter advancing
  by at least 1 per iteration) would occur within `2^63` iterations, inside the fuel, so it is
  not hidden behind `outOfFuel`.
- **In-place table updates.** The primitives that write change a heap table in place
  (`Space.modify`). A lemma (`modify_eq`) states that this equals the functional update the
  proofs reason with; the review of that lemma and of the table type is part of this item.
- **Pointer plus zero, and `NULL - NULL`.** The model defines two operations that C17 leaves
  undefined. Adding or subtracting zero returns the pointer, for every pointer value: a null
  pointer, a pointer field that was never written, and a pointer into a freed block.
  `NULL - NULL` is 0. Every other arithmetic on such a pointer is a fault. This is more
  permissive than ISO C, which defines `p + 0` only for a pointer into a live array object or
  one past its end. The verified source reaches both operations. `gzseek64` and `gz_skip_have`
  compute `x.next += 0` on an `x.next` that was never written, or that points into a caller
  buffer the caller has freed. A `compress` call with a `NULL` destination of capacity 0 is
  inside the goal, and when its `deflateInit` succeeds `compress2_z` computes
  `stream.next_out - dest` with both pointers `NULL`. A no-fault theorem does
  not show that the C avoids these two operations
  ([model limits](model-limits.md#conditions-on-the-model-that-goals-state), row "Pointer plus
  zero, and `NULL - NULL`").

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

The translations also contain at least six further forms, which the four do not cover: a value
just stored is used again without a read; an operand is evaluated before the short-circuit test
that guards it in C; a field value is taken from a record loaded before a store; a shift by a
constant count uses the plain operator; the locals of `inflate` that C leaves uninitialised
start at fixed values; and a store is written after a call that follows it in C. That each of
them computes what the C computes is trusted, not proved.
[Translation](design/translation.md#forms-not-covered-by-the-four-accepted-normalisations) lists
the places known; the list is not complete.

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
allows, and it matches a fix submitted upstream.

Six patches are applied. Every theorem is about the patched source, so each patch is part
of what a reader trusts. [Patches](../../patches/README.md) gives the evidence for each.

| Patch | Fixes | Upstream state |
| --- | --- | --- |
| 0001 | Relational comparison of unrelated pointers in `inflateCopy` | The commit of upstream PR #1369, which the maintainer answered with "Applied"; zlib 1.4 does not contain it |
| 0002 | Signed overflow in `gzseek64` after `gzungetc` | The `gzlib.c` part of upstream PR #1361, open |
| 0003 | Stale `x.next` after a partial transparent read fails, and overflow of the gz position `x.pos` while reading | Upstream PR #1405, open |
| 0004 | Overflow of the gz position `x.pos` while writing | Upstream PR #1406, open |
| 0005 | Signed overflow in `gzoffset64` on a negative result of `lseek` | Upstream PR #1404, open |
| 0006 | `deflateBound` too small for `Z_FIXED` at levels 1 to 3 | Upstream PR #1394, open |

## 5. Configuration and external world

The target is the default x86_64 Linux/LP64 static build with the default allocator.
The [platform scope](spec/platform.md) requires each represented byte
object to have fewer than `2^63` bytes. This is an environment premise: the LP64 `PTRDIFF_MAX`
limit on the size of one object. [Deviations](deviations.md#build-and-platform) lists where each
goal states it. Allocation failure is covered. Other build configurations and custom allocators
would need their own correspondence arguments; they are not planned ([progress](progress.md)).

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
`INT_MAX`). Its `errno` is not modelled. No caller reads `errno`
before a system call sets it again: the model reads `errno` only in `zstrerror` and `getErrno`,
in `gz_comp` (after a failed `fsWrite` in an iteration that starts with `setErrno 0`), in
`gz_load` (after a failed `fsRead`) and in `gzread` (when `again` was set by `gz_load` in the
same call).

The formatter of `snprintf` (`formatGo`) faults on every conversion specification that C17
7.21.6.1 leaves undefined among those it reads: a length modifier on `%c` or `%s`, a modifier
pair such as `zl`, anything between the two `%` of `%%`, the `0` flag on `%c` or `%s`, the `#`
flag on `%d`, `%i`, `%u`, `%c` or `%s`, a precision on `%c`, a `NULL` `%s` argument, and a
negative signed argument for an unsigned conversion. So the three library calls are shown
defined. `VaArg.long` stands for the 64-bit type the conversion expects (`long`, `long long`,
`intmax_t`, `ptrdiff_t` or `size_t`).

**The caller's format.** `GzFs.vsnprintf` models `gzvprintf`'s call
`vsnprintf(next, state->size, format, va)` as an external call, by its C contract (C17
7.21.6.12), not by formatting. Assumed: the call is defined in C for the caller's format and
arguments. This is the caller's obligation, as for every call of the printf family; no premise
states it. In particular the format has no `%n`: a conversion that writes through an argument
is outside the contract. The model reads the format as a string, and faults on a pointer
argument into a freed block (an indeterminate value, C17 6.2.4p2). It does not read the
conversions. So a format that does not match its arguments, which is undefined behaviour in C,
is no fault in the model: for such a call `Goal.gzprintf_safety` and `Goal.gzvprintf_safety`
hold of the model and say nothing about the C. The world oracle chooses the result `r`
(`printfRet`), any `int`:

- `r ≥ 0`: the length of the full output, possibly `size` or more. The call writes the first
  `min(r, size - 1)` bytes of `printfOut` (padded with zeros) and a NUL after them.
- `r < 0`: a failure. `errno` is nonzero (`printfErrno`; zero reads as `EOVERFLOW`), and the
  buffer holds arbitrary bytes (at most `size` of `printfOut`), with no NUL promised.

Nothing outside `[dst, dst + size)` is written. Every goal quantifies over all worlds, so every
result the contract allows is covered, the failures of glibc included.

**The gz file world.** The model of the file system (`Fs`) has two parts. The regular-file part represents
flat paths, regular files, directory markers, descriptor positions and a file-size limit. The
OS-call oracle (fields of `Fs`, numbered by the call counter `nos`) decides for each `read`,
`write`, `lseek`, `close` and `open` call whether it behaves as the regular file, fails with a
chosen errno, or returns a chosen result. Every oracle value is mapped into the range the model
gives the call: `read` returns -1 or at most the requested count; a nonempty `write` returns -1 or
between 1 and the count; `lseek` returns -1 or any 64-bit value, possibly unrelated to
later reads; `close` returns 0 or -1 and releases the descriptor in both cases; `open` returns -1
or any descriptor number below `2^31` that was not open, and fails with `EMFILE` when no
descriptor below `2^31` is free. A failure sets a nonzero errno, and a success may
change errno. The safety goals quantify over every world, hence over every oracle.

Inside these ranges the oracle admits more than a real system does: an oracle read or write succeeds whatever
the descriptor's state (closed, wrong access mode); an oracle write does not change the file; an
oracle `lseek` does not move the descriptor; read data is arbitrary; a regular read is still cut
by the read budget. These choices only add behaviours. The number `open` returns is not
constrained further, because the model's descriptor table is not the whole process.

Two facts about the system are assumed and not checked: a nonempty `write` never returns 0;
and `close` releases the descriptor even when it reports an error. Both hold on Linux.
Nothing is assumed of `lseek`: a successful call may return any 64-bit value, a negative one
included, as on a Linux file with unsigned offsets. The first is needed for termination of `gz_comp`. **To confirm**: by a reading of the C, a `write` that returned 0
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

The gz file world and the formatting model are trusted semantics beside the heap. They do not
represent every file kind, error, conversion or allocation of an external string that an
operating system or a library can show. The callback decoder's theorem assumes the caller's
protocol for `in` and `out`: both return, the total input is bounded, and the window is
preserved ([deviations](deviations.md#callback-decoder)).

## 6. Statements and authority

A proof can establish an incomplete or wrong specification. So the statements are reviewed: each
goal, its preconditions and the definitions it names are compared with the
[API](/api.html), the [format](spec/format.md) and the selected C. The review also
confirms that init establishes the invariant and that the caller domain has not been reduced.
[Deviations](deviations.md) is the list of the places where a goal asks more of the caller than
`zlib.h` does.

No program fixes definitions and theorem types: review decides whether their meaning is right.
[Why a green build is not enough](anti-cheating.md) says what is still protected when a statement
changes. The state of each result is in [progress](progress.md).
