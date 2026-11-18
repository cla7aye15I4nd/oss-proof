# External I/O: files, formatting and local storage

The gz functions call the operating system and the C library: `open`, `read`, `write`,
`lseek`, `close`, `fcntl`, `strerror`, `snprintf` and `vsnprintf`. This page describes the model
of those calls: the record [`Fs`](../../../ZlibF/Zlib/gzfs.lean) and the operations on it. The
model is trusted: the kernel checks the proofs against it and does not check it against Linux
([trusted base](../trusted-base.md)).

The main point: every system call may return any result its POSIX contract allows, chosen by an
oracle, and the safety of the gz interface is proved for every oracle
(`Goal.gz_sequence_safety`; [gzip files](../proof/gzip.md)). The premises of that result are in
[deviations](../deviations.md#gzip-file-interface). One of them is about the oracle: the reading
calls are proved to return only when the read budget of the descriptor is finite
([below](#the-os-oracle)).

## The world beside the heap

The file system, the descriptor table and `errno` are a record `Fs`, separate from the heap. A
gz computation has type `G α = StateT Fs C.M α`: it takes a world and a heap, and returns a
value with the new world and the new heap, or a fault.

- A path is a flat byte string. A node holds the bytes of a file, or is a directory marker.
- An open descriptor stores its node, a position and read, write and append flags.
- A descriptor is a C `int`.
- `Fs` also holds the oracle described below.

`FileSystem fs` is the well-formedness condition on a world: descriptors and names refer to
existing nodes, positions, file sizes and the file-size limit are at most `2^63 - 1`, and a
directory is not open for writing. It constrains the file part only; every value of the oracle
is allowed.

## The OS oracle

Each call of `read`, `write`, `lseek`, `close` and `open` takes the next call number and asks
the oracle what to do. The oracle either lets the call behave as on a regular file, or chooses
another result. Every oracle value is mapped into the range the model gives the call (cut or
clamped, never rejected), so every world is legal.

| Call | Regular-file behaviour (the oracle's default) | Other results the oracle may choose |
| --- | --- | --- |
| `open` | Read or write mode; creation, exclusion, truncation and append are represented. An invalid mode or a modelled path failure sets `errno` and returns `-1`. The new descriptor is the lowest free number from 3 up. When no number below `2^31` is free: `-1` with `EMFILE`, before anything is created or truncated. | `-1` with any nonzero `errno`, before anything is created. Or success with the new descriptor moved to any free number below `2^31`. |
| `read` | Copies the requested bytes of the file up to its end, cut to the read budget. An invalid descriptor, a wrong access mode and a directory fail. | `-1` with any nonzero `errno`. Or, for a request of `n` bytes, any `k` in `[0, n]` bytes of arbitrary data, cut to the read budget, whatever the descriptor's state. |
| `write` | Writes at the position, or at the end in append mode. After a seek past the end, a write fills the gap with zeros. A write that crosses `fsizeLimit` is short; a write at the limit fails with `EFBIG`. | `-1` with any nonzero `errno`. Or any count in `[1, n]` for a nonempty buffer (0 for an empty one), without changing the file. |
| `lseek` | Set, current and end offsets; a negative result or a result above `2^63 - 1` is refused. | `-1` with any nonzero `errno`. Or any 64-bit value, negative ones included, without moving the descriptor. |
| `close` | Releases the descriptor; an invalid descriptor fails. | `-1` with any nonzero `errno`; the descriptor is released anyway. |
| `fcntl` | No effect. | None. |
| `errno` after a success | Unchanged. | A successful call may leave any `errno`. The library's own resets of `errno` are separate effects. |
| Read budget | No bound. | For each non-negative descriptor number, the bytes it may still deliver; every `read` is cut to it and debits it. A negative descriptor has no budget. |

The oracle is wider than a regular file. It covers, call by call, the results of
pipes, sockets, devices, signals (`EINTR`), nonblocking descriptors (`EAGAIN`), transient
failures and concurrent file changes, without representing those objects. The regular-file part
does not represent permissions, directory traversal, links or descriptor sharing through
duplication; `O_NONBLOCK`, `O_CLOEXEC` and `O_LARGEFILE` have no regular-file effect.

Two results are excluded by the model. They are assumptions about the system, not premises
of a theorem: a `write` of a nonempty buffer never returns 0; and `close` releases the descriptor
also when it fails. Both hold on Linux. No result of `lseek` is excluded: on Linux, `lseek` on
a file with unsigned offsets can return a negative value other than `-1`, and the oracle
admits every 64-bit value.

The read budget is there to state when reading ends. `zlib.h` puts no bound on the input, and a
source that never ends keeps one `gzread` call running forever in C. For the calls that read
until the input ends (`gzread`, `gzfread`, `gzgetc`, `gzgets`, `gzungetc`), the gz safety goal
has two parts. On every world, the call does not fault, except possibly with
`Fault.outOfFuel`. When the descriptor has a read budget below `2^61` bytes (`ReadsFinite`), the
call returns. Every other gz call is proved to return on every world
([deviations](../deviations.md#why-a-read-budget)).

The oracle is the fields `nos`, `readChoice`, `writeChoice`, `lseekChoice`, `closeFail`,
`openFail`, `openFd`, `okErrno` and `readBudget` of `Fs`. Their default values give the
regular-file behaviour and serve the differential tests only; every safety goal of the gz
interface quantifies over all worlds.

## Error texts

`errno` is an integer of the world. `strerror` returns a pointer to a static text; the model has
a fixed table of Linux texts with a fallback text for every other `int` value.

The model lets only the most recent `strerror` pointer be read: each call makes the earlier
pointer unreadable, also for the same `errno`. This models sequential invalidation. Thread exit,
concurrent calls and locale changes are not represented. The pointer is a read-only view; it is
not an allocation, and it does not change the set of live blocks or the allocation oracle.

The translation calls `strerror` at four places (two in `gzread.c`, two in `gzwrite.c`). Each
passes the pointer at once to `gz_error`, which copies the text into its own message
allocation and neither stores nor frees the pointer.

C string literals are a different thing: a closed, read-only table of the literals of the
library sources, with one fixed pointer per literal.

## Buffers of external calls

`storeBytes` stores the bytes that `read` or a formatter produced. It copies through a temporary
block and frees it, so its effect is one block copy, not a sequence of byte stores. Memory
operations check object bounds, read-only destinations and overlap as everywhere else. An
invalid user buffer is a model fault; the model does not reproduce the operating system's
`EFAULT`.

## Formatted output

Variadic arguments are a list of values `VaArg`: signed and unsigned 32-bit and 64-bit integers,
and string pointers. `gzprintf` receives the list and delegates to `gzvprintf`. The ABI storage
of a C `va_list` is not represented.

The model has two functions, as the C has:

- `snprintf` serves the fixed formats of `gz_error`, `gz_open` and `gzdopen`. It formats with
  the model's formatter, which supports `%%`, `%c`, `%s`, `%d`, `%i`, `%u`, `%x`, `%X` and `%o`,
  the flags `-`, `0`, `+`, space and `#`, a decimal width and precision, and the length
  modifiers `l`, `ll`, `z`, `j` and `t`, where C defines them. Anything else is a model fault.
  It writes at most `capacity - 1` bytes of text and a NUL, and returns the untruncated length,
  or `-1` when that length exceeds `INT_MAX`.
- `vsnprintf` serves the caller's format in `gzvprintf`. It is an external call modelled by its
  C contract, like `read` and `write`: the world oracle chooses the result (`printfRet`) and the
  bytes (`printfOut`). The model does not read the conversions of the format: the caller ensures
that the call is defined in C for its format and arguments, with no `%n`.
  [Trusted base](../trusted-base.md) states the contract.

`gzvprintf` still runs its own length test, its sentinel test, its buffer vacate and its error
handling after the call, for every result of the contract.

## Pointers and local storage in the gz translations

- A `gzFile` is a pointer to the public prefix `x` of the handle's record (`GzFilePtr`).
  `castState` recovers the record, and `strmOf` names the embedded `z_stream`. A field write
  loads and stores that one record, so the handle, its public prefix and its embedded stream
  stay one object.
- A caller's scalar cell is a little-endian byte block: `gzerror`'s optional `int *errnum`
  (four bytes) and the length cells of the four `uncompress*` functions (eight bytes each).
- The internal `unsigned *have` of `gz_load` is a returned value
  ([normalisation 1](translation.md#the-accepted-normalisations)). Each caller stores it, on
  success and on failure. **To confirm** by review: the store happens at the same point of the
  effect order as in C at every call site.
- A local whose address is taken is a fresh object that does not consume the allocation-failure
  oracle and is released on every return: the one-byte buffers of `gzgetc` and `gzputc`; the
  local stream of `uncompress2_z` and its eight-byte block for `&stream.reserved`; and the local
  length cells of `uncompress2`, `uncompress_z` and `uncompress`.
- File-position arithmetic on `z_off64_t` uses checked 64-bit operations.

The model accepts adding zero to every pointer value, a null or a dangling pointer included
([model limits](../model-limits.md#conditions-on-the-model-that-goals-state)). Every other
arithmetic on a null or a dangling pointer is a fault.

## The source is the patched source

Four patches change the gz files ([patch register](../../../patches/README.md)):

| Patch | Change |
| --- | --- |
| 0002 | The range checks of `gzseek64` |
| 0003 | `x.next` is set before `gz_load` in transparent mode, and the readers keep the position `x.pos` within `z_off64_t` |
| 0004 | The writers keep the position `x.pos` within `z_off64_t` |
| 0005 | `gzoffset64` returns `-1` for every negative result of `lseek` |

In the patched source `gz_reset` does not initialise `x.next`, and a direct read leaves `x.next`
pointing into the caller's buffer. `gzseek64` and `gz_skip_have` add zero to those values; no
patch changes this, and the model accepts it.
[Gzip files](../proof/gzip.md#source-reports-and-patches) gives the reports behind the patches.

## Differential evidence

The gz differential tests compare what each operation returns on temporary real files with runs
over `Fs`. The same family of tests compares the bytes and lengths of `uncompress2`.

The tests start from the default oracle, the regular-file behaviour. A test case can make one
chosen `read` call fail, and one caller-format `vsnprintf` call fail. Each caller-format
`vsnprintf` call gets the output glibc gives, computed with the model's formatter. Every other oracle choice
is covered only by the proofs.

Agreement tests the translation and the world model together against selected C executions. It
is evidence of fidelity. It is not a proof of codec correctness, of all error paths, of all
POSIX behaviour or of leak freedom.
