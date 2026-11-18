# zlib-f

A machine-checked proof, in Lean 4, that every documented public function of zlib is safe: no
undefined behaviour, no memory error, no leak, and every call returns. This holds for every input
and every sequence of calls that meets the conditions below.

The subject is zlib 1.4 with six patches, as built by default on x86_64 Linux: 86 functions.
Lean's kernel checks every proof.

The conditions of the theorems:

- **Source.** zlib 1.4 with the six [patches](patches/README.md). Unpatched zlib 1.4 has the
  defects listed under "Found in zlib".
- **Allocator.** `zalloc` and `zfree` are `Z_NULL`, so zlib uses its default allocator. A custom
  allocator is outside every theorem. A failing `malloc` is covered.
- **Sequence of calls.** A sequence is the history of one object: one stream from its init, one
  gzip file from its open, or one `inflateBack` decoder from its init. Every call in it meets
  the conditions on its arguments, whatever it returns. Between two calls the caller changes only
  the four buffer fields of the stream and memory that zlib did not allocate for the object. Each
  theorem says which memory a call may write. No theorem states how the histories of two objects
  in one program combine.
- **Caller memory.** The buffers given to a call overlap neither one another nor memory that
  zlib allocated for the object, and no object has 2^63 bytes or more.
- **Termination of the gz calls.** `gzread`, `gzfread`, `gzgetc`, `gzgets` and `gzungetc` are
  proved to return when the file descriptor can deliver fewer than 2^61 more bytes; without
  that, they are still proved free of undefined behaviour. The writing calls are proved to
  return for a `write` that never returns 0 on a non-empty request.
- **`inflateBack`.** One call is offered fewer than 2^48 input bytes, and the `in` and `out`
  functions follow a stated protocol: they return, write only memory of their own and leave the
  window as it is.
- **`gzprintf`, `gzvprintf`.** The call is one that C defines for its format and arguments, and
  the format has no `%n`. The model does not read the caller's format, so it does not detect a
  format that does not match its arguments.

[Deviations](https://www.dataisland.org/zlib-f/en/deviations.html) lists the conditions by
function.

## Proved

- `inflate` is safe on every input, however the caller splits the buffers across calls.
- `deflate` is safe on every input, however the caller splits the buffers across calls.
- Every other documented function is safe: `compress` and `uncompress`, the checksums, the gzip
  file interface from `gzopen` to `gzclose`, and the callback decoder `inflateBack`.
- The round trip of the default zlib stream, when every allocation succeeds and no preset
  dictionary is used. `uncompress(compress(x)) = x` when `compress` has `compressBound` room.
  For streams: after `deflateInit` at the default level, `deflate` calls with any flush value
  and any split of the buffers, finished by `deflate(Z_FINISH)` calls with output room, write a
  stream that `inflate` calls after `inflateInit`, in any split and with output room, read back
  to exactly the input. `deflateParams`, resets and other levels are not part of it.

## What it rests on

The C is translated to Lean statement by statement. Every undefined behaviour the C can reach is
a fault in the translation, and the theorems say that no fault occurs. The translation, the model
of memory and the statements themselves are trusted, not proved: the
[trusted base](https://www.dataisland.org/zlib-f/en/trusted-base.html) has six items and names
each one. Differential tests compare the translation with the real C; they are evidence that the
two agree, not proof.

## Found in zlib

Eight issues, each reached through documented calls: six are undefined behaviour or a memory
error, two are a `deflateBound` that is too small. Six patches fix seven of them; each patch is a
fix submitted upstream. The theorems are about the patched source.
[Findings](https://www.dataisland.org/zlib-f/en/findings.html) has the table, and
[patches](patches/README.md) describes each patch.

## Not claimed

Functional correctness beyond that round trip. No round trip is proved in other configurations:
other levels, strategies, window sizes or wrappers, preset dictionaries, the gzip file interface
or `inflateBack`. No theorem says what `inflate` does with a stream the format rejects, beyond
that the call is safe. None of this is planned. Also not covered: other build
configurations, custom allocators, and the functions `zlib.h` lists as undocumented.

## Check it yourself

```bash
lake build --wfail ZlibF
lake env leanchecker --fresh ZlibF.Results
```

The first command compiles every module, so Lean's kernel checks every proof. A warning is an
error, so the build fails if a `sorry` (an admitted, unproved step) is left in the sources. The
build also checks the list of results: each theorem states exactly its goal and depends on no
axiom beyond the three standard ones, and every required goal has a theorem. The largest modules
need 8 to 9 GB of memory each.

The second command is an independent check of the compiled results: the kernel checks every
declaration they depend on again, in a fresh environment. It needs about 10 GB of memory. It is
not run on every change.

## Read more

- [Documentation site (English)](https://www.dataisland.org/zlib-f/en/) · [中文文档](https://www.dataisland.org/zlib-f/zh/)
- [Overview](https://www.dataisland.org/zlib-f/en/overview.html): how the proof is built
- [Status](https://www.dataisland.org/zlib-f/en/progress.html): every result and function
- [Coverage](https://www.dataisland.org/zlib-f/en/coverage.html): the theorem of each function
- [Trusted base](https://www.dataisland.org/zlib-f/en/trusted-base.html): what is not checked
