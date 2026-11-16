# zlib-f

A machine-checked proof, in Lean 4, that every documented public function of zlib is safe: no
undefined behaviour, no memory error, no leak, and every call returns. For every input and every
sequence of calls.

The subject is zlib 1.4 as built by default on x86_64 Linux: 86 functions. Lean's kernel checks
every proof.

## Proved

- `inflate` is safe on every input, however the caller splits the buffers across calls.
- `deflate` is safe on every input, however the caller splits the buffers across calls.
- Every other documented function is safe: `compress` and `uncompress`, the checksums, the gzip
  file interface from `gzopen` to `gzclose`, and the callback decoder `inflateBack`.

Each theorem states its premises. Some go beyond `zlib.h`: caller buffers that do not overlap,
the default allocator, a read budget below 2^61 bytes for the termination of the gz reading
calls, fewer than 2^48 input bytes for one `inflateBack` call.
[Deviations](docs/deviations.md) lists them by function.

## What it rests on

The C is translated to Lean statement by statement. Every undefined behaviour the C can reach is
a fault in the translation, and the theorems say that no fault occurs. The translation, the model
of memory and the statements themselves are trusted, not proved: the
[trusted base](docs/trusted-base.md) has six items and names each one. Differential tests compare
the translation with the real C; they are evidence that the two agree, not proof.

## Found in zlib

Nine issues, each reached through documented calls: seven are undefined behaviour or a memory
error, two are a `deflateBound` that is too small. Six patches fix eight of them; three of the
patches are the fixes submitted upstream. The theorems are about the patched source.
[Findings](docs/findings.md) has the table, and [patches](patches/README.md) describes each patch.

## Not claimed

Functional correctness. No theorem says that the output of `inflate` is what the format defines,
and none is planned. No theorem yet says that the output of `deflate` decodes to its input: that
round trip, for the default zlib stream, is planned and not done. Also not covered: other build
configurations, custom allocators, and the functions `zlib.h` lists as undocumented.

## Check it yourself

```bash
lake build ZlibF
scripts/check-sorry.sh
```

The first command compiles every module, so Lean's kernel checks every proof. The second fails if
a `sorry` (an admitted, unproved step) is left in the sources. The largest modules need 8 to 9 GB
of memory each.

## Read more

- [Documentation site](https://www.dataisland.org/zlib-f/)
- [Overview](https://www.dataisland.org/zlib-f/reference/docs/overview.html): how the proof is built
- [Status](https://www.dataisland.org/zlib-f/reference/docs/progress.html): every result and function
- [Coverage](https://www.dataisland.org/zlib-f/reference/docs/coverage.html): the theorem of each function
- [Trusted base](https://www.dataisland.org/zlib-f/reference/docs/trusted-base.html): what is not checked
