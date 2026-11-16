# Input ranges for lemmas about a fixed configuration

**For safety there is one input range: every input.** The required goals quantify over every
value of each parameter, and a value outside the supported range is a documented refusal,
which the goal also covers. This page defines three narrower ranges: default, common and all
supported. They matter for two things only: internal lemmas that are stated for a fixed
configuration, and functional goals (not required for the safety results).

Examples of "every input": `Goal.deflateInit2__safety` holds for every level, method, window,
memory level and strategy; `Goal.inflateInit2__safety` for every window value; the sequence
goals for every history that starts from such an init.

The build is the same throughout: default x86_64 Linux, LP64, static library, default
allocator, with the [platform assumption](platform.md) that no byte object has `2^63` bytes or
more.

## The three ranges {#the-three-ranges-and-the-colours}

For each family of goals, the default inputs are contained in the common inputs, and those
in all supported inputs. For the two stream engines each containment is strict. A function
that ignores or fixes a parameter has fewer distinct ranges; no separate proof is needed for a
range that coincides with another.

A range is cumulative; it is not a percentage of work. A proof about a few examples does not
cover a range: each range quantifies over the data, the buffers, the heap contents, the
allocation failures and the histories its statement names.

A goal is done only when a theorem of exactly its type covers every input that its statement
admits. A theorem for the default inputs or for the common inputs alone leaves the goal not
done.

## Deflate inputs

All three ranges use `method = Z_DEFLATED = 8`.

| Parameter | Default | Common | All supported |
| --- | --- | --- | --- |
| `level` | `-1`, normalized to 6 | `-1` and 0 through 9 | `-1` and 0 through 9 |
| `memLevel` | 8 | 8 | 1 through 9 |
| `windowBits` | 15 | -15, 15, 31 | -15 through -9; 8 through 15; 25 through 31 |
| `strategy` | 0 | 0 | 0 through 4 |
| Wrapper | zlib | raw, zlib, gzip | raw, zlib, gzip |

Every combination in a column is included. The common inputs keep a 32 KiB window, the
default memory level and the default strategy. The signed window argument selects raw at -15,
zlib at 15 and gzip at 31. In the full range, a zlib window of 8 is normalized to 9; raw -8
and gzip 24 are rejected by the pinned source.

The five strategies are default (0), filtered (1), Huffman-only (2), RLE (3) and fixed-code
(4). The memory level sets the size of the hash table and of the buffer that holds both the
recorded symbols and the pending output. So a small memory level changes the argument that
the pending output never overwrites symbols not yet read
([trees](../proof/trees.md)).

### Engine and helper ranges

The table says which parameter each part of the compressor depends on. A lemma for one value
of that parameter does not cover the others.

| Part of the compressor | Parameters it depends on |
| --- | --- |
| Default initialization | `deflateInit_` fixes method, window, memory level and strategy, and leaves the level free. Its goal is `Goal.deflateInit__safety`. |
| General initialization | `deflateInit2_` takes all five parameters. `Goal.deflateInit2__safety` covers every value of each. |
| Strategy dispatch | Level 0 selects the stored engine, levels 1 through 3 the fast engine, levels 4 through 9 the slow engine. For a nonzero level, Huffman-only and RLE replace that choice. |
| Match search | The chain length, lazy-match length and nice length come from a table row selected by the level. A lemma about one row does not cover the others. |
| Refill and sliding | The window size and the hash size set the array bounds, the ring positions and the slide. A lemma for a fixed window is not a lemma for every window. |
| Trees and block output | The symbol capacity, the pending buffer and the position of the first unread symbol depend on the memory level. A lemma about one tree or one symbol does not give the bound on the overlap. |

The table lists dependencies; it does not say what is proved. The
[deflate proof guide](../proof/deflate.md) explains the invariants, and
[progress](../progress.md) says which goals are done.

## Inflate inputs

Inflate has no level, memory level or strategy. Its input grammar already includes stored,
fixed and dynamic blocks.

| Range | `windowBits` |
| --- | --- |
| Default | 15 |
| Common | -15, 15, 31, 47 |
| All supported | -15 through -8; 0; 8 through 15; 16; 24 through 31; 32; 40 through 47 |

The common inputs select a 32 KiB window with a raw, zlib, gzip or automatically detected
stream. The values 0, 16 and 32 leave the window size to the stream header; a gzip header carries
none, and the pinned source then uses 15. A smaller window
changes the check of match distances. Whether a small window accepts every valid stream is a
functional question, not a safety one.

### Fast and slow execution

`inflate` has a fast decoding loop (`inflate_fast`) and a slow one. Which one runs does not
depend on the configuration: `inflate` enters the fast loop when at least six input bytes and
at least 258 output bytes are available and fewer than eight bits are held
(`have >= 6 && left >= 258 && bits < 8`). A stream with the default configuration takes either path as the caller changes
the buffers. So a result for the default inputs has to cover both paths and the changes
between them.

| Part of the decoder | What it depends on |
| --- | --- |
| Initialization and reset | The window size and the wrapper selected. |
| Table construction | The block type: stored, fixed or dynamic. All three occur in every range. |
| Fast decoding | The entry conditions above, and the tables and window the earlier steps left. |
| Slow decoding | The literal, length, distance and match steps, each on the state the previous one returned. |
| Dispatch and exit | Both paths, the exits that wait for input or output, the error exits, the window update and the write-back of the counters. |

The [inflate proof guide](../proof/inflate.md) describes these parts. A lemma about one path
assumes the invariant at its entry; it is not a result about a whole stream.

## Entry inputs

For the checksums, the queries, the whole-buffer functions, the callback decoder, the gzip
file functions and the internal goals, the input range is what the goal's statement says:
its arguments and its premises. The stream parameters above apply only where the function or
the state it works on depends on them.

A theorem of exactly the goal's type proves the goal for the domain that the statement names,
with its explicit premises. It does not prove the goal of a calling function
and does not remove those premises.

Every range keeps the error returns, the allocation failures and the cleanup paths. A public
goal also keeps the refusal of every invalid parameter value.
