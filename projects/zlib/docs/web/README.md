# zlib × Lean

Three long bilingual articles explain zlib itself:

1. **A complete codec:** LZ77, Huffman, transmitted coding rules, framing and
   independent reconstruction.
2. **Implementation and optimization:** actual deflate/inflate, search, coding
   choices, storage, tables and copying. This is the central, deepest article.
3. **Added capabilities:** streaming, controls, dictionaries, wrappers, Adler-32,
   CRC-32, combinations and application interfaces.

Formal verification has a separate reading track. The three algorithm articles do
not introduce Lean, theorem inventories or formal invariants. Exact specifications,
proof explanations and the single status page remain available as reference.
All 96 public API entries per language retain their complete contracts.

## Writing for the reader

Build an explanatory argument: task, technical difficulty, derived mechanism,
worked example, implementation and its tradeoffs. Introduce the purpose and abstract
object before its concrete name, struct, field or constant. A table or source link
does not substitute for an explanation. Apply this rule to every paragraph,
diagram, control label and code excerpt.

The basic codec must be complete before discussing optimization. The receiver's
codebook, token parsing and termination belong to that basic closure. Optional
wrapper identification, streaming and integrity checks add different capabilities.
Explain each new feature before any optimization of that feature. Distinguish a
format rule from a policy for choosing among the format's legal representations.

Start with a concrete repeated passage, introduce the copy instruction and its
meaning, and only then name distance, length and their stored representation.
Streaming records and buffer fields appear when the application needs partial calls.

Every animation answers an introduced question. Keep its current object, controls
and explanation together. Explain the observed result before continuing the text.
Support keyboard operation, reduced motion and a substantive static fallback.
Coding examples must identify their actual format and account for their complete
metadata, payload and ending. The teaching format must never be presented as DEFLATE.

Place citations in the sentences they support. No closing source catalogs,
duplicated navigation, small topic portals or back-and-forth reading ladders.
Keep one searchable contents control on the left. Both languages are complete,
with matching anchors and code. Read each article without opening references during
review: revise any step that requires guessing a new term or filling a logical gap.

## Site and blog boundary

This repository publishes a standalone GitHub Pages site under `/oss-proof/` on the
blog's domain, with the zlib documentation at `/oss-proof/zlib/`. English pages live
under `/oss-proof/zlib/en/` and Chinese pages under `/oss-proof/zlib/zh/`, with
identical relative paths and no language suffixes; `/oss-proof/zlib/index.html`
redirects to the reader's preferred language. Assets and language links are relative
to `/oss-proof/`. Do not add a separate CNAME file.

The blog contains only the short bilingual entrance posts in `integration/`.
Keep the application, articles and interaction code in this repository. The gray
palette and existing font files preserve the blog's visual style.

## Sources

The website is the only published documentation. `../en/` and `../zh/` hold its
English and Chinese Markdown sources at mirrored relative paths, with no `.en.md`,
`.zh.md` or folder `README.md` files. Repository files outside `docs/` link directly
to the published site URLs.

- `../en/read/` and `../zh/read/`: three paired articles (`codec.md`,
  `optimizations.md`, `features.md`); `book.py` owns their order and sections.
- `reading.py`: article rendering. `navigation.py` and `static/navigation.*` own
  the one global contents panel.
- `../en/spec/api/` and `../zh/spec/api/`: complete API content, return
  classifications and calling rules. Each function contains a three-column Markdown
  return table and native details for exact conditions. `api_returns.py` styles the
  same table as a connected map; it does not maintain a second copy of its wording.
- `static/minimal-codec.*`, `static/minimal-codec-model.mjs`: the first article's
  complete teaching format, packet-only decoder and editable worked example.
- `static/zlib-*-scene.*`: local mechanism diagrams and controls.
- `static/zlib-playground.*`, `static/zlib-playground-worker.js`,
  `static/examples/codec-playground.c`: actual C round trips for editable UTF-8 or
  hexadecimal inputs, with a 256 KiB bound and actual saved call records.
- `content/codec-playground-provenance.json`: source pin, ordered patches, source
  and header hashes, compiler flags and artifact hashes. Compile the listed files
  after applying those patches to reproduce `static/vendor/zlib-playground.*`.
  Keep the bundled license. The wasm32 example has its own build configuration.
- `codec_trace.py`, `content/codec-trace.json`, `static/examples/codec-trace.c`:
  fixed-source native run records. Insert explained comparisons with a
  `comparison:window`, `comparison:search` or `comparison:storage` HTML comment.
- `reference.py`, `syntax.py`: render canonical content and precise source views
  under `en/` and `zh/`.
- `progress.py`: done or not done, for every goal and every public function. A reader sees
  these two states only. It reads the three lists of `ZlibF/Results.lean` as text, with the
  Lean comments removed, and stops the build when a list is missing or empty, holds anything
  but entries, or when a required goal is not in the list of proved goals. The status page itself is `../en/progress.md` and
  `../zh/progress.md`, written by hand; `tests/test_progress.py` compares its rows
  with what `progress.py` computes.
- `home.py`: the landing pages (`en/index.html` and `zh/index.html`) plus the root
  entry `index.html`.
- `pagekit.py`: the build stamp, the fixed top navigation and the meta description.
- `static/diagram-view.mjs`: natural diagram dimensions, scrolling and bounded zoom.

## Build and local preview

Use Python 3.12 or newer, from this directory:

```sh
python3 -m pip install -r requirements.txt
python3 build.py
python3 check.py
node --test tests/*.test.mjs
python3 -m http.server --directory dist
```

The output is static HTML, CSS, fonts, JavaScript and WebAssembly. Interactions have
no server runtime. Mermaid loads on demand using the vendored renderer and license.
The source code views keep their original code and line anchors.

Each Chinese reference document under `../zh/` starts with a comment
`source-sha256: <hash>`, the SHA-256 of its English counterpart under `../en/`. A
missing companion stops the build. A companion whose hash does not match gives a build
warning and a notice on the Chinese page, so update the hash when you change both
files. `check.py` rejects English prose left in a Chinese page.

## Publication

The site is published from `main` only. The Pages workflow builds and checks `dist/` when
`docs/`, the goal statements (`ZlibF/Spec/`), `tests/audit/public-api.json` or the workflow
change. Pull requests are built and checked without publishing; pushes to `main`
publish through GitHub Actions. Lean sources are linked on GitHub at the built commit;
the site keeps no copy.
