# Working rules (`projects/expat`)

Inherits all rules of the repository root [`../../AGENTS.md`](../../AGENTS.md), including the
**Strict ISO C17 Undefined Behaviour Policy** (`framework/check_runtime_ub.py` enforces this
mechanically):

- **No wild, uninitialised, freed/dangling, or `NULL` pointer `+ 0` (`p + 0`, `p - 0`, `&p[0]`)** —
  `Ptr.add` MUST check non-null, live allocation, `off <= a.size`, and `0 <= off + k <= a.size`
  even when `k = 0` (start from `framework/lean/StrictPtr.lean`; NEVER copy legacy shortcuts).
- **No `NULL - NULL` and no cross-object pointer subtraction or relational comparison** (`p - q`,
  `<`, `<=`, `>`, `>=` require the same live array object).
- **No out-of-bounds pointer formation**, even without dereference.
- **No `memcpy` / `memmove` / `memset` / `memcmp` with `n == 0` on `NULL` or dangling pointers**.
- **Every struct pointer field must be written before it is read**.
- **Never argue "benign UB"**. Report confirmed ISO C17 UB in `docs/{en,zh}/findings.md` with
  minimal upstream patches in `patches/`.

- **Status:** Upstream submodule `expat/` pinned (not yet registered in `framework/projects.json`;
  Lean runtime bootstrap, C translation, and safety proofs **Not done**).

## Scope (`ExpatF`)

- **Upstream source:** `expat/` pinned submodule (`https://github.com/libexpat/libexpat`, C library
  under `expat/lib/`) + `patches/*.patch` in name order.
- **Target configuration:** portable scalar x86_64 Linux LP64 build (`-DXML_DTD -DXML_NS
  -DXML_CONTEXT_BYTES=1024 -DXML_GE=1`, ~20k LOC pure C).
- **Verification goal:** full safety (no ISO C17 undefined behaviour, no signed `int` length/buffer
  overflow in `XML_Parse` / `XML_ParseBuffer` / `XML_GetBuffer` / DTD copying / attribute handling,
  no UTF-8 / UTF-16 tokenizer over-read, no UAF/double-free on `XML_ParserReset` / `XML_ParserFree`
  / external-entity parsers, stated write frame, and termination) across every public `expat.h`
  function used by Python, `libvips`/Sharp, and Linux stacks.

## Real-World Usage Paths & Function Priority

`libexpat` is one of the highest-impact pure-C parsers in the Python and Sharp ecosystems:
- **Python standard library (`Modules/pyexpat.c` -> `xml.parsers.expat`, `xml.etree.ElementTree`,
  `xml.dom.minidom`, `xml.sax`, `plistlib`):** Every Python service parsing XML, SOAP, RSS, SAML,
  SVG, or `.docx`/`.xlsx` feeds untrusted bytes straight into `XML_ParserCreate*`, `XML_Parse`,
  `XML_ParseBuffer`, `XML_GetBuffer`, `XML_SetElementHandler`, `XML_SetCharacterDataHandler`,
  `XML_SetBillionLaughsAttackProtection*`, `XML_ParserFree`.
- **Sharp / `libvips` (`sharp-libvips` bundles `expat`):** Used for parsing XMP XML metadata
  embedded inside uploaded JPEGs, PNGs, WebPs, TIFFs, and AVIFs, as well as fontconfig / SVG XML
  processing.
- **Linux / System Infrastructure (Fontconfig, D-Bus, Wayland, Git, Subversion, CMake, Meson,
  GDB, APR/Apache):** Same streaming `XML_Parse` / `XML_ParseBuffer` entry points.
- **Recent High-Severity CVE Wave (2022–2026):**
  - `CVE-2024-45490`: `XML_ParseBuffer` accepted negative `len`!
  - `CVE-2024-45491`: Integer overflow in `dtdCopy` (`xmlparse.c`).
  - `CVE-2024-45492`: Integer overflow in `nextScaffoldPart` (`xmlparse.c`).
  - `CVE-2026-77214` & `CVE-2026-118370`: Recent 2026 XML parsing / attribute-handling integer
    overflow advisories.
  - Earlier `CVE-2022-25235` (malformed UTF-8 encoding), `CVE-2022-25236` (namespace separator
    injection), `CVE-2022-25315` (`storeRawNames` integer overflow), `CVE-2022-40674` (UAF in
    `doContent`).

### Tier 1 (P0) — Core Streaming Parser, Tokenizer & DTD Engine (Prove All)

1. **Parser lifecycle & streaming input (`xmlparse.c`):**
   `XML_ParserCreate`, `XML_ParserCreateNS`, `XML_ParserCreate_MM`, `XML_ParserReset`,
   `XML_ParserFree`, `XML_Parse`, `XML_ParseBuffer`, `XML_GetBuffer`, `XML_StopParser`,
   `XML_ResumeParser`, `XML_GetParsingStatus`.
2. **UTF-8 / UTF-16 / Latin-1 tokenizer & role state machine (`xmltok.c`, `xmltok_impl.c`,
   `xmltok_ns.c`, `xmlrole.c`):**
   Byte-by-byte streaming tokenization across arbitrary 1-byte chunk splits, invalid UTF-8
   sequences (`CVE-2022-25235`), surrogate pairs, CDATA, comments, processing instructions, and
   attribute normalization.
3. **DTD, entity expansion & Billion Laughs accounting (`xmlparse.c`, `xmlrole.c`):**
   `XML_ExternalEntityParserCreate`, `XML_SetParamEntityParsing`,
   `XML_SetBillionLaughsAttackProtectionMaximumAmplification`,
   `XML_SetBillionLaughsAttackProtectionActivationThreshold`, `XML_SetReparseDeferralEnabled`.
4. **Callback registration & error/position queries (`xmlparse.c`):**
   `XML_SetElementHandler`, `XML_SetCharacterDataHandler`, `XML_SetNamespaceDeclHandler`,
   `XML_SetEntityDeclHandler`, `XML_SetXmlDeclHandler`, `XML_GetErrorCode`, `XML_ErrorString`,
   `XML_GetCurrentLineNumber`, `XML_GetCurrentColumnNumber`, `XML_GetCurrentByteIndex`,
   `XML_GetInputContext`.

### Explicitly Not Planned

- External random-seed OS syscalls (`getrandom`/`/dev/urandom` for SipHash salt — modeled as a
  quantified arbitrary `uint64_t` seed so proofs hold for EVERY hash seed!).
- CLI tool (`xmlwf/`), C++ bindings, and full W3C XML 1.0 conformance beyond invariants needed
  for memory safety.

## Verified Translation Units

Entire `expat/lib/` core (only 4 `.c` translation units!):
- `expat/lib/expat.h`, `expat/lib/expat_external.h`, `expat/lib/internal.h`
- `expat/lib/xmlparse.c`, `expat/lib/xmltok.c` (including `xmltok_impl.c`, `xmltok_ns.c`),
  `expat/lib/xmlrole.c`

## Library-Specific Verification Hazards (No Shortcuts)

1. **Signed `int` vs. `size_t` buffer growth & negative-length arguments (`xmlparse.c` —
   `CVE-2024-45490`, `CVE-2024-45491`, `CVE-2024-45492`, `CVE-2022-25315`, `CVE-2026-118370`).**
   Expat's public API uses signed `int len` for `XML_Parse` / `XML_ParseBuffer` / `XML_GetBuffer`
   while internal pools (`STRING_POOL`, `m_buffer`, `m_atts`, `dtdCopy`, `storeRawNames`,
   `nextScaffoldPart`) compute `int`/`size_t` multiples. Prove every arithmetic step checks
   negativity and overflow before allocation or pointer offset!
2. **Pointer relocation across `realloc` (`m_buffer`, `m_bufferPtr`, `m_bufferEnd`, `m_bufferLim`,
   `m_parseEndPtr`).**
   `XML_GetBuffer` reallocates `m_buffer` and updates multiple interior pointers by subtracting the
   old base (`m_bufferPtr - m_buffer`). Under strict ISO C17, verify pointer validity before and
   after every `realloc` (never computing `NULL + 0` on an unallocated buffer!).
3. **Re-entrant callbacks & `XML_StopParser` / `XML_ResumeParser` suspension (`xmlparse.c` —
   `CVE-2022-40674`).**
   User element/character callbacks may call `XML_StopParser(parser, XML_TRUE)` (suspend) or
   `XML_StopParser(parser, XML_FALSE)` (abort). Prove `doContent` / `doProlog` preserve all pool,
   tag-stack, and entity-stack invariants across callback returns, suspension, resumption, and
   `XML_ParserFree`.
4. **Streaming UTF-8 / UTF-16 lookahead at chunk boundaries (`xmltok_impl.c` — `CVE-2022-25235`).**
   Prove multi-byte UTF-8 (`2/3/4`-byte) and UTF-16 surrogate tokenizers never read past `end` when
   an incomplete sequence lands at the end of a chunk (`XML_TOK_PARTIAL`).
5. **Hash tables (`HASH_TABLE` / SipHash) & `STRING_POOL` arena chains.**
   Prove open-addressing table growth (power-of-two capacity, load factor) always terminates and
   never dereferences null/freed pool blocks across `XML_ParserReset` and `dtdCopy`.

## Bootstrap & Local Commands

When onboarding into `framework/projects.json`: copy `lean-toolchain`,
start `ExpatF/Runtime/Ptr.lean` from `framework/lean/StrictPtr.lean`, wire `ExpatF/Results.lean`
and `project.json`, then run:

```bash
lake --dir projects/expat build --wfail ExpatF ExpatF.Results
python3 framework/check_project.py expat --skip-build
```
