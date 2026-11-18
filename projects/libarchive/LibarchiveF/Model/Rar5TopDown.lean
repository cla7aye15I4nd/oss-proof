/-
  LibarchiveF/Model/Rar5TopDown.lean

  Top-down formal state & safety invariant model for `libarchive`'s RAR5 format
  reader (`libarchive/libarchive/archive_read_support_format_rar5.c`, 4,690 lines).

  This module models:
  1. Core RAR5 reader state records (`HeaderVint`, `FilterInfo`, `BitReader`,
     `DecodeTable`, `CompState`, `Rar5State`);
  2. Core representation invariants (`WindowInv`, `SolidResetInv`,
     `FilterQueueInv`, `HuffmanInv`, `HeaderBoundsInv`, `Rar5RepInv`), with
     explicit documentation of every safety gap where the C implementation
     relies on an unchecked assumption or violates the invariant;
  3. Safe abstract transition contracts for `init`, `read_header`, `read_data`,
     `read_data_skip`, and `cleanup`, alongside faithful models of the buggy C
     transitions;
  4. Kernel-checked invariant-preservation / deadlock-freedom theorems AND
     counterexample-characterizing theorems witnessing concrete C bugs.
-/

namespace LibarchiveF.Model.Rar5TopDown

/-! ## 1. Constants & Return Codes -/

/-- `g_unpack_window_size` in `archive_read_support_format_rar5.c` (line 86): 128 KiB. -/
def minWindowSize : Int := 0x20000

/-- Maximum dictionary size accepted by `process_head_file` (line 1977): 64 MiB. -/
def maxWindowSize : Int := 64 * 1024 * 1024

/-- `MAX_HEADER_SIZE` (line 104): 2 MiB ceiling on RAR5 base block headers. -/
def maxHeaderSize : Nat := 2 * 1024 * 1024

/-- `MAX_NAME_IN_BYTES` (lines 100–101): `4 * 2048 = 8192` bytes. -/
def maxNameInBytes : Nat := 4 * 2048

/-- Maximum filter queue capacity initialized in `rar5_init` (line 4633). -/
def maxFilterQueueCap : Nat := 8192

/-- Maximum filter block length checked in `parse_filter` (line 3221): 4 MiB. -/
def maxFilterBlockLength : Int := 0x400000

/-- Maximum signed 64-bit integer (`INT64_MAX` / `SSIZE_MAX` on LP64). -/
def int64Max : Nat := 0x7fffffffffffffff

/-- Return status codes corresponding to `ARCHIVE_*` in `archive.h`. -/
inductive ArchiveStatus where
  | ok     -- ARCHIVE_OK (0)
  | eof    -- ARCHIVE_EOF (1)
  | retry  -- ARCHIVE_RETRY (-10)
  | warn   -- ARCHIVE_WARN (-20)
  | failed -- ARCHIVE_FAILED (-25)
  | fatal  -- ARCHIVE_FATAL (-30)
  deriving DecidableEq, Repr

/-! ## 2. Core State Records -/

/--
Variable-length integer (`vint`) decoded by `read_var` / `read_var_sized`
(`archive_read_support_format_rar5.c`, lines 945–1059).

### C Verification Gap (`read_var` -> `rar5_skip_remaining_block`)
`read_var` unconditionally requests a 10-byte lookahead via
`__archive_read_ahead(a, 10, &avail)` (line 967), even when `< 10` bytes remain
in the current header block. In `archive_read.c` (`__archive_read_filter_ahead`,
lines 1521–1569), requesting `min = 10` can either `realloc`/`free(f->buffer)`
or `memmove` `f->buffer`, invalidating the saved `body_start` pointer in
`process_base_block` (line 2498) and causing C11 §6.5.6p9 pointer-subtraction
UB / Use-After-Free in `rar5_skip_remaining_block` (`cur - body_start`, line 2413).
-/
structure HeaderVint where
  value   : Nat
  byteLen : Nat
  deriving DecidableEq, Repr

/-- Well-formedness of a decoded RAR5 `vint` (`1..10` bytes, unsigned 64-bit value). -/
def HeaderVint.Valid (v : HeaderVint) : Prop :=
  1 ≤ v.byteLen ∧ v.byteLen ≤ 10 ∧ v.value < 2 ^ 64

/-- Filter opcodes (`enum FILTER_TYPE`, lines 168–179). -/
inductive FilterType where
  | delta
  | e8
  | e8e9
  | arm
  | unsupported (code : Nat)
  deriving DecidableEq, Repr

/--
Filter descriptor (`struct filter_info`, lines 181–187).
Stored on the heap and referenced via `rar5->cstate.filters` (`struct cdeque`).

### C Verification Gaps
1. `cdeque_filter_p` (line 484) casts `struct filter_info **` to `void **` via
   `size_t` and writes through `*value` (`void *`), violating C11 §6.5p7 strict
   aliasing.
2. `is_valid_filter_block_start` (line 3181) checks `last_bs == 0 || last_bl == 0`
   instead of `last_bl == 0`, allowing overlapping filters whenever the previous
   filter started at `block_start == 0`.
-/
structure FilterInfo where
  fltType     : FilterType
  channels    : Nat
  blockStart  : Int
  blockLength : Int
  deriving DecidableEq, Repr

/-- Provenance of a buffer queued in `rar5->cstate.dready[2]`. -/
inductive BufOrigin where
  | none
  | windowBuf
  | filteredBuf
  deriving DecidableEq, Repr

/-- Entry in the 2-slot output FIFO (`struct data_ready`, lines 189–194). -/
structure FilterOutputSlot where
  used   : Bool
  origin : BufOrigin
  offset : Int
  size   : Nat
  deriving DecidableEq, Repr

def FilterOutputSlot.empty : FilterOutputSlot :=
  { used := false, origin := .none, offset := 0, size := 0 }

/--
Bit-level stream cursor (`struct bit_reader`, lines 287–290).
`bitAddr` is the bit offset `0..7` within `p[inAddr]`.

### C Verification Gaps
1. `read_bits_32` (lines 1064–1074) checks `in_addr >= cur_block_size` and then
   reads `archive_be32dec(p + in_addr)` AND `p[in_addr + 4]`. At `in_addr = cur_block_size - 1`,
   this accesses index `cur_block_size + 3`, requiring every block buffer `p` to
   carry at least 4 initialized padding/lookahead bytes past `cur_block_size`.
2. `parse_tables` (line 2944) reads the post-`ESCAPE` nibble `p[i]` after `++i`
   without re-checking `i < cur_block_size`.
-/
structure BitReader where
  bitAddr : Nat
  inAddr  : Int
  deriving DecidableEq, Repr

/-- Monotonic bit offset from the start of the current compressed block. -/
def BitReader.bitPos (b : BitReader) : Int :=
  b.inAddr * 8 + (b.bitAddr : Int)

/--
Abstract Huffman decode table (`struct decode_table`, lines 204–212).
Models the properties relied on by `create_decode_tables` and `decode_number`
(lines 2790–2907).
-/
structure DecodeTable where
  size        : Nat
  quickBits   : Nat
  upperLimit  : Nat
  minQuickLen : Nat
  maxQuickLen : Nat
  valid       : Bool
  deriving DecidableEq, Repr

def DecodeTable.zeroed : DecodeTable :=
  { size := 0, quickBits := 0, upperLimit := 0, minQuickLen := 0, maxQuickLen := 0, valid := false }

/-- RAR5 `HEAD_MAIN` state (`struct main_header`, lines 307–317). -/
structure MainHeaderState where
  solid  : Bool
  volume : Bool
  endarc : Bool
  volNo  : Nat
  deriving DecidableEq, Repr

/-- RAR5 generic base-block header flags (`struct generic_header`, lines 319–325). -/
structure GenericHeaderState where
  splitAfter   : Bool
  splitBefore  : Bool
  size         : Nat
  lastHeaderId : Nat
  deriving DecidableEq, Repr

/--
RAR5 per-entry metadata (`struct file_header`, lines 106–137).

### C Verification Gaps
1. `solid_window_size` lives inside `struct file_header` (line 136), which
   `reset_file_context` wipes with `memset(&rar5->file, 0, sizeof(rar5->file))`
   on every new entry (line 886)! Consequently, the solid window-size mismatch
   guard at lines 1988–1995 (`if (rar5->file.solid_window_size > 0 && ...)`) is
   dead code on every new entry.
2. `unpacked_size` is cast from `uint64_t` to `ssize_t` at line 2143 without
   checking `unpacked_size <= SSIZE_MAX`, wrapping values `>= 2^63` to negative.
3. CRC32 presence is inferred from `stored_crc32 > 0` (lines 2773, 4372) instead
   of an explicit `hasCrc32` flag, skipping CRC32 checks whenever `stored_crc32 == 0`.
-/
structure FileHeaderState where
  bytesRemaining  : Int
  unpackedSize    : Int
  lastOffset      : Int
  lastSize        : Int
  solid           : Bool
  service         : Bool
  eof             : Bool
  dir             : Bool
  hasCrc32        : Bool
  storedCrc32     : UInt32
  hasBlake2       : Bool
  solidWindowSize : Int
  deriving DecidableEq, Repr

def FileHeaderState.empty : FileHeaderState :=
  { bytesRemaining := 0
    unpackedSize := 0
    lastOffset := 0
    lastSize := 0
    solid := false
    service := false
    eof := false
    dir := false
    hasCrc32 := false
    storedCrc32 := 0
    hasBlake2 := false
    solidWindowSize := 0 }

/--
LZSS + filter decompression context (`struct comp_state`, lines 214–284).
We ghost-track `windowAllocSize` (allocated bytes of `window_buf`),
`windowInitSize` (zero/data-initialized bytes of `window_buf`), and
`solidWindowSize` (the persistent solid dictionary size that *should* live here
rather than in `FileHeaderState`).
-/
structure CompState where
  initialized          : Bool
  allFiltersApplied    : Bool
  switchMultivolume    : Bool
  blockParsingFinished : Bool
  dataEncrypted        : Bool
  method               : Nat
  version              : Nat
  windowSize           : Int
  windowAllocSize      : Int
  windowInitSize       : Int
  windowMask           : Int
  solidWindowSize      : Int
  writePtr             : Int
  lastWritePtr         : Int
  lastUnstorePtr       : Int
  solidOffset          : Int
  curBlockSize         : Int
  blockLookaheadPad    : Nat
  lastLen              : Int
  lastBlockStart       : Int
  lastBlockLength      : Int
  filters              : List FilterInfo
  dready0              : FilterOutputSlot
  dready1              : FilterOutputSlot
  tablesValid          : Bool
  ld                   : DecodeTable
  dd                   : DecodeTable
  ldd                  : DecodeTable
  rd                   : DecodeTable
  deriving DecidableEq, Repr

def CompState.empty : CompState :=
  { initialized := false
    allFiltersApplied := true
    switchMultivolume := false
    blockParsingFinished := true
    dataEncrypted := false
    method := 0
    version := 0
    windowSize := 0
    windowAllocSize := 0
    windowInitSize := 0
    windowMask := 0
    solidWindowSize := 0
    writePtr := 0
    lastWritePtr := 0
    lastUnstorePtr := 0
    solidOffset := 0
    curBlockSize := 0
    blockLookaheadPad := 0
    lastLen := 0
    lastBlockStart := 0
    lastBlockLength := 0
    filters := []
    dready0 := FilterOutputSlot.empty
    dready1 := FilterOutputSlot.empty
    tablesValid := false
    ld := DecodeTable.zeroed
    dd := DecodeTable.zeroed
    ldd := DecodeTable.zeroed
    rd := DecodeTable.zeroed }

/-- Top-level RAR5 format reader context (`struct rar5`, lines 333–382). -/
structure Rar5State where
  headerInitialized   : Bool
  skippedMagic        : Bool
  skipMode            : Nat
  mergeMode           : Nat
  streamPos           : Nat
  hasEncryptedEntries : Bool
  headersAreEncrypted : Bool
  generic             : GenericHeaderState
  main                : MainHeaderState
  cstate              : CompState
  file                : FileHeaderState
  bits                : BitReader
  expectedVolNo       : Nat
  checksumVerified    : Bool
  freed               : Bool
  deriving DecidableEq, Repr

/-- Initial state created by `rar5_init` (lines 4630–4643). -/
def initState : Rar5State :=
  { headerInitialized := false
    skippedMagic := false
    skipMode := 0
    mergeMode := 0
    streamPos := 0
    hasEncryptedEntries := false
    headersAreEncrypted := false
    generic := { splitAfter := false, splitBefore := false, size := 0, lastHeaderId := 0 }
    main := { solid := false, volume := false, endarc := false, volNo := 0 }
    cstate := CompState.empty
    file := FileHeaderState.empty
    bits := { bitAddr := 0, inAddr := 0 }
    expectedVolNo := 0
    checksumVerified := false
    freed := false }

/-! ## 3. Core Representation Invariants -/

/-- Predicate asserting `w` is a valid positive RAR5 dictionary size (`128 KiB * 2^k`, `k <= 9`). -/
def IsValidDictSize (w : Int) : Prop :=
  ∃ k : Nat, k ≤ 9 ∧ w = ((0x20000 * (2 ^ k) : Nat) : Int)

/--
### `WindowInv`: Circular LZSS Window Representation Invariant
1. `windowSize` is either `0` (before first file / directory) or a power-of-two
   dictionary size in `[128 KiB, 64 MiB]`.
2. `windowMask` equals `windowSize - 1` when `windowSize > 0`, else `0`.
3. `0 <= windowInitSize <= windowAllocSize`.
4. Whenever decompression is initialized (`cs.initialized = true`) with
   `windowSize > 0`, the entire active window `[0, windowSize)` has been
   zero- or data-initialized (`windowSize <= windowInitSize`), preventing C11
   indeterminate-memory reads on LZSS backreferences (`copy_string`, line 3313).

### C Implementation Gaps
- **Gap W1 (`process_head_file` lines 2000–2024 & `do_uncompress_file` line 4108)**:
  When `rar5->main.solid == 1` and Entry 2 declares a larger `window_size` than
  Entry 1 (undetected because `reset_file_context` zeroed `file.solid_window_size`),
  `realloc` grows `window_buf` without zeroing `[old_size, new_size)`, and
  `do_uncompress_file` skips `init_unpack`, violating `windowSize <= windowInitSize`.
- **Gap W2 (`process_head_file` lines 1956, 2028)**:
  A directory entry (`file.dir == 1`) sets `cstate.window_size = 0` while leaving
  `window_buf` non-NULL.
- **Gap W3 (`process_head_file` line 2028 with `switch_multivolume == 1`)**:
  A continuation volume header can overwrite `cstate.window_size` with a smaller
  dictionary size mid-stream while `writePtr - lastWritePtr` and queued filters
  still depend on the previous volume's `window_size`.
-/
def WindowInv (cs : CompState) : Prop :=
  (cs.windowSize = 0 ∨ IsValidDictSize cs.windowSize) ∧
  cs.windowMask = (if cs.windowSize > 0 then cs.windowSize - 1 else 0) ∧
  0 ≤ cs.windowInitSize ∧
  cs.windowInitSize ≤ cs.windowAllocSize ∧
  (cs.initialized = true → cs.windowSize > 0 → cs.windowSize ≤ cs.windowInitSize)

/--
### `SolidResetInv`: Solid & Multivolume Stream Lifecycle Invariant
1. If `file.solid = true` and `!cstate.dataEncrypted`, a solid dictionary must
   already exist (`cstate.windowAllocSize > 0`) and `cstate.windowSize` must
   match the persistent `cstate.solidWindowSize`.
2. At the start of a fresh entry (`writePtr = 0 ∧ lastWritePtr = 0 ∧ lastUnstorePtr = 0`),
   both `dready` slots must be empty (`!dready0.used ∧ !dready1.used`) so stale
   slices from a previous entry cannot be emitted by `use_data` (line 4489).
3. `0 <= lastWritePtr <= writePtr` and `0 <= lastUnstorePtr`.

### C Implementation Gaps
- **Gap S1 (`reset_file_context` lines 885–903)**:
  Omits `clear_data_ready_stack(rar5)`, leaking `dready` across entries into
  `STORE` entries or same-window-size solid entries (`use_data` at line 4489).
- **Gap S2 (`reset_file_context` line 886 vs `process_head_file` line 1988)**:
  `solid_window_size` is stored in `rar5->file` and wiped on every entry reset.
- **Gap S3 (`process_block` line 3824)**:
  Calls `advance_multivolume(a)` on block-aligned volume boundaries without
  setting `cstate.switch_multivolume = 1`, causing `process_head_file` to call
  `reset_file_context` mid-file!
- **Gap S4 (`rar5_read_data_skip` line 4541)**:
  Loops `while (rar5->file.bytes_remaining > 0)` without checking
  `rar5->generic.split_after`, aborting solid skip early at a volume boundary.
-/
def SolidResetInv (s : Rar5State) : Prop :=
  (s.file.solid = true → s.cstate.dataEncrypted = false → s.file.dir = false →
    s.cstate.windowAllocSize > 0 ∧
    s.cstate.solidWindowSize = s.cstate.windowSize) ∧
  (s.cstate.writePtr = 0 ∧ s.cstate.lastWritePtr = 0 ∧ s.cstate.lastUnstorePtr = 0 →
    s.cstate.dready0.used = false ∧ s.cstate.dready1.used = false) ∧
  0 ≤ s.cstate.lastWritePtr ∧
  s.cstate.lastWritePtr ≤ s.cstate.writePtr ∧
  0 ≤ s.cstate.lastUnstorePtr

/-- Inductive predicate asserting filters in a queue are pairwise non-overlapping and ordered. -/
inductive NonOverlappingFilters : List FilterInfo → Prop where
  | nil  : NonOverlappingFilters []
  | cons (f : FilterInfo) (fs : List FilterInfo) :
      (∀ g ∈ fs, f.blockStart + f.blockLength ≤ g.blockStart) →
      NonOverlappingFilters fs →
      NonOverlappingFilters (f :: fs)

/-- Per-filter parameter bounds checked by `parse_filter` and `run_filter`. -/
def ValidFilterItem (windowSize unpackedSize : Int) (f : FilterInfo) : Prop :=
  4 ≤ f.blockLength ∧
  f.blockLength ≤ maxFilterBlockLength ∧
  (windowSize > 0 → f.blockLength ≤ windowSize / 2) ∧
  0 ≤ f.blockStart ∧
  f.blockStart + f.blockLength ≤ unpackedSize ∧
  (f.fltType = .delta → 1 ≤ f.channels ∧ f.channels ≤ 32)

/--
### `FilterQueueInv`: Post-Processing Filter Queue Invariant
1. Filter queue length never exceeds `maxFilterQueueCap` (`8192`).
2. Every queued filter satisfies `ValidFilterItem` (including
   `blockLength <= windowSize / 2`, essential for deadlock freedom with
   `do_uncompress_block`'s `windowSize / 2` throttle!).
3. Filters are pairwise disjoint and ordered (`NonOverlappingFilters`).
4. Every queued filter starts at or after `lastWritePtr`
   (`lastWritePtr <= f.blockStart`), ensuring `push_window_data(lastWritePtr, f.blockStart)`
   never sees `idx_begin > idx_end`!
5. When `filters` is non-empty, `lastBlockLength > 0` and every queued filter
   ends at or before `lastBlockStart + lastBlockLength`.

### C Implementation Gaps
- **Gap F1 (`is_valid_filter_block_start` line 3181)**:
  Checks `if (last_bs == 0 || last_bl == 0) return 1;`. Whenever Filter 1 has
  `block_start == 0`, `last_bs` is `0`, so Filter 2 with `block_start < flt1.end`
  is accepted! After Filter 1 runs (`last_write_ptr = flt1.block_length`),
  `flt2.block_start < last_write_ptr` triggers negative-length wrap-around in
  `push_data` (lines 753–777), disclosing up to `window_size` bytes of `window_buf`.
- **Gap F2 (`is_valid_filter_block_start` line 3177 vs `parse_filter` line 3240)**:
  Casts `uint32_t start` to `(ssize_t)start` (signed 32-bit negative on ILP32
  when `start >= 2^31`) during validation, then adds `uint32_t` unsigned on line 3240,
  and never checks `block_start + block_length <= unpacked_size`.
-/
def FilterQueueInv (cs : CompState) (unpackedSize : Int) : Prop :=
  cs.filters.length ≤ maxFilterQueueCap ∧
  (∀ f ∈ cs.filters, ValidFilterItem cs.windowSize unpackedSize f) ∧
  NonOverlappingFilters cs.filters ∧
  (∀ f ∈ cs.filters, cs.lastWritePtr ≤ f.blockStart) ∧
  (∀ f ∈ cs.filters, cs.lastBlockLength > 0 ∧
    f.blockStart + f.blockLength ≤ cs.lastBlockStart + cs.lastBlockLength)

/-- Well-formedness of an initialized Huffman `DecodeTable`. -/
def ValidDecodeTable (expectedSize expectedQuickBits : Nat) (t : DecodeTable) : Prop :=
  t.valid = true ∧
  t.size = expectedSize ∧
  t.quickBits = expectedQuickBits ∧
  t.upperLimit ≤ 65536 ∧
  1 ≤ t.minQuickLen ∧
  t.minQuickLen ≤ t.maxQuickLen ∧
  t.maxQuickLen ≤ 16

/--
### `HuffmanInv`: BitReader & Huffman Table Invariant
1. `bits.bitAddr < 8` and `0 <= bits.inAddr`.
2. When `blockParsingFinished = false` (an LZSS block is actively open/resumable):
   - `curBlockSize >= 0` and `blockLookaheadPad >= 4` (required by `read_bits_32`
     reading `p[in_addr + 4]` when `in_addr = cur_block_size - 1`);
   - All four LZSS Huffman tables (`ld`, `dd`, `ldd`, `rd`) are valid.

### C Implementation Gaps
- **Gap H1 (`process_block` lines 3925–3938)**:
  Sets `rar5->cstate.block_parsing_finished = 0` BEFORE calling `parse_tables`.
  If `parse_tables` fails (`ARCHIVE_FAILED`), `block_parsing_finished` remains `0`
  with half-mutated tables; a subsequent `rar5_read_data_skip` (in solid mode)
  or `rar5_read_data` retry skips `parse_tables` and runs `do_uncompress_block`
  on the rejected block!
- **Gap H2 (`do_uncompress_block` lines 3415–3492)**:
  `dd` has alphabet `HUFF_DC = 64` (`dist_slot` in `0..63`). For `dist_slot >= 62`
  (`dbits = 30`), `(uint32_t)(2 | (dist_slot & 1)) << 30 >= 0x80000000U`, which
  wraps 32-bit `int dist` negative, bypassing `if (dist >= INT_MAX - low_dist - 1)`
  at line 3456 and skipping the `+3` match-length adjustment at lines 3482–3492.
-/
def HuffmanInv (cs : CompState) (bits : BitReader) : Prop :=
  bits.bitAddr < 8 ∧
  0 ≤ bits.inAddr ∧
  (cs.blockParsingFinished = false →
    0 ≤ cs.curBlockSize ∧
    4 ≤ cs.blockLookaheadPad ∧
    cs.tablesValid = true ∧
    ValidDecodeTable 306 10 cs.ld ∧
    ValidDecodeTable 64 7 cs.dd ∧
    ValidDecodeTable 16 7 cs.ldd ∧
    ValidDecodeTable 44 7 cs.rd)

/--
### `HeaderBoundsInv`: Base-Block & Extra-Area Parsing Bounds Invariant
1. `rawHdrSize <= maxHeaderSize` (`2 MiB`).
2. `bodyStartPos <= curPos` and `curPos - bodyStartPos <= rawHdrSize` (monotonic,
   bounded consumption within the CRC32-verified header bytes, tracked by stream
   offset `position` rather than raw buffer pointers!).
3. `0 <= extraRem` and `extraRem.toNat <= rawHdrSize - (curPos - bodyStartPos)`.
4. `unpackedRaw <= int64Max` (`INT64_MAX`, preventing negative `ssize_t`/`int64_t` wrap).
5. `nameLen < maxNameInBytes` (`8192`, including after `EX_VERSION` suffixing).

### C Implementation Gaps
- **Gap B1 (`rar5_skip_remaining_block` line 2413)**:
  Computes `cur - body_start` via pointer subtraction across `read_var(10)` calls
  that may `free` or `memmove` `a->filter->buffer` (C11 §6.5.6p9 UB / UAF).
- **Gap B2 (`process_head_file_extra` lines 1718, 1727, 1728, 1764)**:
  Subtracts `var_size` from `int64_t extra_data_size` and `uint64_t extra_field_size`
  without underflow checks, then compares `extra_field_size > (uint64_t)extra_data_size`
  where negative `extra_data_size` wraps to `~UINT64_MAX`.
- **Gap B3 (`process_base_block` lines 2534–2539)**:
  `HEAD_FILE` and `HEAD_SERVICE` never check `curPos - bodyStartPos == rawHdrSize`.
- **Gap B4 (`process_head_file` line 2143)**:
  Casts `uint64_t unpacked_size` to `ssize_t` / `la_int64_t` without `<= SSIZE_MAX`.
- **Gap B5 (`parse_file_extra_version` lines 1359–1414)**:
  Appends `;version` per `EX_VERSION` record without bounding total pathname length,
  enabling `O(N^2)` (~550 GB) allocation/copy amplification in a single 2 MiB header.
-/
def HeaderBoundsInv
    (bodyStartPos curPos rawHdrSize : Nat)
    (extraRem : Int)
    (unpackedRaw nameLen : Nat) : Prop :=
  rawHdrSize ≤ maxHeaderSize ∧
  bodyStartPos ≤ curPos ∧
  curPos - bodyStartPos ≤ rawHdrSize ∧
  0 ≤ extraRem ∧
  extraRem.toNat ≤ rawHdrSize - (curPos - bodyStartPos) ∧
  unpackedRaw ≤ int64Max ∧
  nameLen < maxNameInBytes

/--
### `Rar5RepInv`: Composite Top-Level RAR5 Reader Representation Invariant
Holds across public `archive_read_*` API boundaries (`init`, `read_header`,
`read_data`, `read_data_skip`, `cleanup`).
-/
def Rar5RepInv (s : Rar5State) : Prop :=
  (s.freed = true →
    s.cstate.windowAllocSize = 0 ∧
    s.cstate.filters = [] ∧
    s.cstate.dready0.used = false ∧
    s.cstate.dready1.used = false) ∧
  (s.freed = false →
    0 ≤ s.file.bytesRemaining ∧
    0 ≤ s.file.unpackedSize ∧
    WindowInv s.cstate ∧
    SolidResetInv s ∧
    FilterQueueInv s.cstate s.file.unpackedSize ∧
    HuffmanInv s.cstate s.bits)

/-! ## 4. Safe Abstract Transition Contracts -/

/--
Safe `reset_file_context` contract (fixing Gaps S1 & S2 in lines 885–903):
- Clears `dready0` and `dready1` (`clear_data_ready_stack`);
- Preserves `cstate.solidWindowSize` across entries;
- Resets `solidOffset` when `!main.solid`.
-/
def safeResetFileContext (s : Rar5State) : Rar5State :=
  let newSolidOffset :=
    if s.main.solid then s.cstate.solidOffset + s.cstate.writePtr else 0
  { s with
    file := FileHeaderState.empty
    checksumVerified := false
    cstate :=
      { s.cstate with
        solidOffset := newSolidOffset
        writePtr := 0
        lastWritePtr := 0
        lastUnstorePtr := 0
        lastBlockStart := 0
        lastBlockLength := 0
        filters := []
        dready0 := FilterOutputSlot.empty
        dready1 := FilterOutputSlot.empty } }

/--
Safe dictionary growth transition (fixing Gap W1 in lines 2000–2024):
Zero-initializes `[windowInitSize, newSize)` whenever `window_buf` is grown, so
`windowInitSize` tracks the full `newSize`.
-/
def safeGrowWindow (cs : CompState) (newSize : Int) (_hValid : IsValidDictSize newSize) : CompState :=
  let newAlloc := if cs.windowAllocSize < newSize then newSize else cs.windowAllocSize
  let newInit  := if cs.windowInitSize < newSize then newSize else cs.windowInitSize
  { cs with
    windowSize := newSize
    windowAllocSize := newAlloc
    windowInitSize := newInit
    windowMask := if newSize > 0 then newSize - 1 else 0
    dready0 := FilterOutputSlot.empty
    dready1 := FilterOutputSlot.empty }

/-- Compute channels for a filter descriptor (`channels + 1` for delta, `0` otherwise). -/
def computeFilterChannels (fltType : FilterType) (rawChannels : Nat) : Nat :=
  match fltType with
  | .delta => rawChannels + 1
  | _ => 0

/--
Safe filter validation & insertion (`parse_filter`, fixing Gaps F1 & F2 in
lines 3174–3259):
- Uses `cs.lastBlockLength == 0` (NOT `lastBlockStart == 0 || lastBlockLength == 0`!)
  to detect whether a prior filter exists;
- Enforces `cs.lastWritePtr <= blockStart` and `blockStart + blockLength <= unpackedSize`.
-/
def safePushFilter
    (cs : CompState)
    (unpackedSize : Int)
    (relStart : Nat)
    (blockLen : Nat)
    (fltType : FilterType)
    (rawChannels : Nat) : ArchiveStatus × CompState :=
  let blockStart : Int := cs.writePtr + (relStart : Int)
  let blockLength : Int := (blockLen : Int)
  let channels : Nat := computeFilterChannels fltType rawChannels
  let nonOverlapProp : Prop :=
    cs.lastBlockLength = 0 ∨ cs.lastBlockStart + cs.lastBlockLength ≤ blockStart
  let guardProp : Prop :=
    cs.filters.length < maxFilterQueueCap ∧
    4 ≤ blockLength ∧
    blockLength ≤ maxFilterBlockLength ∧
    (cs.windowSize > 0 → blockLength ≤ cs.windowSize / 2) ∧
    0 ≤ blockStart ∧
    cs.lastWritePtr ≤ blockStart ∧
    blockStart + blockLength ≤ unpackedSize ∧
    (fltType = .delta → 1 ≤ channels ∧ channels ≤ 32) ∧
    nonOverlapProp
  if decide guardProp then
    let flt : FilterInfo :=
      { fltType := fltType
        channels := channels
        blockStart := blockStart
        blockLength := blockLength }
    (.ok,
      { cs with
        filters := cs.filters ++ [flt]
        lastBlockStart := blockStart
        lastBlockLength := blockLength })
  else
    (.failed, cs)

/-- Safe bit-reader advance (`skip_bits`, lines 1094–1098). -/
def skipBits (b : BitReader) (n : Nat) : BitReader :=
  let newBits : Nat := b.bitAddr + n
  { bitAddr := newBits % 8
    inAddr := b.inAddr + ((newBits / 8 : Nat) : Int) }

/--
Safe `rar5_read_header` entry contract (fixing Gaps S1, S2, W1, W2, W3, B4):
Validates `unpackedRaw <= int64Max`, preserves `windowSize` on directories and
multivolume continuations, enforces solid dictionary invariance, and resets
per-file context cleanly.
-/
def safeReadHeaderFile
    (s : Rar5State)
    (isDir isSolid splitBefore splitAfter : Bool)
    (dataSize unpackedRaw : Nat)
    (declWindowSize : Int) : ArchiveStatus × Rar5State :=
  if s.freed then
    (.fatal, s)
  else if unpackedRaw > int64Max || dataSize > int64Max then
    (.fatal, s)
  else if isDir && (unpackedRaw != 0 || dataSize != 0) then
    (.fatal, s)
  else if s.cstate.switchMultivolume then
    -- Continuation volume header must match active stream geometry (fixes Gap W3)
    if isDir || declWindowSize != s.cstate.windowSize then
      (.fatal, s)
    else
      let s' :=
        { s with
          generic := { s.generic with splitBefore := splitBefore, splitAfter := splitAfter }
          file := { s.file with bytesRemaining := (dataSize : Int) } }
      (if splitBefore then .retry else .ok, s')
  else
    let s1 := safeResetFileContext s
    if isDir then
      -- Directory does not clobber cstate.windowSize (fixes Gap W2)
      let s2 :=
        { s1 with
          generic := { s1.generic with splitBefore := splitBefore, splitAfter := splitAfter }
          file := { s1.file with dir := true, bytesRemaining := 0, unpackedSize := 0 } }
      (.ok, s2)
    else if isSolid && !s1.cstate.dataEncrypted &&
        (s1.cstate.windowAllocSize ≤ 0 ||
         (s1.cstate.solidWindowSize > 0 && s1.cstate.solidWindowSize != declWindowSize)) then
      (.fatal, s1)
    else
      (.ok,
        { s1 with
          generic := { s1.generic with splitBefore := splitBefore, splitAfter := splitAfter }
          file :=
            { s1.file with
              dir := false
              solid := isSolid
              bytesRemaining := (dataSize : Int)
              unpackedSize := (unpackedRaw : Int) } })

/--
Safe `rar5_read_data` end-of-entry checksum check (fixing Gap in lines 4508–4521):
Uses `lastUnstorePtr` for `STORE` / `service` entries and `lastWritePtr` for
compressed entries, and checks `!generic.splitAfter`.
-/
def safeEntryProgressPtr (s : Rar5State) : Int :=
  if s.file.service || s.cstate.method == 0 then
    s.cstate.lastUnstorePtr
  else
    s.cstate.lastWritePtr

def safeShouldVerifyChecksums (s : Rar5State) : Bool :=
  !s.generic.splitAfter &&
  s.file.bytesRemaining == 0 &&
  safeEntryProgressPtr s == s.file.unpackedSize

/--
Safe `rar5_read_data_skip` continuation predicate (fixing Gap S4 in line 4541):
In a solid archive, skipping must continue across multivolume splits
(`main.volume && generic.splitAfter`) even when `bytesRemaining` hits `0` at the
end of the current volume.
-/
def safeSolidSkipNeedsMore (s : Rar5State) : Bool :=
  s.file.bytesRemaining > 0 || (s.main.volume && s.generic.splitAfter)

/-- Safe `rar5_cleanup` transition (`rar5_cleanup`, lines 4594–4610). -/
def safeCleanupStep (s : Rar5State) : ArchiveStatus × Rar5State :=
  (.ok,
    { s with
      cstate :=
        { s.cstate with
          initialized := false
          windowSize := 0
          windowAllocSize := 0
          windowInitSize := 0
          windowMask := 0
          filters := []
          dready0 := FilterOutputSlot.empty
          dready1 := FilterOutputSlot.empty }
      freed := true })

/-- Abstract safe transition contract for `rar5_read_header` (lines 2688–2723). -/
def read_header
    (s : Rar5State)
    (isDir isSolid splitBefore splitAfter : Bool)
    (dataSize unpackedRaw : Nat)
    (declWindowSize : Int) : ArchiveStatus × Rar5State :=
  safeReadHeaderFile s isDir isSolid splitBefore splitAfter dataSize unpackedRaw declWindowSize

/--
Abstract safe transition contract for `rar5_read_data` (lines 4453–4524).
Models encryption/directory guards, draining `dready`, output progress bounds,
and unified `STORE`/compressed end-of-entry checksum verification.
-/
def read_data (s : Rar5State) (chunkBytes : Nat) : ArchiveStatus × Rar5State :=
  if s.freed then
    (.fatal, s)
  else if s.headersAreEncrypted || s.cstate.dataEncrypted then
    (.failed, s)
  else if s.file.dir then
    (.fatal, s)
  else if s.skipMode == 0 && safeEntryProgressPtr s > s.file.unpackedSize then
    (.fatal, s)
  else if s.cstate.dready0.used then
    (.ok, { s with cstate := { s.cstate with dready0 := FilterOutputSlot.empty } })
  else if s.cstate.dready1.used then
    (.ok, { s with cstate := { s.cstate with dready1 := FilterOutputSlot.empty } })
  else if s.file.eof then
    (.eof, s)
  else
    let step : Int := min s.file.bytesRemaining (chunkBytes : Int)
    if step ≤ 0 then
      (.eof, { s with file := { s.file with eof := true } })
    else if safeEntryProgressPtr s + step > s.file.unpackedSize then
      (if s.main.solid then .fatal else .failed, s)
    else
      let cs' :=
        if s.file.service || s.cstate.method == 0 then
          { s.cstate with lastUnstorePtr := s.cstate.lastUnstorePtr + step }
        else
          { s.cstate with
            writePtr := s.cstate.writePtr + step
            lastWritePtr := s.cstate.lastWritePtr + step }
      let s' :=
        { s with
          cstate := cs'
          file := { s.file with bytesRemaining := s.file.bytesRemaining - step } }
      if safeShouldVerifyChecksums s' then
        (.ok, { s' with file := { s'.file with eof := true }, checksumVerified := true })
      else
        (.ok, s')

/--
Abstract safe transition contract for `rar5_read_data_skip` (lines 4526–4578).
In non-solid (or encrypted) mode, consumes `bytesRemaining` directly; in solid
mode, unpacks remaining stream bytes across any multivolume splits (`splitAfter = false`)
and clears `dready`.
-/
def read_data_skip (s : Rar5State) : ArchiveStatus × Rar5State :=
  if s.freed then
    (.fatal, s)
  else if s.main.solid && !s.cstate.dataEncrypted then
    if s.file.dir then
      (.ok, s)
    else
      (.ok,
        { s with
          generic := { s.generic with splitAfter := false }
          file := { s.file with bytesRemaining := 0, eof := true }
          cstate :=
            { s.cstate with
              writePtr := s.file.unpackedSize
              lastWritePtr := s.file.unpackedSize
              filters := []
              lastBlockStart := 0
              lastBlockLength := 0
              dready0 := FilterOutputSlot.empty
              dready1 := FilterOutputSlot.empty } })
  else
    (.ok,
      { s with
        file := { s.file with bytesRemaining := 0 }
        cstate :=
          { s.cstate with
            dready0 := FilterOutputSlot.empty
            dready1 := FilterOutputSlot.empty } })

/-- Abstract safe transition contract for `rar5_cleanup` (lines 4594–4610). -/
def cleanup (s : Rar5State) : ArchiveStatus × Rar5State :=
  safeCleanupStep s

/-! ## 5. Faithful Models of Buggy C Transitions (For Counterexample Proofs) -/

/--
Exact C logic of `is_valid_filter_block_start` (lines 3174–3194):
`if (last_bs == 0 || last_bl == 0) return 1; if (block_start >= last_bs + last_bl) return 1;`
-/
def cBuggyIsValidFilterBlockStart
    (writePtr lastBlockStart lastBlockLength : Int) (start : Nat) : Bool :=
  let blockStart : Int := (start : Int) + writePtr
  if lastBlockStart == 0 || lastBlockLength == 0 then
    true
  else if blockStart ≥ lastBlockStart + lastBlockLength then
    true
  else
    false

/--
Exact C logic of `reset_file_context` (lines 885–903):
Zeroes `rar5->file` (including `file.solid_window_size = 0`!) and fails to call
`clear_data_ready_stack`.
-/
def cBuggyResetFileContext (s : Rar5State) : Rar5State :=
  let newSolidOffset :=
    if s.main.solid then s.cstate.solidOffset + s.cstate.writePtr else 0
  { s with
    file := FileHeaderState.empty -- wipes file.solidWindowSize to 0!
    cstate :=
      { s.cstate with
        solidOffset := newSolidOffset
        writePtr := 0
        lastWritePtr := 0
        lastUnstorePtr := 0
        lastBlockStart := 0
        lastBlockLength := 0
        filters := [] } } -- dready0 & dready1 NOT cleared!

/--
Exact C logic of `process_head_file_extra` default skip check (lines 1718–1770):
Subtracts `varSize1` and `varSize2` from `int64_t extraDataSize`, then checks
`extraFieldSize > (uint64_t)extraDataSize`.
-/
def cBuggyExtraDefaultAllowsSkip
    (initialExtraDataSize : Int)
    (varSize1 varSize2 : Nat)
    (rawExtraFieldSize : UInt64) : Bool :=
  let extraAfterVars : Int := initialExtraDataSize - (varSize1 : Int) - (varSize2 : Int)
  let fieldAfterId : UInt64 := rawExtraFieldSize - UInt64.ofNat varSize2
  let castRemaining : UInt64 := UInt64.ofInt extraAfterVars
  !(fieldAfterId > castRemaining)

/--
Exact C logic of `rar5_read_data` end-of-file checksum trigger (lines 4508–4509):
`if (rar5->file.bytes_remaining == 0 && rar5->cstate.last_write_ptr == rar5->file.unpacked_size)`
-/
def cBuggyShouldVerifyChecksums (s : Rar5State) : Bool :=
  s.file.bytesRemaining == 0 && s.cstate.lastWritePtr == s.file.unpackedSize

/--
Exact C logic of `rar5_read_data_skip` solid loop condition (line 4541):
`while (rar5->file.bytes_remaining > 0)` (ignoring `rar5->generic.split_after`).
-/
def cBuggySolidSkipNeedsMore (s : Rar5State) : Bool :=
  s.file.bytesRemaining > 0

/--
Exact C logic of `process_block` table-loading transition (lines 3925–3949):
Sets `block_parsing_finished = 0` BEFORE `parse_tables`, so if `parse_tables`
fails (`tableParseOk = false`), `blockParsingFinished` stays `false` and the
next call enters the `else` branch and invokes `do_uncompress_block` directly!
-/
def cBuggyOpenBlock (cs : CompState) (tablePresent tableParseOk : Bool) : ArchiveStatus × CompState :=
  let cs1 := { cs with blockParsingFinished := false }
  if tablePresent then
    if tableParseOk then
      (.ok, { cs1 with tablesValid := true })
    else
      (.failed, { cs1 with tablesValid := false })
  else
    (.ok, cs1)

/--
Single iteration of `uncompress_file -> do_uncompress_file -> process_block ->
do_uncompress_block` (lines 3330–3338, 4126–4223) when an uncompressed block is
open (`blockParsingFinished = false`) and a filter sits at the head of `filters`.
-/
def cBuggyUncompressIter (cs : CompState) (flt : FilterInfo) : ArchiveStatus × CompState :=
  let csAfterBlock :=
    if cs.allFiltersApplied then
      if cs.writePtr - cs.lastWritePtr > cs.windowSize / 2 then
        -- Line 3331: throttle breaks immediately without advancing bits or setting finished!
        cs
      else
        { cs with blockParsingFinished := true }
    else
      cs
  if csAfterBlock.allFiltersApplied && csAfterBlock.lastWritePtr == csAfterBlock.writePtr then
    (.eof, csAfterBlock)
  else
    if csAfterBlock.writePtr > flt.blockStart &&
       csAfterBlock.writePtr ≥ flt.blockStart + flt.blockLength then
      (.ok, { csAfterBlock with allFiltersApplied := false, lastWritePtr := flt.blockStart + flt.blockLength })
    else
      let csAfterApply := { csAfterBlock with allFiltersApplied := true }
      let maxEndPos := min flt.blockStart csAfterApply.writePtr
      if maxEndPos == csAfterApply.lastWritePtr then
        -- Line 4199: returns ARCHIVE_RETRY to `uncompress_file`'s `while (1)` loop!
        (.retry, csAfterApply)
      else
        (.ok, { csAfterApply with lastWritePtr := maxEndPos })

/--
Exact C 32-bit signed distance calculation in `do_uncompress_block`
(lines 3391, 3415–3423, 3456, 3482) for `dist_slot >= 4` with `add = 0, low_dist = 0`.
-/
def cBuggyDecodeDist32 (distSlot : UInt32) : Int32 :=
  let dbits : UInt32 := distSlot / 2 - 1
  let shifted : UInt32 := (2 ||| (distSlot &&& 1)) <<< dbits
  let distU32 : UInt32 := 1 + shifted
  distU32.toInt32

/-! ## 6. Positive Safety & Invariant-Preservation Theorems -/

/-- Theorem 1: `initState` satisfies the full `Rar5RepInv` representation invariant. -/
theorem initState_satisfies_inv : Rar5RepInv initState := by
  unfold Rar5RepInv WindowInv SolidResetInv FilterQueueInv HuffmanInv
  unfold initState CompState.empty FileHeaderState.empty FilterOutputSlot.empty
  dsimp only
  constructor
  · intro hFreed
    cases hFreed
  · intro _
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
    · refine ⟨Or.inl rfl, by decide, by omega, by omega, ?_⟩
      intro hInit
      cases hInit
    · refine ⟨?_, ?_, by omega, by omega, by omega⟩
      · intro hSolid
        cases hSolid
      · intro _
        exact ⟨rfl, rfl⟩
    · refine ⟨by decide, ?_, NonOverlappingFilters.nil, ?_, ?_⟩
      · intro f hf; cases hf
      · intro f hf; cases hf
      · intro f hf; cases hf
    · refine ⟨by omega, by omega, ?_⟩
      intro hFin
      cases hFin

/-- Theorem 2: `safeCleanupStep` establishes the post-free resource invariant without leaks. -/
theorem safeCleanupStep_preserves_inv (s : Rar5State) :
    Rar5RepInv (safeCleanupStep s).2 := by
  unfold safeCleanupStep Rar5RepInv FilterOutputSlot.empty
  dsimp only
  constructor
  · intro _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hNotFreed
    cases hNotFreed

/-- Theorem 3: `safeResetFileContext` clears `dready` and preserves `cstate.solidWindowSize`. -/
theorem safeResetFileContext_clears_dready_and_preserves_solid_window (s : Rar5State) :
    let s' := safeResetFileContext s
    s'.cstate.dready0.used = false ∧
    s'.cstate.dready1.used = false ∧
    s'.cstate.solidWindowSize = s.cstate.solidWindowSize ∧
    s'.cstate.filters = [] := by
  unfold safeResetFileContext FilterOutputSlot.empty
  dsimp only
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 4: Zero-filling grown dictionary regions in `safeGrowWindow` preserves `WindowInv`. -/
theorem safeGrowWindow_preserves_WindowInv
    (cs : CompState) (newSize : Int)
    (hInv : WindowInv cs) (hDict : IsValidDictSize newSize) :
    WindowInv (safeGrowWindow cs newSize hDict) := by
  rcases hInv with ⟨_, _, hInitNonNeg, hInitLeAlloc, _⟩
  rcases hDict with ⟨k, hk, hEq⟩
  have hPow : 0 < 2 ^ k := Nat.two_pow_pos k
  have hPosNat : 0 < 0x20000 * 2 ^ k := Nat.mul_pos (by omega) hPow
  have hPos : newSize > 0 := by omega
  unfold safeGrowWindow WindowInv
  dsimp only
  refine ⟨Or.inr ⟨k, hk, hEq⟩, rfl, ?_, ?_, ?_⟩
  · split <;> omega
  · split <;> split <;> omega
  · intro _ _
    split <;> omega

/-- Helper: appending a filter after `lastBlockStart + lastBlockLength` preserves `NonOverlappingFilters`. -/
theorem nonOverlapping_append_singleton
    (fs : List FilterInfo) (f : FilterInfo)
    (hNo : NonOverlappingFilters fs)
    (hAfterAll : ∀ g ∈ fs, g.blockStart + g.blockLength ≤ f.blockStart) :
    NonOverlappingFilters (fs ++ [f]) := by
  induction hNo with
  | nil =>
      apply NonOverlappingFilters.cons
      · intro g hg
        cases hg
      · exact NonOverlappingFilters.nil
  | cons hd tl hHd _hTl ih =>
      apply NonOverlappingFilters.cons
      · intro g hg
        simp only [List.append_eq, List.mem_append, List.mem_singleton] at hg
        cases hg with
        | inl hInTl => exact hHd g hInTl
        | inr hInSingle =>
            subst hInSingle
            exact hAfterAll hd (List.Mem.head tl)
      · apply ih
        intro g hg
        exact hAfterAll g (List.Mem.tail hd hg)

/-- Theorem 5: `safePushFilter` preserves `FilterQueueInv` on success. -/
theorem safePushFilter_preserves_FilterQueueInv
    (cs : CompState) (unpackedSize : Int)
    (relStart blockLen : Nat) (fltType : FilterType) (rawChannels : Nat)
    (hInv : FilterQueueInv cs unpackedSize)
    (hEmptySentinel : cs.lastBlockLength = 0 → cs.filters = []) :
    let res := safePushFilter cs unpackedSize relStart blockLen fltType rawChannels
    res.1 = .ok → FilterQueueInv res.2 unpackedSize := by
  unfold safePushFilter
  dsimp only
  split
  · next hDec =>
    intro _
    have hGuard := of_decide_eq_true hDec
    rcases hGuard with
      ⟨hCap, hMinLen, hMaxLen, hHalfWin, hStartNonNeg, hAfterLastWrite,
       hInUnpacked, hDeltaCh, hNonOverlap⟩
    rcases hInv with ⟨_, hItems, hNoOverlap, hAfterWriteAll, hTailBound⟩
    unfold FilterQueueInv
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · intro g hg
      rw [List.mem_append] at hg
      cases hg with
      | inl hOld => exact hItems g hOld
      | inr hNew =>
          rw [List.mem_singleton] at hNew
          subst hNew
          exact ⟨hMinLen, hMaxLen, hHalfWin, hStartNonNeg, hInUnpacked, hDeltaCh⟩
    · cases hNonOverlap with
      | inl hZero =>
          rw [hEmptySentinel hZero]
          apply NonOverlappingFilters.cons
          · intro g hg; cases hg
          · exact NonOverlappingFilters.nil
      | inr hAfterPrev =>
          apply nonOverlapping_append_singleton cs.filters _ hNoOverlap
          intro g hg
          have ⟨_, hGe⟩ := hTailBound g hg
          dsimp only
          omega
    · intro g hg
      rw [List.mem_append] at hg
      cases hg with
      | inl hOld => exact hAfterWriteAll g hOld
      | inr hNew =>
          rw [List.mem_singleton] at hNew
          subst hNew
          exact hAfterLastWrite
    · intro g hg
      rw [List.mem_append] at hg
      cases hg with
      | inl hOld =>
          cases hNonOverlap with
          | inl hZero =>
              rw [hEmptySentinel hZero] at hOld
              cases hOld
          | inr hAfterPrev =>
              have ⟨_, hGe⟩ := hTailBound g hOld
              omega
      | inr hNew =>
          rw [List.mem_singleton] at hNew
          subst hNew
          dsimp only
          omega
  · intro hOk
    cases hOk

/--
Theorem 6 (**Throttle-Filter Deadlock Freedom**):
Whenever `FilterQueueInv` holds (`flt.blockLength <= windowSize / 2` and
`lastWritePtr <= flt.blockStart`), if the head filter `flt` is NOT yet fully
covered by unpacked bytes (`writePtr < flt.blockStart + flt.blockLength`) AND
no pre-filter bytes can be flushed (`min flt.blockStart writePtr = lastWritePtr`,
with `lastWritePtr < writePtr`), then `writePtr - lastWritePtr < windowSize / 2`!

This proves mathematically that `do_uncompress_block`'s throttle check
(`write_ptr - last_write_ptr > window_size >> 1`, line 3331) CANNOT deadlock
against `do_uncompress_file`'s `ARCHIVE_RETRY` loop PROVIDED `windowSize` is not
shrunk mid-entry (which is why multivolume `window_size` shrinking in Gap W3
triggers an infinite loop!).
-/
theorem throttle_filter_no_deadlock
    (windowSize writePtr lastWritePtr : Int) (flt : FilterInfo)
    (_hWinPos : windowSize > 0)
    (hHalf : flt.blockLength ≤ windowSize / 2)
    (_hOrder : lastWritePtr ≤ flt.blockStart)
    (hProgress : lastWritePtr < writePtr)
    (hNotReady : writePtr < flt.blockStart + flt.blockLength)
    (hNoPreFlush : min flt.blockStart writePtr = lastWritePtr) :
    writePtr - lastWritePtr < windowSize / 2 := by
  omega

/--
Theorem 7 (**BitReader Strict Progress & Normalization**):
Skipping `n` bits (`1 <= n <= 16`) from a normalized `BitReader` (`bitAddr < 8`,
`0 <= inAddr`) preserves normalization (`bitAddr < 8`, `0 <= inAddr`) and
strictly advances `bitPos` by exactly `n` bits (guaranteeing termination of
`decode_number` / `do_uncompress_block` over a finite block).
-/
theorem bitReader_skipBits_strict_progress
    (b : BitReader) (n : Nat)
    (_hBit : b.bitAddr < 8) (hIn : 0 ≤ b.inAddr) (hPos : 1 ≤ n) :
    let b' := skipBits b n
    b'.bitAddr < 8 ∧ 0 ≤ b'.inAddr ∧ b'.bitPos = b.bitPos + (n : Int) ∧ b.bitPos < b'.bitPos := by
  unfold skipBits BitReader.bitPos
  dsimp only
  refine ⟨Nat.mod_lt _ (by omega), by omega, by omega, by omega⟩

/--
Theorem 8 (**Circular Window Masking Bounds**):
For any positive window size `w > 0`, modular/masked indexing `idx % w` always
produces a valid array index in `[0, w)`.
-/
theorem circular_index_in_bounds (idx w : Int) (hw : 0 < w) :
    0 ≤ idx % w ∧ idx % w < w :=
  ⟨Int.emod_nonneg idx (by omega), Int.emod_lt_of_pos idx hw⟩

/--
Theorem 9 (**`safeReadHeaderFile` Rejects Multivolume Window Shrink & Preserves
Directory Window Size**):
1. On a multivolume continuation (`switchMultivolume = true`), any mismatched
   `declWindowSize != s.cstate.windowSize` is rejected with `.fatal`.
2. On a fresh directory entry (`isDir = true`, `switchMultivolume = false`),
   `cstate.windowSize` is preserved (not zeroed).
-/
theorem safeReadHeaderFile_protects_windowSize
    (s : Rar5State) (hNotFreed : s.freed = false) :
    (∀ declW, declW ≠ s.cstate.windowSize → s.cstate.switchMultivolume = true →
      (safeReadHeaderFile s false false true false 100 1000 declW).1 = .fatal) ∧
    (s.cstate.switchMultivolume = false →
      (safeReadHeaderFile s true false false false 0 0 0).2.cstate.windowSize = s.cstate.windowSize) := by
  constructor
  · intro declW hNe hMv
    unfold safeReadHeaderFile int64Max
    simp [hNotFreed, hMv, hNe]
  · intro hNoMv
    unfold safeReadHeaderFile safeResetFileContext int64Max
    simp [hNotFreed, hNoMv]

/--
Theorem 10 (**`read_data_skip` Preserves `Rar5RepInv`**):
Executing the safe `read_data_skip` contract from any valid `Rar5RepInv` state
preserves `Rar5RepInv` across both solid (including multivolume) and non-solid archives.
-/
theorem read_data_skip_preserves_inv (s : Rar5State) (hInv : Rar5RepInv s) :
    Rar5RepInv (read_data_skip s).2 := by
  unfold read_data_skip
  split
  · exact hInv
  · next hNotFreedBool =>
    have hNotFreed : s.freed = false := by
      cases hf : s.freed
      · rfl
      · exfalso; exact hNotFreedBool hf
    have hInvOrig := hInv
    rcases hInv with ⟨_, hLive⟩
    rcases hLive hNotFreed with ⟨_, hUnpackedNonNeg, hWin, hSolid, hFlt, hHuff⟩
    rcases hWin with ⟨hWinDict, hWinMask, hWinInit0, hWinInitLe, hWinInitFull⟩
    rcases hSolid with ⟨hSolidMatch, _, hLastWrite0, hLastLeWrite, hLastUnstore0⟩
    rcases hHuff with ⟨hBitAddr, hInAddr, hHuffActive⟩
    split
    · split
      · exact hInvOrig
      · unfold Rar5RepInv WindowInv SolidResetInv FilterQueueInv HuffmanInv FilterOutputSlot.empty
        dsimp only
        constructor
        · intro hf; rw [hNotFreed] at hf; cases hf
        · intro _
          refine ⟨by omega, hUnpackedNonNeg, ?_, ?_, ?_, ?_⟩
          · exact ⟨hWinDict, hWinMask, hWinInit0, hWinInitLe, hWinInitFull⟩
          · refine ⟨hSolidMatch, ?_, hUnpackedNonNeg, by omega, hLastUnstore0⟩
            intro _; exact ⟨rfl, rfl⟩
          · refine ⟨by decide, ?_, NonOverlappingFilters.nil, ?_, ?_⟩
            · intro f hf; cases hf
            · intro f hf; cases hf
            · intro f hf; cases hf
          · exact ⟨hBitAddr, hInAddr, hHuffActive⟩
    · rcases hFlt with ⟨hFltCap, hFltItems, hFltNoOverlap, hFltOrder, hFltTail⟩
      unfold Rar5RepInv WindowInv SolidResetInv FilterQueueInv HuffmanInv FilterOutputSlot.empty
      dsimp only
      constructor
      · intro hf; rw [hNotFreed] at hf; cases hf
      · intro _
        refine ⟨by omega, hUnpackedNonNeg, ?_, ?_, ?_, ?_⟩
        · exact ⟨hWinDict, hWinMask, hWinInit0, hWinInitLe, hWinInitFull⟩
        · refine ⟨hSolidMatch, ?_, hLastWrite0, hLastLeWrite, hLastUnstore0⟩
          intro _; exact ⟨rfl, rfl⟩
        · exact ⟨hFltCap, hFltItems, hFltNoOverlap, hFltOrder, hFltTail⟩
        · exact ⟨hBitAddr, hInAddr, hHuffActive⟩

/-! ## 7. Counterexample-Characterizing Theorems (Witnessing Real C Bugs) -/

/--
Bug Theorem 1 (**Filter `last_bs == 0` Sentinel Bypass — `rar5.c` line 3181**):
When Filter 1 starts at offset `0` (`blockStart = 0, blockLength = 100`),
`last_block_start` is `0` and `last_block_length` is `100`.
If Filter 2 is declared at `writePtr = 10` with `start = 0` (`blockStart = 10`,
`blockLength = 100`), `cBuggyIsValidFilterBlockStart` returns `true`, even though:
1. Filter 2 (`[10, 110)`) overlaps Filter 1 (`[0, 100)`);
2. After Filter 1 executes (`lastWritePtr = 100`), `flt2.blockStart = 10 < 100 = lastWritePtr`,
   causing `push_window_data(100, 10)` to wrap modulo `window_mask` and leak
   `window_size - 90` bytes of raw `window_buf`!
-/
theorem cBuggyIsValidFilterStart_accepts_overlapping_filter :
    let flt1 : FilterInfo := { fltType := .e8, channels := 0, blockStart := 0, blockLength := 100 }
    let flt2 : FilterInfo := { fltType := .e8, channels := 0, blockStart := 10, blockLength := 100 }
    cBuggyIsValidFilterBlockStart 10 flt1.blockStart flt1.blockLength 0 = true ∧
    flt2.blockStart < flt1.blockStart + flt1.blockLength ∧
    ¬ NonOverlappingFilters [flt1, flt2] := by
  refine ⟨by decide, by decide, ?_⟩
  intro hNo
  cases hNo with
  | cons _ _ hHead _ =>
      have hLe := hHead { fltType := .e8, channels := 0, blockStart := 10, blockLength := 100 } (by simp)
      dsimp only at hLe
      omega

/--
Bug Theorem 2 (**`reset_file_context` Wipes `solid_window_size` & Leaks `dready` —
`rar5.c` lines 885–903, 1988, 4489**):
Starting from a solid archive state where `file.solidWindowSize = 0x20000` and
`dready1.used = true` (left over after a partial read of a wrapped window push),
`cBuggyResetFileContext` resets `file.solidWindowSize` to `0` AND leaves
`dready1.used = true`, violating `SolidResetInv`!
-/
theorem cBuggyResetFileContext_loses_solidWindowSize_and_leaks_dready :
    let s : Rar5State :=
      { initState with
        main := { initState.main with solid := true }
        file := { initState.file with solid := true, solidWindowSize := 0x20000 }
        cstate :=
          { initState.cstate with
            windowSize := 0x20000
            windowAllocSize := 0x20000
            windowInitSize := 0x20000
            dready1 := { used := true, origin := .windowBuf, offset := 50000, size := 200 } } }
    let s' := cBuggyResetFileContext s
    s'.file.solidWindowSize = 0 ∧
    s'.cstate.dready1.used = true ∧
    ¬ SolidResetInv s' := by
  refine ⟨rfl, rfl, ?_⟩
  intro hInv
  rcases hInv with ⟨_, hDreadyClean, _, _, _⟩
  have ⟨_, hD1⟩ := hDreadyClean ⟨rfl, rfl, rfl⟩
  cases hD1

/--
Bug Theorem 3 (**Deterministic Zero-I/O Infinite Loop on Multivolume `window_size`
Shrink — `rar5.c` lines 2028, 3331, 4137, 4188, 4216**):
Suppose Volume 1 (`windowSize = 1 MiB`) queued `flt = (blockStart = 0, blockLength = 256 KiB)`
and unpacked `192 KiB` (`writePtr = 0x30000, lastWritePtr = 0`), and Volume 2's
continuation `HEAD_FILE` shrinks `cstate.windowSize` to `128 KiB` (`0x20000`)
with `blockParsingFinished = false` and `allFiltersApplied = true`.
Then `cBuggyUncompressIter` returns `(.retry, cs)` with the **exact same `CompState`**,
proving `uncompress_file`'s `while (ret == ARCHIVE_RETRY)` loop spins forever!
-/
theorem cBuggyMultivolShrink_causes_zero_progress_spin :
    let flt : FilterInfo :=
      { fltType := .e8, channels := 0, blockStart := 0, blockLength := 0x40000 }
    let cs : CompState :=
      { CompState.empty with
        initialized := true
        allFiltersApplied := true
        blockParsingFinished := false
        windowSize := 0x20000
        windowAllocSize := 0x100000
        windowInitSize := 0x100000
        windowMask := 0x1ffff
        writePtr := 0x30000
        lastWritePtr := 0
        filters := [flt] }
    cBuggyUncompressIter cs flt = (.retry, cs) := by
  decide

/--
Bug Theorem 4 (**`process_head_file_extra` Signed-to-Unsigned Underflow Bypass —
`rar5.c` lines 1718–1770**):
When `extra_data_size = 1`, reading a 10-byte `extra_field_size` varint
(`0x7fffffffffffffff`) and a 1-byte `extra_field_id` varint makes `extra_data_size = -10`.
Casting `(uint64_t)extra_data_size` yields `0xfffffffffffffff6`, which is GREATER
than `extra_field_size - 1` (`0x7ffffffffffffffe`), so the bounds check
`extra_field_size > (uint64_t)extra_data_size` fails to trigger (`AllowsSkip = true`)!
-/
theorem cBuggyExtraUnderflow_bypasses_bounds_check :
    cBuggyExtraDefaultAllowsSkip 1 10 1 0x7fffffffffffffff = true := by
  decide

/--
Bug Theorem 5 (**`STORE` (`-m0`) Checksum Verification Dead Code —
`rar5.c` lines 4284–4288, 4508–4521**):
For ANY non-empty `STORE` (`method = 0`) entry (`unpackedSize > 0`) that has
finished unstoring all bytes (`bytesRemaining = 0`, `lastUnstorePtr = unpackedSize`,
while `lastWritePtr = 0`), `cBuggyShouldVerifyChecksums` evaluates to `false`,
whereas `safeShouldVerifyChecksums` evaluates to `true`.
-/
theorem cBuggyStoreChecksum_never_verifies (n : Int) (hPos : 0 < n) :
    let s : Rar5State :=
      { initState with
        cstate := { initState.cstate with method := 0, lastWritePtr := 0, lastUnstorePtr := n }
        file := { initState.file with bytesRemaining := 0, unpackedSize := n } }
    cBuggyShouldVerifyChecksums s = false ∧ safeShouldVerifyChecksums s = true := by
  unfold cBuggyShouldVerifyChecksums safeShouldVerifyChecksums safeEntryProgressPtr initState
  unfold CompState.empty FileHeaderState.empty
  dsimp only
  constructor
  · simp only [beq_self_eq_true, Bool.true_and]
    exact beq_false_of_ne (by omega)
  · simp

/--
Bug Theorem 6 (**32-bit Signed Distance Wrap on `dist_slot = 62` —
`rar5.c` lines 3415–3423, 3456, 3482**):
In `do_uncompress_block`, `dd` has size `HUFF_DC = 64` (`dist_slot` in `0..63`).
When `dist_slot = 62` (`dbits = 30`), `cBuggyDecodeDist32 62` wraps `int dist`
to `-2147483647 < 0`, simultaneously bypassing the overflow guard
`dist >= INT32_MAX - 1` AND failing the length-adjustment condition `dist > 0x100`!
-/
theorem cBuggyDistSlot62_wraps_int32_negative :
    let d := cBuggyDecodeDist32 62
    d = (-2147483647 : Int32) ∧
    decide (d < 0) = true ∧
    decide (d ≥ (2147483646 : Int32)) = false ∧
    decide (d > (0x100 : Int32)) = false := by
  decide

/--
Bug Theorem 7 (**Premature `block_parsing_finished = 0` Before `parse_tables` —
`rar5.c` lines 3925–3949**):
When `tablePresent = true` and `parse_tables` fails (`tableParseOk = false`),
`cBuggyOpenBlock` returns `.failed` with `blockParsingFinished = false` and
`tablesValid = false` (violating `HuffmanInv` and causing the next `process_block`
call in `rar5_read_data_skip` / retry to skip `parse_tables`!).
-/
theorem cBuggyOpenBlock_violates_HuffmanInv_on_table_failure :
    let res := cBuggyOpenBlock CompState.empty true false
    res.1 = .failed ∧
    res.2.blockParsingFinished = false ∧
    res.2.tablesValid = false ∧
    ¬ HuffmanInv res.2 { bitAddr := 0, inAddr := 0 } := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hInv
  rcases hInv with ⟨_, _, hActive⟩
  have ⟨_, _, hValid, _, _, _, _⟩ := hActive rfl
  cases hValid

/--
Bug Theorem 8 (**Premature Exit of `rar5_read_data_skip` on Multivolume Solid
Split — `rar5.c` line 4541**):
When a solid multivolume entry finishes Volume 1 (`bytesRemaining = 0`) with
`main.volume = true` and `generic.splitAfter = true`, `cBuggySolidSkipNeedsMore`
returns `false` (aborting solid decompression early), whereas
`safeSolidSkipNeedsMore` returns `true`.
-/
theorem cBuggySolidSkip_stops_early_on_multivol :
    let s : Rar5State :=
      { initState with
        main := { initState.main with solid := true, volume := true }
        generic := { initState.generic with splitAfter := true }
        file := { initState.file with bytesRemaining := 0, unpackedSize := 4096 } }
    cBuggySolidSkipNeedsMore s = false ∧ safeSolidSkipNeedsMore s = true := by
  decide

end LibarchiveF.Model.Rar5TopDown
