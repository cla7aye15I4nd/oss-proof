/-
  LibarchiveF/Model/SevenZipTopDown.lean

  Top-down formal state and safety invariant model for libarchive's 7-Zip format
  reader (`libarchive/archive_read_support_format_7zip.c`) and PPMd7/PPMd8
  sub-allocator (`libarchive/archive_ppmd7.c`, `libarchive/archive_ppmd8.c`).

  Every docstring documents both the mathematical representation invariant and
  the exact locations where the C implementation omits or weakens checks
  required by that invariant.
-/

namespace LibarchiveF.Model.SevenZipTopDown

/-! ## 1. Codec Identifiers and Properties -/

/-- Codec identifiers recognized by `archive_read_support_format_7zip.c` (lines 93-116). -/
inductive CodecId where
  | copy
  | lzma
  | lzma2
  | deflate
  | bz2
  | ppmd
  | zstd
  | delta
  | x86
  | x86Bcj2
  | powerpc
  | ia64
  | arm
  | armThumb
  | arm64
  | riscv
  | sparc
  | cryptoMainZip
  | cryptoRar29
  | cryptoAes256Sha256
  | unknown (rawId : Nat)
  deriving DecidableEq, Repr

namespace CodecId

/-- Mirrors `compressor_name(codec) != NULL` (`archive_read_support_format_7zip.c:3947-3959`). -/
def isCompressor : CodecId → Bool
  | .copy | .lzma | .lzma2 | .deflate | .bz2 | .ppmd | .zstd => true
  | _ => false

/-- Mirrors `bcj_lookahead(codec2)` (`archive_read_support_format_7zip.c:4882-4900`).
    Returns the instruction lookahead width (and minimum progress buffer size)
    for in-house BCJ filters, or `0` otherwise. -/
def bcjLookahead : CodecId → Nat
  | .x86      => 5
  | .riscv    => 8
  | .ia64     => 16
  | .arm | .armThumb | .arm64 | .powerpc | .sparc => 4
  | _         => 0

/-- Encryption codecs checked in `read_header` (line 969) and `setup_decode_folder` (line 3985). -/
def isCrypto : CodecId → Bool
  | .cryptoMainZip | .cryptoRar29 | .cryptoAes256Sha256 => true
  | _ => false

/-- Filter codecs permitted as `coder2` (`init_decompression`, lines 1366-1375, 1474-1531). -/
def isFilter : CodecId → Bool
  | .delta | .x86Bcj2 => true
  | c => bcjLookahead c != 0

end CodecId

/-! ## 2. Folder Graph (`struct _7z_coder`, `BindPair`, `struct _7z_folder`) -/

/-- Mirrors `struct _7z_coder` (`archive_read_support_format_7zip.c:176-182`). -/
structure Coder where
  codec          : CodecId
  numInStreams   : Nat
  numOutStreams  : Nat
  propertiesSize : Nat
  deriving DecidableEq, Repr

/-- Mirrors an element of `folder->bindPairs` (`archive_read_support_format_7zip.c:184-187`),
    connecting producer output port `outIndex` to consumer input port `inIndex`. -/
structure BindPair where
  inIndex  : Nat
  outIndex : Nat
  deriving DecidableEq, Repr

/-- Mirrors `struct _7z_folder` (`archive_read_support_format_7zip.c:174-198`).
    Note: C discards the explicit `packedStreams` port indices in `read_Folder`
    (lines 2495-2499), storing only `numPackedStreams`; we retain `packedStreams`
    in the model to state the full port-partition invariant. -/
structure FolderDAG where
  coders           : List Coder
  bindPairs        : List BindPair
  packedStreams    : List Nat
  unPackSizes      : List Nat
  digestDefined    : Bool
  digest           : UInt32
  numUnpackStreams : Nat
  packIndex        : Nat
  skippedBytes     : Nat
  deriving DecidableEq, Repr

namespace FolderDAG

/-- Total input ports across all coders in the folder. -/
def totalInStreams (f : FolderDAG) : Nat :=
  f.coders.foldl (fun acc c => acc + c.numInStreams) 0

/-- Total output ports across all coders in the folder. -/
def totalOutStreams (f : FolderDAG) : Nat :=
  f.coders.foldl (fun acc c => acc + c.numOutStreams) 0

/-- Helper mapping a flat port index `p` to the index of the coder owning it. -/
def findCoderForPort : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | arity :: rest, coderIdx, port =>
    if port < arity then
      some coderIdx
    else
      findCoderForPort rest (coderIdx + 1) (port - arity)

/-- Maps a flat input-stream port index to its owning coder index (`0 .. coders.length - 1`). -/
def inPortOwner (f : FolderDAG) (inPort : Nat) : Option Nat :=
  findCoderForPort (f.coders.map Coder.numInStreams) 0 inPort

/-- Maps a flat output-stream port index to its owning coder index (`0 .. coders.length - 1`). -/
def outPortOwner (f : FolderDAG) (outPort : Nat) : Option Nat :=
  findCoderForPort (f.coders.map Coder.numOutStreams) 0 outPort

/-- Mirrors `folder_uncompressed_size` (`archive_read_support_format_7zip.c:2630-2645`):
    scans output ports from highest index down to `0` and returns `unPackSizes[n]`
    for the first port `n` not appearing as any `bp.outIndex`. -/
def cFolderUncompressedSize (f : FolderDAG) : Nat :=
  let rec go : Nat → Nat
    | 0 => 0
    | n + 1 =>
      if f.bindPairs.any (fun bp => bp.outIndex == n) then
        go n
      else
        f.unPackSizes.getD n 0
  go f.totalOutStreams

/-- Topological ranking witness for `FolderDAG`: assigns each coder `i` a rank `rank i`
    such that every `BindPair` flows strictly forward (`rank srcCoder < rank dstCoder`). -/
def CoderRankAcyclic (f : FolderDAG) (rank : Nat → Nat) : Prop :=
  ∀ bp ∈ f.bindPairs,
    ∀ srcCoder dstCoder,
      f.outPortOwner bp.outIndex = some srcCoder →
      f.inPortOwner bp.inIndex = some dstCoder →
      rank srcCoder < rank dstCoder

/-- BCJ2 structural arity invariant (`archive_read_support_format_7zip.c:4054-4135`).

    **C implementation gaps:**
    1. In `setup_decode_folder` lines 4103-4121 (`7z a -m0=BCJ2 ...` 4-coder form),
       the code selects `coder1` as `coders[2]`, `coders[1]`, or `coders[0]` depending
       on which two of `fc[0..2]` are `_7Z_COPY`, yet line 4121 unconditionally sets
       `remaining = folder->unPackSize[2]`. When `coder1` is `coders[1]` or `coders[0]`,
       `main_stream_bytes_remaining` gets a `COPY` sub-stream's size instead of the
       main stream's uncompressed size (`unPackSize[1]` or `unPackSize[0]`).
    2. `read_Folder` does not validate that `BCJ2` itself has `numInStreams = 4` and
       `numOutStreams = 1`, checking only aggregate sums `numInStreams == 7, numOutStreams == 4`
       or `numInStreams == 5, numOutStreams == 2`. -/
def Bcj2ArityInv (f : FolderDAG) : Prop :=
  let bcj2Coders := f.coders.filter (fun c => c.codec == .x86Bcj2)
  bcj2Coders.length ≤ 1 ∧
  (bcj2Coders.length = 1 →
    f.packedStreams.length = 4 ∧
    ∀ c ∈ f.coders,
      if c.codec = .x86Bcj2 then
        c.numInStreams = 4 ∧ c.numOutStreams = 1
      else
        c.numInStreams = 1 ∧ c.numOutStreams = 1)

/-- Full well-formedness invariant for a 7-Zip `Folder` coder graph.

    **C implementation gaps (`read_Folder`, lines 2374-2505, and `setup_decode_folder`, lines 3962-4246):**
    1. **Missing port-index bounds:** `read_Folder` (lines 2473-2478) parses `inIndex`
       and `outIndex` via `parse_7zip_size` (allowing up to `100,000,000`) without
       checking `inIndex < numInStreamsTotal` or `outIndex < numOutStreamsTotal`.
    2. **Missing port uniqueness (`Nodup`):** `read_Folder` never checks that `inIndex`
       values are pairwise distinct or that `outIndex` values are pairwise distinct.
       Duplicate or out-of-bounds `outIndex` leaves multiple output ports unbound, making
       `folder_uncompressed_size` pick an arbitrary port.
    3. **Missing acyclicity check:** `read_Folder` does not check for self-loops or cycles
       in `bindPairs`.
    4. **Discarded `packedStreams`:** Lines 2495-2499 parse `packedStream` into a dead
       local variable without checking bounds, uniqueness, or disjointness from `bindPairs`.
    5. **Zero or excess `numPackedStreams` on non-BCJ2 folders:** `read_Folder` line 2460
       only checks `numInStreamsTotal >= numOutStreamsTotal - 1`, permitting
       `numInStreamsTotal = 0, numOutStreamsTotal = 1` (`numPackedStreams = 0`), as well as
       `numPackedStreams >= 2` on 1-coder/2-coder non-BCJ2 folders. In the latter case,
       `setup_decode_folder` sets `pack_stream_remaining >= 2`, leaving `pack_stream_remaining >= 1`
       after Folder 0 finishes and causing `read_stream` (line 3853) to skip `setup_decode_folder`
       for Folder 1!
    6. **Ignored `bindPairs` in 2-coder folders:** `setup_decode_folder` (lines 4048-4052)
       hardcodes `coder1 = &coders[0]` and `coder2 = &coders[1]` without checking which
       coder's output feeds which coder's input in `bindPairs`. -/
def FolderDAGInv (f : FolderDAG) : Prop :=
  1 ≤ f.coders.length ∧ f.coders.length ≤ 4 ∧
  1 ≤ f.totalOutStreams ∧
  f.bindPairs.length + 1 = f.totalOutStreams ∧
  f.totalInStreams = f.bindPairs.length + f.packedStreams.length ∧
  1 ≤ f.packedStreams.length ∧
  f.unPackSizes.length = f.totalOutStreams ∧
  (∀ bp ∈ f.bindPairs, bp.inIndex < f.totalInStreams ∧ bp.outIndex < f.totalOutStreams) ∧
  (f.bindPairs.map BindPair.inIndex).Nodup ∧
  (f.bindPairs.map BindPair.outIndex).Nodup ∧
  (∀ ps ∈ f.packedStreams, ps < f.totalInStreams) ∧
  f.packedStreams.Nodup ∧
  (∀ ps ∈ f.packedStreams, ∀ bp ∈ f.bindPairs, ps ≠ bp.inIndex) ∧
  (∃ rank : Nat → Nat, f.CoderRankAcyclic rank) ∧
  f.Bcj2ArityInv ∧
  ((f.coders.all (fun c => c.codec != .x86Bcj2)) → f.packedStreams.length = 1)

end FolderDAG

/-! ## 3. PackInfo, SubStreams Ledger, BCJ2 Streams, and PPMd7 Sub-Allocator -/

/-- Mirrors `struct _7z_pack_info` (`archive_read_support_format_7zip.c:205-212`). -/
structure PackInfo where
  pos       : Nat
  sizes     : List Nat
  positions : List Nat
  deriving DecidableEq, Repr

/-- Mirrors `struct _7z_substream_info` (`archive_read_support_format_7zip.c:214-219`),
    indexed per folder to expose the per-folder substream conservation law. -/
structure SubStreamsLedger where
  perFolderSizes   : List (List Nat)
  digestsDefined   : List Bool
  digests          : List UInt32
  deriving DecidableEq, Repr

namespace SubStreamsLedger

def flatUnpackSizes (ss : SubStreamsLedger) : List Nat :=
  ss.perFolderSizes.flatten

def totalUnpackStreams (ss : SubStreamsLedger) : Nat :=
  ss.flatUnpackSizes.length

end SubStreamsLedger

/-- Substream sum and CRC propagation invariant (`read_SubStreamsInfo`, lines 2656-2791,
    and `read_StreamsInfo`, lines 2858-2871).

    **C implementation gaps:**
    1. **Omitted `kSubStreamsInfo` not defaulted:** Per the 7-Zip specification, when
       every folder has `1` unpack stream and CRCs are in `kUnPackInfo`, `kSubStreamsInfo`
       may be omitted in `MainStreamsInfo`. `read_StreamsInfo` (line 2858) leaves
       `si->ss.unpack_streams = 0` and `f[i].numUnpackStreams = 0`, causing `read_Header`
       (line 3193) to reject valid archives.
    2. **Dropped folder CRCs when `type != kCRC`:** In `read_SubStreamsInfo` (lines 2752-2783),
       copying `f[i].digest` into `ss->digests` for `f[i].numUnpackStreams == 1 && f[i].digest_defined`
       is nested inside `if (type == kCRC)`. When `kSubStreamsInfo` has no `kCRC` block
       (`type == kEnd`, valid when all CRCs were already declared at folder level in `kUnPackInfo`),
       all folder CRCs are silently dropped (`ss->digestsDefined` remains `0`), skipping CRC32 checks. -/
def SubStreamSumInv (folders : List FolderDAG) (ss : SubStreamsLedger) : Prop :=
  ss.perFolderSizes.length = folders.length ∧
  ss.digestsDefined.length = ss.totalUnpackStreams ∧
  ss.digests.length = ss.totalUnpackStreams ∧
  (∀ i (h : i < folders.length),
    let f := folders[i]
    let subSizes := ss.perFolderSizes.getD i []
    subSizes.length = f.numUnpackStreams ∧
    (f.numUnpackStreams > 0 → subSizes.foldl (· + ·) 0 = f.cFolderUncompressedSize) ∧
    (f.numUnpackStreams = 1 ∧ f.digestDefined →
      let flatOffset := (ss.perFolderSizes.take i).flatten.length
      ss.digestsDefined.getD flatOffset false = true ∧
      ss.digests.getD flatOffset 0 = f.digest))

/-- Mirrors BCJ2 4-stream state in `struct _7zip` (`archive_read_support_format_7zip.c:370-388`).

    **C implementation gaps:**
    1. **Sub-stream extraction loop stops early (`setup_decode_folder`, line 4185):**
       `while (zip->pack_stream_inbytes_remaining > 0)` omits `|| zip->folder_outbytes_remaining > 0`.
       When a `7zr` BCJ2 sub-stream (`CALL` or `JMP`) is encoded with `PPMd` or expands its
       last compressed block across the 64 KB `UBUFF_SIZE` boundary, `pack_stream_inbytes_remaining`
       reaches `0` while `folder_outbytes_remaining > 0`, silently truncating `sub_stream_size[i]`.
    2. **`malloc(0)` portability hazard (line 4176):** `b[i] = malloc((size_t)zip->folder_outbytes_remaining)`
       fails with `ENOMEM` on platforms where `malloc(0)` returns `NULL` whenever an executable has
       `0` `CALL` or `0` `JMP` targets (`sunpack[i] == 0`).
    3. **Partial `odd_bcj` drain without shift (`Bcj2_Decode`, lines 4978-4981):**
       Draining `outSize < odd_bcj_size` bytes decrements `odd_bcj_size` without shifting
       `odd_bcj` left, re-emitting `odd_bcj[0]` on the next call and dropping tail bytes. -/
structure Bcj2Streams where
  mainBytesRemaining : Nat
  subStreamSizes     : Fin 3 → Nat
  subStreamRemaining : Fin 3 → Nat
  subStreamNonNull   : Fin 3 → Bool
  tmpBuffSize        : Nat
  tmpBytesAvail      : Nat
  tmpBytesRemaining  : Nat
  oddBcj             : List UInt8
  bcjState           : Nat
  outPos             : Nat

def Bcj2StreamsInv (b : Bcj2Streams) : Prop :=
  (∀ k : Fin 3, b.subStreamRemaining k ≤ b.subStreamSizes k) ∧
  (∀ k : Fin 3, b.subStreamSizes k > 0 → b.subStreamNonNull k = true) ∧
  b.tmpBytesRemaining ≤ b.tmpBytesAvail ∧
  b.tmpBytesAvail ≤ b.tmpBuffSize ∧
  b.tmpBytesRemaining ≤ b.mainBytesRemaining ∧
  b.oddBcj.length ≤ 4 ∧
  b.bcjState ≤ 2

/-! ## 4. PPMd7 Custom Sub-Allocator (`archive_ppmd7.c`) -/

/-- `UNIT_SIZE = 12` bytes (`archive_ppmd7.c:30`). -/
def PPMD_UNIT_SIZE : Nat := 12

/-- `PPMD_NUM_INDEXES = 38` free-list buckets (`archive_ppmd_private.h:98-102`). -/
def PPMD_NUM_INDEXES : Nat := 38

/-- `PPMD7_MAX_ORDER = 64` (`archive_ppmd7_private.h:19`). -/
def PPMD7_MAX_ORDER : Nat := 64

/-- `PPMD7_MIN_MEM_SIZE = 2048` (`archive_ppmd7_private.h:21`). -/
def PPMD7_MIN_MEM_SIZE : Nat := 2048

/-- `PPMD7_MAX_MEM_SIZE = 0xFFFFFFFF - 36` (`archive_ppmd7_private.h:22`). -/
def PPMD7_MAX_MEM_SIZE : Nat := 0xFFFFFFFF - 12 * 3

/-- Exact mathematical specification of `p->Indx2Units[indx]` (`archive_ppmd7.c:93-98`):
    - `0..3`  -> `1, 2, 3, 4`       (step 1)
    - `4..7`  -> `6, 8, 10, 12`     (step 2)
    - `8..11` -> `15, 18, 21, 24`   (step 3)
    - `12..37`-> `28, 32, ..., 128` (step 4) -/
def ppmdIndx2Units (i : Nat) : Nat :=
  if i < 4 then
    i + 1
  else if i < 8 then
    4 + 2 * (i - 3)
  else if i < 12 then
    12 + 3 * (i - 7)
  else
    24 + 4 * (i - 11)

/-- Exact mathematical specification of `U2I(nu) = p->Units2Indx[nu - 1]` (`archive_ppmd7.c:33, 93-98`)
    for `1 ≤ nu ≤ 128`: smallest bucket index `i < 38` with `ppmdIndx2Units i ≥ nu`. -/
def ppmdUnits2Indx (nu : Nat) : Nat :=
  if nu ≤ 4 then
    nu - 1
  else if nu ≤ 12 then
    4 + (nu - 5) / 2
  else if nu ≤ 24 then
    8 + (nu - 13) / 3
  else
    12 + (nu - 25) / 4

/-- Model of `SplitBlock(p, ptr, oldIndx, newIndx)` (`archive_ppmd7.c:165-175`),
    returning the list of bucket indices inserted back into `FreeList`. -/
def ppmdSplitBlockBuckets (oldIndx newIndx : Nat) : List Nat :=
  let nu := ppmdIndx2Units oldIndx - ppmdIndx2Units newIndx
  let i0 := ppmdUnits2Indx nu
  if ppmdIndx2Units i0 == nu then
    [i0]
  else
    let i := i0 - 1
    let k := ppmdIndx2Units i
    [nu - k - 1, i]

/-- Bytes carved from `[HiUnit - ..., HiUnit)` for unit allocations in `RestartModel`
    (`archive_ppmd7.c:331`): `p->Size / 8 / UNIT_SIZE * 7 * UNIT_SIZE`. -/
def ppmdRestartCarveBytes (size : Nat) : Nat :=
  (size / (8 * PPMD_UNIT_SIZE)) * (7 * PPMD_UNIT_SIZE)

/-- Free block interval `[offset, offset + nu * 12)` in `CPpmd7`'s arena. -/
structure PpmdFreeBlock where
  offset : Nat
  nu     : Nat
  deriving DecidableEq, Repr

/-- Mirrors `CPpmd7` sub-allocator and context-order state (`archive_ppmd7_private.h:44-62`). -/
structure PpmdSubAlloc where
  allocated        : Bool
  size             : Nat
  alignOffset      : Nat
  allocBytes       : Nat
  textOffset       : Nat
  unitsStartOffset : Nat
  loUnitOffset     : Nat
  hiUnitOffset     : Nat
  maxOrder         : Nat
  orderFall        : Nat
  contextDepth     : Nat
  runLength        : Int
  freeBlocks       : List PpmdFreeBlock
  deriving DecidableEq, Repr

/-- Representation invariant for `CPpmd7` (`archive_ppmd7.c`).

    **C implementation gaps:**
    1. **Insufficient minimum-size guard in `Ppmd7_Alloc` (`archive_ppmd7.c:129-133`):**
       `Ppmd7_Alloc` only checks `if (size < UNIT_SIZE) return False;` (`size < 12`),
       claiming `RestartModel` only needs `size >= 12`. In fact, `RestartModel` (lines 338-343)
       immediately allocates `1` unit from `HiUnit` (`12` bytes) and `128` units from `LoUnit`
       (`1536` bytes) = `1548` bytes inside `ppmdRestartCarveBytes(size)`, which requires
       `size >= 1824` (`19 * 96`). For `12 <= size < 1824`, `LoUnit` crosses `HiUnit` and
       overflows `p->Base`! (Mitigated in 7zip reader at line 1670 via `msize >= 2048`.)
    2. **Unchecked `UInt32` wraparound in `Ppmd8_Alloc` (`archive_ppmd8.c:99-115`):**
       `Ppmd8_Alloc` omits even `size < UNIT_SIZE` and computes `p->AlignOffset + size`
       in 32-bit `UInt32`, wrapping to `0` when `size >= 0xFFFFFFFC`.
    3. **Signed 32-bit `Int32 RunLength` overflow (`archive_ppmd7.c:724, 735`):**
       `p->RunLength++` in `Ppmd7_UpdateBin` (and `p->RunLength += p->PrevSuccess` in
       `Ppmd7_Update1_0`) overflows signed `Int32` (`> 2^31 - 1`) on valid streams with
       `> 2.15` billion consecutive predictable symbols without an Order-2 escape. -/
def PpmdHeapInv (p : PpmdSubAlloc) : Prop :=
  p.allocated = true →
    1824 ≤ p.size ∧ p.size ≤ PPMD7_MAX_MEM_SIZE ∧
    1 ≤ p.alignOffset ∧ p.alignOffset ≤ 4 ∧
    p.allocBytes = p.alignOffset + p.size + PPMD_UNIT_SIZE ∧
    p.allocBytes ≤ 0xFFFFFFFF ∧
    p.alignOffset ≤ p.textOffset ∧
    p.textOffset ≤ p.unitsStartOffset ∧
    p.unitsStartOffset ≤ p.loUnitOffset ∧
    p.loUnitOffset ≤ p.hiUnitOffset ∧
    p.hiUnitOffset ≤ p.alignOffset + p.size ∧
    2 ≤ p.maxOrder ∧ p.maxOrder ≤ PPMD7_MAX_ORDER ∧
    p.contextDepth + p.orderFall = p.maxOrder ∧
    -2147483648 ≤ p.runLength ∧ p.runLength ≤ 2147483647 ∧
    (∀ b ∈ p.freeBlocks,
      1 ≤ b.nu ∧
      (p.unitsStartOffset ≤ b.offset ∧ b.offset + b.nu * PPMD_UNIT_SIZE ≤ p.loUnitOffset ∨
       p.hiUnitOffset ≤ b.offset ∧ b.offset + b.nu * PPMD_UNIT_SIZE ≤ p.alignOffset + p.size))

/-! ## 5. Top-Level 7-Zip Reader State (`struct _7zip`) & Safety Invariants -/

inductive SevenZipStage where
  | initial
  | readingRawHeader
  | readingEncodedHeader
  | readingEntries
  | entryFailed
  | fatal
  deriving DecidableEq, Repr

/-- Abstract top-down model of `struct _7zip` (`archive_read_support_format_7zip.c:259-394`). -/
structure SevenZipState where
  stage                            : SevenZipStage
  headerOffset                     : Nat
  seekBase                         : Nat
  headerBytesRemaining             : Nat
  headerIsBeingRead                : Bool
  headerIsEncoded                  : Bool
  packInfo                         : PackInfo
  folders                          : List FolderDAG
  subStreams                       : SubStreamsLedger
  numFiles                         : Nat
  currentEntryFolder               : Option Nat
  entryBytesRemaining              : Nat
  endOfEntry                       : Bool
  folderIndex                      : Nat
  folderOutBytesRemaining          : Nat
  packStreamIndex                  : Nat
  packStreamRemaining              : Nat
  packStreamInBytesRemaining       : Nat
  packStreamBytesUnconsumed        : Nat
  uncompressedBufferSize           : Nat
  uncompressedBufferBytesRemaining : Nat
  codec                            : Option CodecId
  codec2                           : Option CodecId
  lzstreamValid                    : Bool
  bzstreamValid                    : Bool
  zstdStreamValid                  : Bool
  zstdDStreamNonNull               : Bool
  ppmd7Valid                       : Bool
  oddBcj                           : List UInt8
  bcj2                             : Bcj2Streams
  ppmd                             : PpmdSubAlloc

namespace SevenZipState

/-- `PackInfo` & `EncodedHeader` offset bound invariant (`read_StreamsInfo`, lines 2823-2831,
    and `decode_encoded_header_info`, lines 3327-3359). -/
def EncodedHeaderBoundInv (s : SevenZipState) : Prop :=
  ∃ hEq : s.packInfo.sizes.length = s.packInfo.positions.length,
    ∀ i (h : i < s.packInfo.sizes.length),
      s.packInfo.positions[i]'(hEq ▸ h) + s.packInfo.sizes[i] ≤ s.headerOffset

/-- Clean state-reset invariant required upon completing `slurp_central_directory`
    before reading file entries (`archive_read_support_format_7zip.c:3562-3570`).

    **C implementation gap (HIGH):**
    Lines 3563-3568 reset `pack_stream_remaining`, `pack_stream_index`,
    `folder_outbytes_remaining`, `uncompressed_buffer_bytes_remaining`,
    `pack_stream_bytes_unconsumed`, and `header_is_being_read`, **but OMIT
    `zip->pack_stream_inbytes_remaining = 0;`, `zip->odd_bcj_size = 0;`, and
    `zip->tmp_stream_bytes_remaining = 0;`!**
    When an `EncodedHeader` pack stream has trailing padding bytes (or `_7Z_COPY`
    with `sizes[0] > bytes_avail`, or exact 64 KB header buffer), `pack_stream_inbytes_remaining`
    remains `> 0`. On the first `archive_read_data` call for Entry 0, `read_stream`
    (line 3835) sees `zip->pack_stream_inbytes_remaining > 0`, skips `setup_decode_folder`
    for Entry 0, and tries to read Entry 0 from the exhausted `EncodedHeader` stream! -/
def EncodedHeaderCleanResetInv (s : SevenZipState) : Prop :=
  s.headerIsBeingRead = false ∧
  s.packStreamRemaining = 0 ∧
  s.packStreamIndex = 0 ∧
  s.folderOutBytesRemaining = 0 ∧
  s.packStreamInBytesRemaining = 0 ∧
  s.packStreamBytesUnconsumed = 0 ∧
  s.uncompressedBufferBytesRemaining = 0 ∧
  s.oddBcj = [] ∧
  s.bcj2.tmpBytesRemaining = 0

/-- Active codec handle validity, unconsumed-byte discipline, and stream synchronization invariant.

    **C implementation gaps:**
    1. **Unchecked `ZSTD_createDStream()` (`init_decompression`, line 1621):**
       Sets `zip->zstdstream_valid = 1` without checking `zip->zstd_dstream != NULL`,
       causing `NULL` dereference in `ZSTD_decompressStream` (line 1925) on `ENOMEM`.
    2. **Calling `lzma_code` / `BZ2_bzDecompress` after stream end (`decompress`, lines 1834, 1864):**
       `LZMA_STREAM_END` calls `lzma_end` and sets `lzstream_valid = 0`, yet `extract_pack_stream`
       (line 3769) breaks on a full 64 KB `uncompressed_buffer` before checking `end_of_data` (line 3780).
       With `BCJ2 + LZMA2/LZMA/BZ2`, when the final 4-byte `CALL`/`JMP` target straddles the 64 KB
       boundary (`tmp_stream_bytes_remaining = 0`, `odd_bcj_size > 0`), the next `decompress` call
       invokes `lzma_code` with `lzstream_valid == 0` (`LZMA_PROG_ERROR`).
    3. **Unconsumed input replay (`get_uncompressed_data`, line 3611):**
       `read_stream` calls `extract_pack_stream(a, 0)` (leaving `pack_stream_bytes_unconsumed > 0`)
       and immediately calls `get_uncompressed_data(..., minimum)`. When `minimum > UBUFF_SIZE`,
       `get_uncompressed_data` calls `extract_pack_stream(a, minimum)` without `read_consume(a)`,
       re-feeding the same compressed bytes into the decompressor.
    4. **Folder index desynchronization (`read_stream`, lines 3866-3887):**
       `if (zip->folder_index == 0 && ...)` only resynchronizes `zip->folder_index` to
       `zip->entry->folderIndex` when `folder_index == 0`. If Folder `k` (`k >= 1`) has
       `numUnpackStreams == 0` (allowed by `read_SubStreamsInfo` line 2718 and skipped by
       `read_Header` line 3243) or failed with `ARCHIVE_FAILED` (recoverable per `archive_read.c`),
       subsequent entries in Folder `k + 1` decode the wrong folder `k`! -/
def StreamDecompInv (s : SevenZipState) : Prop :=
  (s.zstdStreamValid = true → s.zstdDStreamNonNull = true) ∧
  (s.codec = some .lzma ∨ s.codec = some .lzma2 →
    s.folderOutBytesRemaining > 0 → s.bcj2.oddBcj = [] → s.bcj2.tmpBytesRemaining = 0 →
    s.lzstreamValid = true) ∧
  (s.codec = some .bz2 →
    s.folderOutBytesRemaining > 0 → s.bcj2.oddBcj = [] → s.bcj2.tmpBytesRemaining = 0 →
    s.bzstreamValid = true) ∧
  s.uncompressedBufferBytesRemaining ≤ s.uncompressedBufferSize ∧
  s.oddBcj.length ≤ 16 ∧
  (s.stage = .readingEntries →
    s.uncompressedBufferBytesRemaining = 0 →
    s.packStreamInBytesRemaining = 0 →
    s.folderOutBytesRemaining = 0 →
    s.packStreamRemaining = 0 →
    ∀ targetFolder, s.currentEntryFolder = some targetFolder →
      targetFolder < s.folders.length ∧ s.folderIndex = targetFolder)

/-- Complete top-down safety invariant for `SevenZipState`. -/
def SafetyInv (s : SevenZipState) : Prop :=
  s.EncodedHeaderBoundInv ∧
  (∀ f ∈ s.folders, f.FolderDAGInv) ∧
  SubStreamSumInv s.folders s.subStreams ∧
  Bcj2StreamsInv s.bcj2 ∧
  PpmdHeapInv s.ppmd ∧
  s.StreamDecompInv

end SevenZipState

/-! ## 6. State-Transition Models & Verified Safety / Bug-Witness Theorems -/

/-- Whether `read_stream` (`archive_read_support_format_7zip.c:3834-3887`) enters the
    new-folder initialization path (`setup_decode_folder`). -/
def readStreamEntersNewFolder (s : SevenZipState) : Bool :=
  s.uncompressedBufferBytesRemaining == 0 &&
  s.packStreamInBytesRemaining == 0 &&
  s.folderOutBytesRemaining == 0 &&
  s.packStreamRemaining == 0 &&
  !s.headerIsBeingRead

/-- Models the exact C cleanup at the end of `slurp_central_directory`
    (`archive_read_support_format_7zip.c:3562-3568`), which omits resetting
    `packStreamInBytesRemaining`, `oddBcj`, and `bcj2.tmpBytesRemaining`. -/
def cBuggyResetAfterEncodedHeader (s : SevenZipState) : SevenZipState :=
  { s with
    stage := .readingEntries
    packStreamRemaining := 0
    packStreamIndex := 0
    folderOutBytesRemaining := 0
    uncompressedBufferBytesRemaining := 0
    packStreamBytesUnconsumed := 0
    headerIsBeingRead := false }

/-- Defensive C fix for `slurp_central_directory` cleanup: resets all stream-decoding
    residuals (`packStreamInBytesRemaining`, `oddBcj`, `bcj2.tmpBytesRemaining`). -/
def safeResetAfterEncodedHeader (s : SevenZipState) : SevenZipState :=
  { s with
    stage := .readingEntries
    packStreamRemaining := 0
    packStreamIndex := 0
    folderOutBytesRemaining := 0
    packStreamInBytesRemaining := 0
    uncompressedBufferBytesRemaining := 0
    packStreamBytesUnconsumed := 0
    headerIsBeingRead := false
    oddBcj := []
    bcj2 := { s.bcj2 with tmpBytesRemaining := 0, oddBcj := [] } }

/-- Theorem 1: `safeResetAfterEncodedHeader` establishes `EncodedHeaderCleanResetInv`
    and guarantees that Entry 0's first `read_stream` call initializes Entry 0's folder. -/
theorem safeReset_establishes_cleanInv (s : SevenZipState) :
    (safeResetAfterEncodedHeader s).EncodedHeaderCleanResetInv ∧
    readStreamEntersNewFolder (safeResetAfterEncodedHeader s) = true := by
  refine ⟨?_, ?_⟩
  · unfold SevenZipState.EncodedHeaderCleanResetInv safeResetAfterEncodedHeader
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold readStreamEntersNewFolder safeResetAfterEncodedHeader
    rfl

/-- Theorem 2 (Bug Witness): Whenever `EncodedHeader` finishes with leftover
    `packStreamInBytesRemaining > 0`, C's `cBuggyResetAfterEncodedHeader` violates
    `EncodedHeaderCleanResetInv` AND prevents `read_stream` from setting up Entry 0's folder! -/
theorem cBuggyReset_skips_entry0_folder (s : SevenZipState)
    (hLeftover : s.packStreamInBytesRemaining > 0) :
    ¬ (cBuggyResetAfterEncodedHeader s).EncodedHeaderCleanResetInv ∧
    readStreamEntersNewFolder (cBuggyResetAfterEncodedHeader s) = false := by
  refine ⟨?_, ?_⟩
  · intro hInv
    dsimp only [SevenZipState.EncodedHeaderCleanResetInv, cBuggyResetAfterEncodedHeader] at hInv
    rcases hInv with ⟨_, _, _, _, hInZero, _⟩
    omega
  · unfold readStreamEntersNewFolder cBuggyResetAfterEncodedHeader
    have hNe : (s.packStreamInBytesRemaining == 0) = false :=
      beq_false_of_ne (by omega)
    simp [hNe]

/-- Models C's buggy `odd_bcj` drain loop (`Bcj2_Decode` lines 4978-4981 and
    `decompress` lines 1756-1761): copies `min outSize q.length` bytes from `q[0..]`
    and shrinks the length without shifting the array elements left! -/
def cBuggyOddBcjDrain (q : List UInt8) (outSize : Nat) : List UInt8 × List UInt8 :=
  let emitted := q.take outSize
  let remainingLen := q.length - emitted.length
  (emitted, q.take remainingLen)

/-- Correct FIFO `odd_bcj` drain (with `memmove` shift): returns `(q.take outSize, q.drop outSize)`. -/
def safeOddBcjDrain (q : List UInt8) (outSize : Nat) : List UInt8 × List UInt8 :=
  (q.take outSize, q.drop outSize)

/-- Theorem 3: `safeOddBcjDrain` preserves the exact stream concatenation across two
    calls (`emitted1 ++ emitted2 ++ rem2 = q`), whereas `cBuggyOddBcjDrain` corrupts
    the output stream on any partial drain `0 < outSize < q.length` with distinct bytes! -/
theorem safeOddBcjDrain_fifo_exact (q : List UInt8) (n1 n2 : Nat) :
    let (e1, q1) := safeOddBcjDrain q n1
    let (e2, q2) := safeOddBcjDrain q1 n2
    e1 ++ e2 ++ q2 = q := by
  simp only [safeOddBcjDrain, List.append_assoc, List.take_append_drop]

theorem cBuggyOddBcjDrain_corrupts_partial :
    let q : List UInt8 := [0x11, 0x22, 0x33]
    let (e1, q1) := cBuggyOddBcjDrain q 1
    let (e2, _)  := cBuggyOddBcjDrain q1 2
    e1 ++ e2 ≠ q := by
  decide

/-- Models BCJ instruction-pointer (`bcj_ip`) vs emitted-byte synchronization in
    `decompress` (`archive_read_support_format_7zip.c:2073-2082`).
    `convertedLen` (`l`) is how many bytes `*_Convert` processed (and added to `bcj_ip`).
    C checks `oAvailIn > 0` instead of `folderOutBytesRemaining > rawOutBytes`. -/
def cBuggyBcjStep (bcjIp totalEmitted oAvailIn rawOutBytes convertedLen : Nat) : Nat × Nat :=
  let newIp := bcjIp + convertedLen
  let oddLen := rawOutBytes - convertedLen
  if oddLen > 0 && oddLen ≤ 16 && oAvailIn > 0 then
    (newIp, totalEmitted + convertedLen)
  else
    (newIp, totalEmitted + rawOutBytes)

def safeBcjStep (bcjIp totalEmitted folderOutRemaining rawOutBytes convertedLen : Nat) : Nat × Nat :=
  let newIp := bcjIp + convertedLen
  let oddLen := rawOutBytes - convertedLen
  if oddLen > 0 && oddLen ≤ 16 && folderOutRemaining > rawOutBytes then
    (newIp, totalEmitted + convertedLen)
  else
    (newIp, totalEmitted + rawOutBytes)

/-- Theorem 4 (`bcj_ip` Synchronization vs Desynchronization):
    During a multi-chunk flush (`oAvailIn = 0` while `folderOutRemaining > rawOutBytes`),
    if an instruction straddles the chunk boundary (`0 < rawOutBytes - convertedLen ≤ 16`),
    `safeBcjStep` preserves `newIp = newEmitted` (assuming `bcjIp = totalEmitted`), whereas
    `cBuggyBcjStep` desynchronizes `newIp < newEmitted` for the remainder of the folder! -/
theorem bcj_ip_sync_vs_c_desync
    (ip rawOut converted folderRem : Nat)
    (hConvLt : converted < rawOut)
    (hLookahead : rawOut - converted ≤ 16)
    (hMoreFolder : rawOut < folderRem) :
    let (safeIp, safeEmit) := safeBcjStep ip ip folderRem rawOut converted
    let (bugIp, bugEmit)   := cBuggyBcjStep ip ip 0 rawOut converted
    safeIp = safeEmit ∧ bugIp < bugEmit := by
  have h1 : rawOut - converted > 0 := by omega
  simp [safeBcjStep, cBuggyBcjStep, h1, hLookahead, hMoreFolder]
  omega

/-- Models C's folder-switching logic in `read_stream` (`archive_read_support_format_7zip.c:3866-3887`),
    returning which folder index is passed to `setup_decode_folder`. -/
def cBuggySelectFolder (folderIndex entryFolderIndex : Nat) (skippedBytes : Nat) : Nat :=
  if folderIndex == 0 && (skippedBytes > 0 || folderIndex != entryFolderIndex) then
    entryFolderIndex
  else
    folderIndex

def safeSelectFolder (_folderIndex entryFolderIndex : Nat) : Nat :=
  entryFolderIndex

/-- Theorem 5 (`FolderSyncInv` Violation Witness): Whenever `folderIndex ≥ 1`
    (e.g., after reading Folder 0, when Folder 1 has `numUnpackStreams = 0` or failed
    with `ARCHIVE_FAILED`, and the next entry resides in Folder `entryFolderIndex > folderIndex`),
    `cBuggySelectFolder` decodes the wrong folder (`folderIndex ≠ entryFolderIndex`)! -/
theorem cBuggySelectFolder_wrong_when_nonzero
    (folderIndex entryFolderIndex skippedBytes : Nat)
    (hPos : 1 ≤ folderIndex)
    (hAhead : folderIndex < entryFolderIndex) :
    cBuggySelectFolder folderIndex entryFolderIndex skippedBytes ≠ entryFolderIndex ∧
    safeSelectFolder folderIndex entryFolderIndex = entryFolderIndex := by
  have hNeZero : (folderIndex == 0) = false := beq_false_of_ne (by omega)
  simp [cBuggySelectFolder, safeSelectFolder, hNeZero]
  omega

/-! ## 7. FolderDAG Structural Lemmas -/

/-- Helper lemma for `findCoderForPort`: if `findCoderForPort arities base port = some idx`,
    then `base ≤ idx` and `idx < base + arities.length`. -/
theorem findCoderForPort_bounds :
    ∀ (arities : List Nat) (base port idx : Nat),
      FolderDAG.findCoderForPort arities base port = some idx →
      base ≤ idx ∧ idx < base + arities.length
  | [], _, _, _, h => by simp [FolderDAG.findCoderForPort] at h
  | a :: rest, base, port, idx, h => by
    simp only [FolderDAG.findCoderForPort] at h
    split at h
    · injection h with hEq
      subst hEq
      simp only [List.length_cons]
      omega
    · have ih := findCoderForPort_bounds rest (base + 1) (port - a) idx h
      simp only [List.length_cons]
      omega

/-- Theorem 6 (No Self-Loop in `FolderDAG`): Under `CoderRankAcyclic`, no `BindPair`
    can connect an output port of coder `c` back to an input port of the same coder `c`. -/
theorem folderDAG_no_self_loop (f : FolderDAG) (rank : Nat → Nat)
    (hAcyclic : f.CoderRankAcyclic rank)
    (bp : BindPair) (hBp : bp ∈ f.bindPairs)
    (c : Nat)
    (hOut : f.outPortOwner bp.outIndex = some c) :
    f.inPortOwner bp.inIndex ≠ some c := by
  intro hIn
  have hLt := hAcyclic bp hBp c c hOut hIn
  omega

/-- Theorem 7 (Port Conservation): Every well-formed `FolderDAG` has at least one input
    stream and strictly fewer `bindPairs` than output streams (guaranteeing at least one
    unbound output port for `folder_uncompressed_size`). -/
theorem folderDAG_port_conservation (f : FolderDAG) (hInv : f.FolderDAGInv) :
    f.bindPairs.length < f.totalOutStreams ∧ 1 ≤ f.totalInStreams := by
  rcases hInv with ⟨_, _, _, hOutEq, hInEq, hPackPos, _⟩
  omega

/-! ## 8. Substream Sum Conservation Lemma -/

/-- Helper: accumulator monotonicity for `List.foldl (· + ·)`. -/
theorem foldl_add_mono : ∀ (zs : List Nat) (a : Nat), a ≤ zs.foldl (· + ·) a
  | [], a => by simp
  | z :: zs, a => by
    simp only [List.foldl_cons]
    have ih := foldl_add_mono zs (a + z)
    omega

/-- Helper: every element of a `Nat` list is bounded above by `foldl (· + ·) acc`. -/
theorem mem_le_foldl_add : ∀ (xs : List Nat) (acc x : Nat),
    x ∈ xs → x ≤ xs.foldl (· + ·) acc
  | [], _, _, h => by cases h
  | y :: ys, acc, x, h => by
    simp only [List.mem_cons] at h
    simp only [List.foldl_cons]
    rcases h with rfl | hMem
    · have hMono := foldl_add_mono ys (acc + x)
      omega
    · exact mem_le_foldl_add ys (acc + y) x hMem

/-- Theorem 8: Under `SubStreamSumInv`, every file substream size in folder `i` is
    bounded above by `f.cFolderUncompressedSize`. -/
theorem substream_size_le_folder_size (folders : List FolderDAG) (ss : SubStreamsLedger)
    (hInv : SubStreamSumInv folders ss)
    (i : Nat) (hi : i < folders.length)
    (sz : Nat) (hSz : sz ∈ ss.perFolderSizes.getD i []) :
    sz ≤ folders[i].cFolderUncompressedSize := by
  rcases hInv with ⟨_, _, _, hPerFolder⟩
  have hF := hPerFolder i hi
  rcases hF with ⟨hLen, hSum, _⟩
  have hPos : folders[i].numUnpackStreams > 0 := by
    cases hList : ss.perFolderSizes.getD i [] with
    | nil =>
      rw [hList] at hSz
      cases hSz
    | cons hd tl =>
      rw [hList, List.length_cons] at hLen
      omega
  have hEq := hSum hPos
  rw [← hEq]
  exact mem_le_foldl_add (ss.perFolderSizes.getD i []) 0 sz hSz

/-! ## 9. PPMd7 Sub-Allocator & Context-Order Safety Theorems -/

/-- Theorem 9 (`RestartModel` Heap Safety): For every `size ≥ 1824` (and in particular
    every `size ≥ PPMD7_MIN_MEM_SIZE = 2048`), `ppmdRestartCarveBytes size ≥ 1548`
    (`(128 + 1) * 12` bytes), proving that `LoUnit + 128 * 12 ≤ HiUnit - 12` holds
    without buffer overflow in `RestartModel`. -/
theorem ppmd_restart_safe_of_ge_1824 (size : Nat) (hSize : 1824 ≤ size) :
    129 * PPMD_UNIT_SIZE ≤ ppmdRestartCarveBytes size := by
  simp only [PPMD_UNIT_SIZE, ppmdRestartCarveBytes]
  omega

/-- Theorem 10 (`Ppmd7_Alloc` Precondition Gap Witness): `Ppmd7_Alloc` (`archive_ppmd7.c:131`)
    accepts `size = 12` (`size >= UNIT_SIZE`), for which `ppmdRestartCarveBytes 12 = 0 < 1548`,
    causing `RestartModel` to advance `LoUnit` (`+ 1536`) past `HiUnit` (`- 12`). -/
theorem ppmd_alloc_guard_insufficient :
    12 ≥ PPMD_UNIT_SIZE ∧ ppmdRestartCarveBytes 12 < 129 * PPMD_UNIT_SIZE := by
  unfold PPMD_UNIT_SIZE ppmdRestartCarveBytes
  decide

/-- Executable exhaustive checker for all `(oldIndx, newIndx)` with `newIndx < oldIndx < 38`. -/
def checkSplitBlockPair (oldIndx newIndx : Nat) : Bool :=
  let rem := ppmdIndx2Units oldIndx - ppmdIndx2Units newIndx
  let buckets := ppmdSplitBlockBuckets oldIndx newIndx
  buckets.all (fun b => b < PPMD_NUM_INDEXES) &&
  buckets.foldl (fun acc b => acc + ppmdIndx2Units b) 0 == rem

def checkAllSplitBlocks : Bool :=
  (List.range PPMD_NUM_INDEXES).all fun oldIndx =>
    (List.range oldIndx).all fun newIndx =>
      checkSplitBlockPair oldIndx newIndx

theorem ppmd_splitBlock_all_checked :
    checkAllSplitBlocks = true := by
  decide

/-- Theorem 11 (`SplitBlock` Exact Unit Conservation & Bucket Validity, Universally Quantified):
    For EVERY pair of bucket indices `newIndx < oldIndx < PPMD_NUM_INDEXES` (`38`),
    `ppmdSplitBlockBuckets oldIndx newIndx` produces only valid bucket indices `< 38`,
    and the sum of their unit sizes equals `ppmdIndx2Units oldIndx - ppmdIndx2Units newIndx`. -/
theorem ppmd_splitBlock_valid_and_conserves_units
    (oldIndx newIndx : Nat)
    (hLt : newIndx < oldIndx)
    (hBound : oldIndx < PPMD_NUM_INDEXES) :
    (∀ b ∈ ppmdSplitBlockBuckets oldIndx newIndx, b < PPMD_NUM_INDEXES) ∧
    (ppmdSplitBlockBuckets oldIndx newIndx).foldl (fun acc b => acc + ppmdIndx2Units b) 0 =
      ppmdIndx2Units oldIndx - ppmdIndx2Units newIndx := by
  have hAll := ppmd_splitBlock_all_checked
  unfold checkAllSplitBlocks at hAll
  rw [List.all_eq_true] at hAll
  have hOldMem : oldIndx ∈ List.range PPMD_NUM_INDEXES := List.mem_range.mpr hBound
  have hInner := hAll oldIndx hOldMem
  rw [List.all_eq_true] at hInner
  have hNewMem : newIndx ∈ List.range oldIndx := List.mem_range.mpr hLt
  have hPair := hInner newIndx hNewMem
  unfold checkSplitBlockPair at hPair
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hPair
  rcases hPair with ⟨hBuckets, hSum⟩
  refine ⟨?_, hSum⟩
  intro b hb
  exact of_decide_eq_true (hBuckets b hb)

/-- Theorem 12 (`CreateSuccessors` Stack-Array Safety in `Ppmd7`):
    In `archive_ppmd7.c:385`, `CPpmd_State *ps[PPMD7_MAX_ORDER]` has capacity `64`
    (without `+ 1`). Under the exact invariant `contextDepth + orderFall = maxOrder`
    and `maxOrder ≤ PPMD7_MAX_ORDER`:
    - When `skip = true` (called at line 497 only when `orderFall = 0`), at most
      `contextDepth ≤ 64` pointers are pushed onto `ps`.
    - When `skip = false` (called at line 519 only when `orderFall ≥ 1`), `1` initial
      pointer plus at most `contextDepth = maxOrder - orderFall ≤ 63` suffix pointers
      are pushed, so `1 + contextDepth ≤ 64 = PPMD7_MAX_ORDER`! -/
theorem ppmd_createSuccessors_ps_in_bounds
    (maxOrder contextDepth orderFall : Nat)
    (hMax : maxOrder ≤ PPMD7_MAX_ORDER)
    (hInv : contextDepth + orderFall = maxOrder)
    (skip : Bool)
    (hCallPre : skip = false → 1 ≤ orderFall) :
    (if skip then 0 else 1) + contextDepth ≤ PPMD7_MAX_ORDER := by
  unfold PPMD7_MAX_ORDER at *
  cases skip with
  | true =>
    simp only [↓reduceIte, Nat.zero_add]
    omega
  | false =>
    have hOf := hCallPre rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

end LibarchiveF.Model.SevenZipTopDown
