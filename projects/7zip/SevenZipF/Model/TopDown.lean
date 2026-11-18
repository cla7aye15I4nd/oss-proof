/-
  SevenZipF/Model/TopDown.lean

  Top-down formal state and safety invariant model for the official 7-Zip pure-C SDK
  (`C/7zArcIn.c`, `C/7zDec.c`, `C/7z.h`, `C/Bcj2.c`, `C/Bcj2.h`, `C/Ppmd7.c`,
  `C/Ppmd7Dec.c`, `C/Ppmd7.h`, `C/Ppmd.h`, `C/LzmaDec.c`, `C/Lzma2Dec.c`) targeting
  the portable scalar x86_64 Linux LP64 build.

  Every theorem in this module is kernel-checked with zero `sorry` and uses only
  standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace SevenZipF.Model

/-!
## 1. C11 Pointer, Alignment, and Memory Safety Primitives (`Runtime`)

Models C11 pointer provenance, object bounds, alignment, and initialization state
so that subtle C11 undefined behaviors in the SDK can be stated and distinguished
from well-defined transitions:
- C11 §6.5.6p8: pointer addition `p + n` on `NULL` (even `NULL + 0`) is UB.
- C11 §6.5.6p9: pointer subtraction `p - q` on `NULL` or distinct objects is UB.
- C11 §6.3.2.3p7 & §6.5.3.2p4: misaligned typed pointer cast/dereference is UB.
- C11 §6.3.2.1p2 & §6.2.6.1p5: reading uninitialized `malloc` heap bytes is UB.
- C11 §7.24.1p2 & §7.1.4: `memcpy`/`memset` with a `NULL` pointer is UB even for `n = 0`.
-/
namespace Runtime

abbrev BlockId := Nat

/-- Metadata for a single live heap or stack allocation object. -/
structure HeapBlock where
  /-- Allocation size in bytes (`size_t`). -/
  size : Nat
  /-- Guaranteed base alignment in bytes (a positive power of two, e.g., 8 or 16 for `malloc`). -/
  baseAlign : Nat
  /-- Per-byte initialization predicate (`true` iff written since allocation). -/
  init : Nat → Bool

/-- A C pointer is either `NULL` (`block = none`) or an offset into a provenance block. -/
structure CPtr where
  block : Option BlockId
  offset : Nat
  deriving DecidableEq, Repr

def CPtr.null : CPtr := { block := none, offset := 0 }

def CPtr.add (p : CPtr) (delta : Nat) : CPtr :=
  { p with offset := p.offset + delta }

/-- Abstract heap mapping `BlockId` to live `HeapBlock`s. -/
abbrev Heap := BlockId → Option HeapBlock

/-- C11 §6.5.6p8 valid pointer formation `p + delta`:
    `p` must be non-null, belong to a live block `b`, and satisfy `p.offset + delta ≤ b.size`
    (allowing one-past-the-end formation, while rejecting `NULL + 0`). -/
def ValidPtrAdd (h : Heap) (p : CPtr) (delta : Nat) : Prop :=
  ∃ bid blk, p.block = some bid ∧ h bid = some blk ∧ p.offset + delta ≤ blk.size

/-- C11 §6.5.6p9 valid pointer difference `p - q`:
    both pointers must be non-null and point into (or one past) the same live object. -/
def ValidPtrSub (h : Heap) (p q : CPtr) : Prop :=
  ∃ bid blk,
    p.block = some bid ∧ q.block = some bid ∧
    h bid = some blk ∧ p.offset ≤ blk.size ∧ q.offset ≤ blk.size

/-- C11 §6.3.2.3p7 / §6.5.3.2p4 / §6.3.2.1p2 valid aligned typed read of `width` bytes:
    non-null, strictly within `blk.size`, aligned to `align`, and all `width` bytes initialized. -/
def ValidTypedRead (h : Heap) (p : CPtr) (width align : Nat) : Prop :=
  ∃ bid blk,
    p.block = some bid ∧
    h bid = some blk ∧
    0 < align ∧
    blk.baseAlign % align = 0 ∧
    p.offset % align = 0 ∧
    p.offset + width ≤ blk.size ∧
    ∀ k, k < width → blk.init (p.offset + k) = true

/-- C11 §7.24.1p2 valid `memcpy(dest, src, n)` pointer precondition:
    even when `n = 0`, both `dest` and `src` must be valid non-null pointers in live objects,
    and when `n > 0` the ranges must be in-bounds. -/
def ValidMemcpyPtrs (h : Heap) (dest src : CPtr) (n : Nat) : Prop :=
  ValidPtrAdd h dest n ∧ ValidPtrAdd h src n

/-- C11 §6.5.6p8: `NULL + 0` is NOT valid pointer arithmetic.
    Directly captures the C11 UB in `7zDec.c:520-525` (`tempBuf[i] + 0` when `SzAlloc(0) = NULL`),
    `7zArcIn.c:1672` (`*tempBuf + *offset` on 0-byte folders), `7zDec.c:658` (`PackPositions + 0`),
    and `7zCrcOpt.c:55` / `Bra.c:83` (`p + 0`). -/
theorem null_add_zero_not_valid (h : Heap) : ¬ ValidPtrAdd h CPtr.null 0 := by
  intro ⟨_, _, hblk, _, _⟩
  cases hblk

/-- C11 §6.5.6p9: `NULL - NULL` is NOT valid pointer subtraction (`Bcj2.c:114`). -/
theorem null_sub_null_not_valid (h : Heap) : ¬ ValidPtrSub h CPtr.null CPtr.null := by
  intro ⟨_, _, hblk, _, _⟩
  cases hblk

/-- C11 §7.24.1p2: `memcpy(NULL, src, 0)` is NOT valid (`LzmaDec.c:1233`, `Lzma2Dec.c:459`). -/
theorem memcpy_null_dest_zero_not_valid (h : Heap) (src : CPtr) :
    ¬ ValidMemcpyPtrs h CPtr.null src 0 := by
  intro ⟨hdest, _⟩
  exact null_add_zero_not_valid h hdest

/-- Composing two valid pointer additions within the same block remains valid. -/
theorem validPtrAdd_trans (h : Heap) (p : CPtr) (d1 d2 : Nat)
    (h1 : ValidPtrAdd h p d1)
    (h2 : ValidPtrAdd h (p.add d1) d2) :
    ValidPtrAdd h p (d1 + d2) := by
  rcases h1 with ⟨bid1, blk1, hp1, hblk1, hle1⟩
  rcases h2 with ⟨bid2, blk2, hp2, hblk2, hle2⟩
  simp [CPtr.add] at hp2 hle2
  rw [hp1] at hp2
  injection hp2 with hbid
  subst hbid
  rw [hblk1] at hblk2
  injection hblk2 with hblkEq
  subst hblkEq
  refine ⟨bid1, blk1, hp1, hblk1, ?_⟩
  omega

/-- Misaligned `UInt32` dereference (`align = 4`) at an unaligned byte offset (`offset % 4 ≠ 0`)
    violates `ValidTypedRead`, modeling `CpuArch.h:488,495,542` (`SetUi32(dest, v)` in `Bcj2.c:270`
    after a 1-byte `0xe8`/`0xe9` opcode at offset 0). -/
theorem misaligned_u32_read_not_valid (h : Heap) (p : CPtr) (hmis : p.offset % 4 ≠ 0) :
    ¬ ValidTypedRead h p 4 4 := by
  intro ⟨_, _, _, _, _, _, hal, _, _⟩
  exact hmis hal

end Runtime

/-!
## 2. `.7z` Archive, `CSzFolder` / `BindPairs` DAG, `SubStreams`, and `SzArEx_Extract` Cache
   (`C/7z.h`, `C/7zArcIn.c`, `C/7zDec.c`)

Key subtle invariants and findings modeled here:
1. **Coder Graph Acyclicity Gap (`7zArcIn.c:525-566`, `700-750`):**
   `SzGetNextFolderItem` and `ReadUnpackInfo` enforce `numBonds + 1 = numCoders`, distinct
   `InIndex < numInStreams`, and distinct `OutIndex < numCoders`, leaving one sink `UnpackStream`.
   We prove (`szGetNextFolderItem_allows_cycle`) that this degree check admits disconnected cyclic
   graphs (e.g. a self-loop on Coder 0 with Coder 1 isolated), whereas `CheckSupportedFolder`
   (`7zDec.c:329-404`) restricts to 3 canonical topologies that are all genuine DAGs
   (`checkSupportedFolder_implies_DAG`).
2. **`SzArEx_Extract` Solid-Block Cache Poisoning on Error (`7zArcIn.c:1630-1662`):**
   `SzArEx_Extract` sets `*blockIndex = folderIndex` and allocates `*tempBuf` *before* calling
   `SzAr_DecodeFolder`, and does NOT clear `*tempBuf` or reset `*blockIndex` when decoding fails.
   We prove (`buggy_extract_breaks_cache_coherence`) that a subsequent `SzArEx_Extract` call on
   another file in the same solid folder skips `SzAr_DecodeFolder` and returns uninitialized/corrupt
   memory as `SZ_OK` if that file lacks a per-file CRC, and we prove that our fixed transition
   preserves `CacheCoherentInv` (`fixed_extract_preserves_cache_coherence`).
3. **`SubStreams` 0-Substream Folder Offset Shift (`7zArcIn.c:1314` vs `1351`):**
   We prove `unpackPos_folder_end_monotone` and `zero_substream_folder_shifts_first_file_size`
   when a folder with `numSubStreams = 0` has non-zero `folderUnpackSize`.
-/
namespace Archive

def SZ_NUM_CODERS_IN_FOLDER_MAX : Nat := 4
def SZ_NUM_BONDS_IN_FOLDER_MAX : Nat := 3
def SZ_NUM_PACK_STREAMS_IN_FOLDER_MAX : Nat := 4

structure CoderInfo where
  propsOffset : Nat
  methodID : UInt32
  numStreams : Nat
  propsSize : Nat
  deriving DecidableEq, Repr

structure SzBond where
  inIndex : Nat
  outIndex : Nat
  deriving DecidableEq, Repr

structure SzFolder where
  coders : List CoderInfo
  bonds : List SzBond
  packStreams : List Nat
  unpackStream : Nat
  deriving DecidableEq, Repr

/-- Total number of input ports across all coders in `f`. -/
def totalInStreams (coders : List CoderInfo) : Nat :=
  coders.foldl (fun acc c => acc + c.numStreams) 0

/-- Maps a global input stream port index `inIdx` to the coder index `ci` that owns it. -/
def ownerCoderAux : List CoderInfo → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, ci, rem =>
    if rem < c.numStreams then some ci
    else ownerCoderAux cs (ci + 1) (rem - c.numStreams)

def ownerCoder (f : SzFolder) (inIdx : Nat) : Option Nat :=
  ownerCoderAux f.coders 0 inIdx

/-- Exact structural checks enforced by `SzGetNextFolderItem` (`7zArcIn.c:424-579`):
    - `1 ≤ numCoders ≤ 4`
    - `numBonds + 1 = numCoders`
    - `numPackStreams + numBonds = totalInStreams` and `numPackStreams ≤ 4`
    - All `bond.inIndex` and `packStreams` are pairwise-disjoint and `< totalInStreams`
    - All `bond.outIndex` are pairwise-distinct and `< numCoders`
    - `unpackStream < numCoders` is not used by any `bond.outIndex`. -/
def SzGetNextFolderItemValid (f : SzFolder) : Prop :=
  let numCoders := f.coders.length
  let numIn := totalInStreams f.coders
  1 ≤ numCoders ∧ numCoders ≤ SZ_NUM_CODERS_IN_FOLDER_MAX ∧
  f.bonds.length + 1 = numCoders ∧
  f.bonds.length ≤ SZ_NUM_BONDS_IN_FOLDER_MAX ∧
  f.bonds.length ≤ numIn ∧
  f.packStreams.length = numIn - f.bonds.length ∧
  f.packStreams.length ≤ SZ_NUM_PACK_STREAMS_IN_FOLDER_MAX ∧
  (∀ b ∈ f.bonds, b.inIndex < numIn ∧ b.outIndex < numCoders) ∧
  (∀ p ∈ f.packStreams, p < numIn) ∧
  (f.bonds.map (·.inIndex) ++ f.packStreams).Nodup ∧
  (f.bonds.map (·.outIndex)).Nodup ∧
  f.unpackStream < numCoders ∧
  f.unpackStream ∉ f.bonds.map (·.outIndex)

/-- Finds the unique consumer coder that `outCoder`'s output feeds via `f.bonds`, if any. -/
def nextConsumerCoder (f : SzFolder) (outCoder : Nat) : Option Nat :=
  match f.bonds.find? (fun b => b.outIndex == outCoder) with
  | none => none
  | some b => ownerCoder f b.inIndex

/-- Follows `nextConsumerCoder` up to `fuel` steps to test whether `ci` reaches `f.unpackStream`
    without cycling. In a graph on `N` coders, `ci` is cycle-free and connected to the root output
    iff it reaches `f.unpackStream` in at most `N - 1` bond steps. -/
def reachesUnpackIn : SzFolder → Nat → Nat → Bool
  | f, 0, ci => ci == f.unpackStream
  | f, fuel + 1, ci =>
    if ci == f.unpackStream then true
    else match nextConsumerCoder f ci with
      | none => false
      | some nextCi => reachesUnpackIn f fuel nextCi

/-- True coder-tree / DAG invariant: every coder `ci < numCoders` has at least 1 input stream
    and reaches `f.unpackStream` along `f.bonds` in `< numCoders` steps (ruling out cycles and
    disconnected components). -/
def FolderDAGInv (f : SzFolder) : Prop :=
  (∀ c ∈ f.coders, 1 ≤ c.numStreams) ∧
  ∀ ci, ci < f.coders.length → reachesUnpackIn f (f.coders.length - 1) ci = true

/-- Counterexample folder accepted by `SzGetNextFolderItem` (`7zArcIn.c:424-579`) and
    `ReadUnpackInfo` (`7zArcIn.c:700-750`):
    - Coder 0 (`numStreams = 1`, port 0): `Bonds[0]` connects `outIndex = 0 → inIndex = 0` (self-loop!)
    - Coder 1 (`numStreams = 1`, port 1): `PackStreams[0] = 1`, `UnpackStream = 1`. -/
def cyclicFolderCounterexample : SzFolder :=
  { coders := [
      { propsOffset := 0, methodID := 0x21, numStreams := 1, propsSize := 1 },
      { propsOffset := 1, methodID := 0x21, numStreams := 1, propsSize := 1 }
    ]
    bonds := [{ inIndex := 0, outIndex := 0 }]
    packStreams := [1]
    unpackStream := 1 }

/-- Theorem (Validation Gap in `SzGetNextFolderItem` / `ReadUnpackInfo`):
    `cyclicFolderCounterexample` passes every check in `SzGetNextFolderItemValid`, yet violates
    `FolderDAGInv` because Coder 0 forms a closed cycle disconnected from `UnpackStream = 1`. -/
theorem szGetNextFolderItem_allows_cycle :
    SzGetNextFolderItemValid cyclicFolderCounterexample ∧
    ¬ FolderDAGInv cyclicFolderCounterexample := by
  constructor
  · simp [SzGetNextFolderItemValid, cyclicFolderCounterexample, totalInStreams,
          SZ_NUM_CODERS_IN_FOLDER_MAX, SZ_NUM_BONDS_IN_FOLDER_MAX,
          SZ_NUM_PACK_STREAMS_IN_FOLDER_MAX]
  · intro ⟨_, hreach⟩
    have h0 := hreach 0 (by simp [cyclicFolderCounterexample])
    revert h0
    decide

/-- Also shows `ReadUnpackInfo` / `SzGetNextFolderItem` accept a 0-input-stream coder
    (`mainByte & 0x10` with `coderInStreams = 0`), yielding `numPackStreams = 0` and
    leaving `f->PackStreams[0]` uninitialized while `p->PackPositions` may be `NULL`. -/
def zeroInStreamFolderCounterexample : SzFolder :=
  { coders := [{ propsOffset := 0, methodID := 0, numStreams := 0, propsSize := 0 }]
    bonds := []
    packStreams := []
    unpackStream := 0 }

theorem szGetNextFolderItem_allows_zero_packStreams :
    SzGetNextFolderItemValid zeroInStreamFolderCounterexample ∧
    zeroInStreamFolderCounterexample.packStreams = [] := by
  simp [SzGetNextFolderItemValid, zeroInStreamFolderCounterexample, totalInStreams,
        SZ_NUM_CODERS_IN_FOLDER_MAX, SZ_NUM_BONDS_IN_FOLDER_MAX,
        SZ_NUM_PACK_STREAMS_IN_FOLDER_MAX]

/-- Predicate modeling the three topologies accepted by `CheckSupportedFolder` (`7zDec.c:329-404`),
    combined with `f.unpackStream` determined by `SzGetNextFolderItem`. -/
def CheckSupportedFolderTopology (f : SzFolder) : Prop :=
  (f.coders.length = 1 ∧
    (∃ c0, f.coders = [c0] ∧ c0.numStreams = 1) ∧
    f.bonds = [] ∧ f.packStreams = [0] ∧ f.unpackStream = 0) ∨
  (f.coders.length = 2 ∧
    (∃ c0 c1, f.coders = [c0, c1] ∧ c0.numStreams = 1 ∧ c1.numStreams = 1) ∧
    f.bonds = [{ inIndex := 1, outIndex := 0 }] ∧
    f.packStreams = [0] ∧ f.unpackStream = 1) ∨
  (f.coders.length = 4 ∧
    (∃ c0 c1 c2 c3,
      f.coders = [c0, c1, c2, c3] ∧
      c0.numStreams = 1 ∧ c1.numStreams = 1 ∧ c2.numStreams = 1 ∧ c3.numStreams = 4) ∧
    f.bonds = [
      { inIndex := 5, outIndex := 0 },
      { inIndex := 4, outIndex := 1 },
      { inIndex := 3, outIndex := 2 }
    ] ∧
    f.packStreams = [2, 6, 1, 0] ∧ f.unpackStream = 3)

/-- Theorem (`CheckSupportedFolder` Restores DAG Acyclicity):
    Every folder accepted by `CheckSupportedFolder` in `7zDec.c:329-404` satisfies `FolderDAGInv`. -/
theorem checkSupportedFolder_implies_DAG (f : SzFolder)
    (hsupp : CheckSupportedFolderTopology f) :
    FolderDAGInv f := by
  rcases hsupp with h1 | h2 | h4
  · rcases h1 with ⟨_, ⟨c0, hc, hs0⟩, _, _, hu⟩
    refine ⟨?_, ?_⟩
    · intro c hcIn
      rw [hc] at hcIn
      simp at hcIn
      subst hcIn
      omega
    · intro ci hci
      rw [hc] at hci ⊢
      simp at hci
      subst hci
      simp [reachesUnpackIn, hu]
  · rcases h2 with ⟨_, ⟨c0, c1, hc, hs0, hs1⟩, hb, _, hu⟩
    refine ⟨?_, ?_⟩
    · intro c hcIn
      rw [hc] at hcIn
      rcases List.mem_cons.mp hcIn with rfl | hcIn1
      · omega
      · simp at hcIn1
        subst hcIn1
        omega
    · intro ci hci
      rw [hc] at hci ⊢
      simp at hci
      have hciCases : ci = 0 ∨ ci = 1 := by omega
      rcases hciCases with rfl | rfl
      · simp [reachesUnpackIn, hu, nextConsumerCoder, hb, ownerCoder, ownerCoderAux, hc, hs0, hs1]
      · simp [reachesUnpackIn, hu]
  · rcases h4 with ⟨_, ⟨c0, c1, c2, c3, hc, hs0, hs1, hs2, hs3⟩, hb, _, hu⟩
    refine ⟨?_, ?_⟩
    · intro c hcIn
      rw [hc] at hcIn
      simp at hcIn
      rcases hcIn with rfl | rfl | rfl | rfl <;> omega
    · intro ci hci
      rw [hc] at hci ⊢
      simp at hci
      have hciCases : ci = 0 ∨ ci = 1 ∨ ci = 2 ∨ ci = 3 := by omega
      rcases hciCases with rfl | rfl | rfl | rfl <;>
        simp [reachesUnpackIn, hu, nextConsumerCoder, hb, ownerCoder, ownerCoderAux,
              hc, hs0, hs1, hs2, hs3]

/-- Safe `CodersData` slice & `PropsOffset` bounds in `SzAr_DecodeFolder` / `SzFolder_Decode2`
    (`7zDec.c:476, 481, 487, 551, 563, 579, 639-641` and `7zArcIn.c:495-502, 651, 773`):
    when `FoCodersOffsets` is monotonically non-decreasing up to `CodersData` length `codersDataSize`,
    and `SzGetNextFolderItem` checked `propsOffset + propsSize ≤ foEnd - foStart`, the property
    slice `[foStart + propsOffset, foStart + propsOffset + propsSize)` lies strictly within
    `[0, codersDataSize]`. -/
theorem foCodersOffsets_props_slice_in_bounds
    (codersDataSize foStart foEnd propsOffset propsSize : Nat)
    (hmono : foStart ≤ foEnd)
    (hend : foEnd ≤ codersDataSize)
    (hprops : propsOffset + propsSize ≤ foEnd - foStart) :
    foStart + propsOffset + propsSize ≤ codersDataSize := by
  omega

/-- Safe pre-checked BCJ2 stream-size relation (`7zDec.c:511-514` hardened against `SizeT` wrap):
    checking `tempSizes0 ≤ outSize - tempSize3` and `tempSizes1 = outSize - tempSize3 - tempSizes0`
    prevents multi-gigabyte OOM allocations before line 513 and rules out modular overflow. -/
theorem bcj2_folder_sizes_no_overflow (outSize tempSize3 tempSizes0 tempSizes1 : Nat)
    (h3 : tempSize3 ≤ outSize)
    (h0 : tempSizes0 ≤ outSize - tempSize3)
    (h1 : tempSizes1 = outSize - tempSize3 - tempSizes0) :
    tempSize3 + tempSizes0 + tempSizes1 = outSize ∧
    tempSizes0 ≤ outSize ∧ tempSizes1 ≤ outSize := by
  omega

/-- Stream-end underflow hazard in `SzArEx_Open2` (`7zArcIn.c:1515`):
    when `pos < startPosAfterHeader` (e.g. concurrent truncation), unsigned 64-bit subtraction
    `(UInt64)(pos - startPosAfterHeader)` wraps to `≥ 2^63`, bypassing `< nextHeaderOffset + nextHeaderSize`
    whenever `nextHeaderOffset < 2^62` and `nextHeaderSize < 2^48`. -/
theorem open2_truncated_stream_bypasses_eof_check
    (startPos pos nextHeaderOffset nextHeaderSize : Nat)
    (hshrunk : pos < startPos)
    (hspos : startPos < (1 <<< 63))
    (hoff : nextHeaderOffset < (1 <<< 62))
    (hsz : nextHeaderSize < (1 <<< 48)) :
    let wrappedDiff := (1 <<< 64) + pos - startPos
    ¬ (wrappedDiff < nextHeaderOffset + nextHeaderSize) := by
  simp only [Nat.shiftLeft_eq] at *
  omega

/-! ### `SzArEx_Extract` Solid-Block Cache State Machine (`7zArcIn.c:1603-1677`) -/

def kNoFolderSentinel : Nat := 0xFFFFFFFF

/-- Abstract model of a parsed `CSzArEx` archive relevant to `SzArEx_Extract`. -/
structure ArchiveModel where
  numFolders : Nat
  numFiles : Nat
  /-- Maps `fileIndex ↦ Option folderIndex` (`none` models `(UInt32)-1` empty stream). -/
  fileToFolder : Nat → Option Nat
  /-- Uncompressed size of each folder. -/
  folderUnpackSize : Nat → Nat
  /-- Whether `fileIndex` has a defined CRC in `db->CRCs`. -/
  fileHasCRC : Nat → Bool

/-- Caller-maintained solid-folder extraction cache (`*blockIndex`, `*outBuffer`, `*outBufferSize`). -/
structure ExtractCache where
  blockIndex : Nat
  hasBuffer : Bool
  outBufferSize : Nat
  /-- Ghost state tracking whether the currently allocated `*outBuffer` genuinely holds the
      verified decoded contents of `folderIndex` (as opposed to uninitialized `malloc` memory
      or partially-written failed-decode output). -/
  bufferValidFor : Option Nat
  deriving DecidableEq, Repr

/-- Initial cache state required by `7z.h:158` (`*outBuffer` must be `NULL` before first call). -/
def ExtractCache.init (arbitraryBlockIndex arbitraryOutBufSize : Nat) : ExtractCache :=
  { blockIndex := arbitraryBlockIndex
    hasBuffer := false
    outBufferSize := arbitraryOutBufSize
    bufferValidFor := none }

/-- Fundamental safety invariant of the solid-folder cache:
    whenever `hasBuffer = true`, the buffer must contain valid, verified decoded bytes for
    `blockIndex`, and `outBufferSize` must equal `folderUnpackSize blockIndex`. -/
def CacheCoherentInv (ar : ArchiveModel) (cache : ExtractCache) : Prop :=
  cache.hasBuffer = true →
    cache.blockIndex < ar.numFolders ∧
    cache.bufferValidFor = some cache.blockIndex ∧
    cache.outBufferSize = ar.folderUnpackSize cache.blockIndex

theorem init_establishes_cacheCoherentInv (ar : ArchiveModel) (bi sz : Nat) :
    CacheCoherentInv ar (ExtractCache.init bi sz) := by
  intro h
  cases h

inductive ExtractResult where
  | ok (returnedBufferValid : Bool)
  | error
  deriving DecidableEq, Repr

/-- Faithful model of upstream `SzArEx_Extract` (`7zArcIn.c:1630-1676`):
    Notice lines 1642-1660: when `unpackSize > 0` and allocation succeeds (`allocOk = true`),
    `*blockIndex` is set to `folderIndex` and `*tempBuf` is non-NULL (`hasBuffer := true`),
    even if `SzAr_DecodeFolder` returns an error (`decodeOk = false`)! -/
def szArExExtractUpstream
    (ar : ArchiveModel) (fileIndex : Nat) (cache : ExtractCache)
    (allocOk decodeOk crcMatches : Bool) : ExtractCache × ExtractResult :=
  match ar.fileToFolder fileIndex with
  | none =>
    ({ blockIndex := kNoFolderSentinel
       hasBuffer := false
       outBufferSize := 0
       bufferValidFor := none }, .ok true)
  | some folderIndex =>
    let needDecode := (!cache.hasBuffer) || (cache.blockIndex != folderIndex)
    let (cache1, res1Ok) : ExtractCache × Bool :=
      if needDecode then
        let unpackSize := ar.folderUnpackSize folderIndex
        if unpackSize == 0 then
          ({ blockIndex := folderIndex
             hasBuffer := false
             outBufferSize := 0
             bufferValidFor := if decodeOk then some folderIndex else none },
           decodeOk)
        else if !allocOk then
          ({ blockIndex := folderIndex
             hasBuffer := false
             outBufferSize := unpackSize
             bufferValidFor := none },
           false)
        else if decodeOk then
          ({ blockIndex := folderIndex
             hasBuffer := true
             outBufferSize := unpackSize
             bufferValidFor := some folderIndex },
           true)
        else
          -- BUG (`7zArcIn.c:1642-1660`): `*blockIndex = folderIndex` and `*tempBuf != NULL`
          -- remain live in `cache` with uninitialized / corrupt buffer contents!
          ({ blockIndex := folderIndex
             hasBuffer := true
             outBufferSize := unpackSize
             bufferValidFor := none },
           false)
      else
        (cache, true)
    if !res1Ok then
      (cache1, .error)
    else if ar.fileHasCRC fileIndex && !crcMatches then
      (cache1, .error)
    else
      let isGenuine := (cache1.bufferValidFor == some folderIndex) || (ar.folderUnpackSize folderIndex == 0)
      (cache1, .ok isGenuine)

/-- Theorem (Upstream `SzArEx_Extract` Cache-Poisoning Bug, `7zArcIn.c:1630-1662`):
    Starting from a valid initial cache (`*outBuffer = NULL`), if solid folder 0 (`unpackSize = 64`)
    contains file 0 and file 1 (without per-file CRC), and extracting file 0 fails inside
    `SzAr_DecodeFolder` after `*tempBuf` allocation succeeds, then:
    1. Call 1 returns `.error` while leaving `CacheCoherentInv` violated (`bufferValidFor = none`).
    2. Call 2 on file 1 in the same archive returns `.ok false` — reporting `SZ_OK` while
       handing the caller uninitialized/corrupt heap memory without re-running `SzAr_DecodeFolder`! -/
theorem buggy_extract_breaks_cache_coherence :
    ∃ (ar : ArchiveModel),
      let c0 := ExtractCache.init kNoFolderSentinel 0
      CacheCoherentInv ar c0 ∧
      let (c1, r1) := szArExExtractUpstream ar 0 c0 true false false
      r1 = .error ∧ ¬ CacheCoherentInv ar c1 ∧
      let (_, r2) := szArExExtractUpstream ar 1 c1 true false false
      r2 = .ok false := by
  let ar : ArchiveModel :=
    { numFolders := 1
      numFiles := 2
      fileToFolder := fun _ => some 0
      folderUnpackSize := fun _ => 64
      fileHasCRC := fun _ => false }
  refine ⟨ar, ?_⟩
  refine ⟨init_establishes_cacheCoherentInv ar kNoFolderSentinel 0, ?_⟩
  refine ⟨rfl, ?_, rfl⟩
  intro hcoh
  have h : (szArExExtractUpstream ar 0 (ExtractCache.init kNoFolderSentinel 0) true false false).1.hasBuffer = true := rfl
  have hvalid := (hcoh h).2.1
  revert hvalid
  decide

/-- Repaired `SzArEx_Extract` transition: flushes `*tempBuf` and resets `*blockIndex` whenever
    `SzAr_DecodeFolder` fails, ensuring failed decodes never poison the solid-block cache. -/
def szArExExtractFixed
    (ar : ArchiveModel) (fileIndex : Nat) (cache : ExtractCache)
    (allocOk decodeOk crcMatches : Bool) : ExtractCache × ExtractResult :=
  match ar.fileToFolder fileIndex with
  | none =>
    ({ blockIndex := kNoFolderSentinel
       hasBuffer := false
       outBufferSize := 0
       bufferValidFor := none }, .ok true)
  | some folderIndex =>
    let needDecode := (!cache.hasBuffer) || (cache.blockIndex != folderIndex)
    let (cache1, res1Ok) : ExtractCache × Bool :=
      if needDecode then
        let unpackSize := ar.folderUnpackSize folderIndex
        if unpackSize == 0 then
          if decodeOk then
            ({ blockIndex := folderIndex
               hasBuffer := false
               outBufferSize := 0
               bufferValidFor := some folderIndex }, true)
          else
            ({ blockIndex := kNoFolderSentinel
               hasBuffer := false
               outBufferSize := 0
               bufferValidFor := none }, false)
        else if allocOk && decodeOk then
          ({ blockIndex := folderIndex
             hasBuffer := true
             outBufferSize := unpackSize
             bufferValidFor := some folderIndex }, true)
        else
          ({ blockIndex := kNoFolderSentinel
             hasBuffer := false
             outBufferSize := 0
             bufferValidFor := none }, false)
      else
        (cache, true)
    if !res1Ok then
      (cache1, .error)
    else if ar.fileHasCRC fileIndex && !crcMatches then
      (cache1, .error)
    else
      let isGenuine := (cache1.bufferValidFor == some folderIndex) || (ar.folderUnpackSize folderIndex == 0)
      (cache1, .ok isGenuine)

/-- Theorem (Repaired `SzArEx_Extract` Preserves Cache Coherence & Never Returns Uninitialized Data):
    For every valid `fileIndex` (`folderIndex < ar.numFolders`), `szArExExtractFixed` preserves
    `CacheCoherentInv` across all allocation/decode/CRC failures, and every `.ok` return guarantees
    `returnedBufferValid = true`. -/
theorem fixed_extract_preserves_cache_coherence
    (ar : ArchiveModel) (fileIndex : Nat) (cache : ExtractCache)
    (allocOk decodeOk crcMatches : Bool)
    (hvalidFile : ∀ fi, ar.fileToFolder fileIndex = some fi → fi < ar.numFolders)
    (hinv : CacheCoherentInv ar cache) :
    let (cache', res) := szArExExtractFixed ar fileIndex cache allocOk decodeOk crcMatches
    CacheCoherentInv ar cache' ∧ (∀ validFlag, res = .ok validFlag → validFlag = true) := by
  dsimp [szArExExtractFixed]
  cases hftf : ar.fileToFolder fileIndex with
  | none =>
    simp [CacheCoherentInv]
  | some fi =>
    have hfiLt : fi < ar.numFolders := hvalidFile fi hftf
    by_cases hneed : ((!cache.hasBuffer) || (cache.blockIndex != fi)) = true
    · simp [hneed]
      by_cases hsz : ar.folderUnpackSize fi = 0
      · simp [hsz]
        cases decodeOk <;> cases hfc : ar.fileHasCRC fileIndex <;> cases crcMatches <;>
          simp [CacheCoherentInv, hsz]
      · simp [hsz]
        cases allocOk <;> cases decodeOk <;>
          cases hfc : ar.fileHasCRC fileIndex <;> cases crcMatches <;>
          simp [CacheCoherentInv, hfiLt]
    · simp [hneed]
      have hhas : cache.hasBuffer = true := by
        cases h : cache.hasBuffer
        · simp [h] at hneed
        · rfl
      have hbi : cache.blockIndex = fi := by
        simp [hhas] at hneed
        exact hneed
      rcases hinv hhas with ⟨_, hbufValid, _⟩
      subst hbi
      cases hfc : ar.fileHasCRC fileIndex <;> cases crcMatches <;>
        simp [hinv, hbufValid]

/-- Demonstrates the `7zArcIn.c:1314` vs `1351` `UnpackPositions` boundary shift:
    when Folder 0 has `numSubStreams = 0` and `folder0Size > 0`, and Folder 1 has
    `numSubStreams = 2` with substream 0 of size `v0` and total `folder1Size ≥ folder0Size + v0`,
    `SzReadHeader2` sets `UnpackPositions = [0, folder0Size + v0, folder1Size]`, inflating file 0's
    computed size from `v0` to `folder0Size + v0` and shrinking file 1's size by `folder0Size`. -/
def szReadHeader2TwoFilesAfterZeroSubstreamFolder (folder0Size v0 folder1Size : Nat) :
    List Nat :=
  let u0 := 0 -- written at 7zArcIn.c:1314 BEFORE skipping 0-substream Folder 0
  let unpackPosAfterSkip := u0 + folder0Size -- 7zArcIn.c:1351
  let unpackPosAfterFile0 := unpackPosAfterSkip + v0 -- 7zArcIn.c:1385
  let u1 := unpackPosAfterFile0 -- 7zArcIn.c:1314 for i = 1
  let startFolder1Pos := u0 -- 7zArcIn.c:1367 (`UnpackPositions[FolderToFile[1]] = UnpackPositions[0]`)
  let u2 := startFolder1Pos + folder1Size -- 7zArcIn.c:1370 & 1408
  [u0, u1, u2]

theorem zero_substream_folder_shifts_first_file_size (folder0Size v0 folder1Size : Nat)
    (hpos : 0 < folder0Size) :
    match szReadHeader2TwoFilesAfterZeroSubstreamFolder folder0Size v0 folder1Size with
    | [u0, u1, _] => u1 - u0 ≠ v0 ∧ u1 - u0 = folder0Size + v0
    | _ => False := by
  simp [szReadHeader2TwoFilesAfterZeroSubstreamFolder]
  omega

/-- Monotonicity of `UnpackPositions` step (`7zArcIn.c:1368-1370`):
    because `SzReadHeader2` checks `folderUnpackSize ≥ unpackPos - startFolderUnpackPos` where
    `startFolderUnpackPos ≤ unpackPos`, the updated `startFolderUnpackPos + folderUnpackSize`
    never decreases `unpackPos` (ruling out unsigned subtraction underflow at `7zArcIn.c:1668`). -/
theorem unpackPos_folder_end_monotone (startFolderUnpackPos unpackPos folderUnpackSize : Nat)
    (hstart : startFolderUnpackPos ≤ unpackPos)
    (hcheck : unpackPos - startFolderUnpackPos ≤ folderUnpackSize) :
    unpackPos ≤ startFolderUnpackPos + folderUnpackSize := by
  omega

end Archive

/-!
## 3. BCJ2 4-Stream x86 Filter Decoder (`C/Bcj2.h`, `C/Bcj2.c`)

Models and proves:
1. **Probability bounds (`31 ≤ prob ≤ 2017`) and single-byte normalization sufficiency:**
   In `Bcj2.c:98`, normalization uses `if (p->range < kTopValue)` (single `<<= 8`, NOT `while`).
   We prove (`bcj2_range_single_norm_sufficient`) that starting from `range ≥ 2^24`, one binary
   range-decode step leaves `range ≥ 253,952 > 2^16` (so one `<< 8` restores `range ≥ 2^24`,
   and `range` never enters the `p->range <= 5` initialization/error region of `Bcj2.c:32`).
2. **Branchless probability table index & CALL/JUMP selector bounds (`Bcj2.c:212-214, 242`):**
   Proves that for all three x86 branch markers (`0xe8`, `0xe9`, `0x0f 0x80..0x8f`), the probability
   index lies strictly within `[0, 257]` (`sizeof(probs)/sizeof(probs[0]) = 258`) and `cj ∈ {1, 2}`.
3. **4-Stream cursor bounds & in-place `dest` / `MAIN` overlap (`Bcj2.h:68-90`, `7zDec.c:458,519`):**
   Proves that `dest + remCall + remJump + pendingTemp ≤ bufMain` is preserved by every decoder
   transition when `remCall % 4 = 0` and `remJump % 4 = 0`, guaranteeing `dest` never overtakes
   `bufMain` during in-place decoding in `SzFolder_Decode2`.
-/
namespace Bcj2

def kTopValue : Nat := 16777216       -- 1 <<< 24
def kBitModelTotal : Nat := 2048      -- 1 <<< 11
def kProbMin : Nat := 31
def kProbMax : Nat := 2017

def updateProb0 (ttt : Nat) : Nat :=
  ttt + ((kBitModelTotal - ttt) / 32)

def updateProb1 (ttt : Nat) : Nat :=
  ttt - (ttt / 32)

theorem bcj2_prob_init_in_bounds : kProbMin ≤ kBitModelTotal / 2 ∧ kBitModelTotal / 2 ≤ kProbMax := by
  simp [kProbMin, kProbMax, kBitModelTotal]

/-- Theorem (`Bcj2.c:24-25, 227, 234`):
    Starting at `1024`, both probability update rules preserve `31 ≤ prob ≤ 2017`. -/
theorem bcj2_prob_update_bounds (ttt : Nat) (hlo : kProbMin ≤ ttt) (hhi : ttt ≤ kProbMax) :
    (kProbMin ≤ updateProb0 ttt ∧ updateProb0 ttt ≤ kProbMax) ∧
    (kProbMin ≤ updateProb1 ttt ∧ updateProb1 ttt ≤ kProbMax) := by
  simp only [kProbMin, kProbMax, kBitModelTotal, updateProb0, updateProb1] at *
  omega

/-- Single-byte normalization step (`Bcj2.c:98-108`). -/
def normalizeOnce (range : Nat) : Nat :=
  if range < kTopValue then range * 256 else range

/-- Theorem (`Bcj2.c:98, 222-235` Single-Byte Normalization & `range > 5` Invariant):
    Whenever `range ≥ 2^24` (`kTopValue`) and `31 ≤ ttt ≤ 2017`:
    1. Both `bound = (range / 2048) * ttt` and `range - bound` are `≥ 253,952 > 65,536` (`> 5`,
       so `Bcj2.c:32`'s `p->range <= 5` init/error guard can never trigger in the main loop).
    2. A single byte shift (`normalizeOnce`) restores `≥ kTopValue` (`2^24`). -/
theorem bcj2_range_single_norm_sufficient (range ttt : Nat)
    (hrange : kTopValue ≤ range)
    (hlo : kProbMin ≤ ttt) (hhi : ttt ≤ kProbMax) :
    let bound := (range / kBitModelTotal) * ttt
    let r0 := bound
    let r1 := range - bound
    253952 ≤ r0 ∧ 253952 ≤ r1 ∧
    kTopValue ≤ normalizeOnce r0 ∧ kTopValue ≤ normalizeOnce r1 := by
  dsimp only
  simp only [kTopValue, kBitModelTotal, kProbMin, kProbMax, normalizeOnce] at *
  have hdiv : 8192 ≤ range / 2048 := by omega
  have hrem : range = 2048 * (range / 2048) + range % 2048 := (Nat.div_add_mod range 2048).symm
  have hboundLo : 253952 ≤ (range / 2048) * ttt := by
    have h1 : 8192 * 31 ≤ (range / 2048) * 31 := Nat.mul_le_mul_right 31 hdiv
    have h2 : (range / 2048) * 31 ≤ (range / 2048) * ttt := Nat.mul_le_mul_left (range / 2048) hlo
    omega
  have hboundHi : (range / 2048) * ttt ≤ (range / 2048) * 2017 :=
    Nat.mul_le_mul_left (range / 2048) hhi
  have hr1Lo : 253952 ≤ range - (range / 2048) * ttt := by
    omega
  refine ⟨hboundLo, hr1Lo, ?_, ?_⟩
  · by_cases hlt0 : (range / 2048) * ttt < 16777216 <;> simp [hlt0] <;> omega
  · by_cases hlt1 : range - (range / 2048) * ttt < 16777216 <;> simp [hlt1] <;> omega

/-- Arithmetic equivalence of the branchless probability index (`Bcj2.c:212-214`) on `Nat`
    for `prevByte < 256` and marker byte `b < 256` (`v = prevByte * 2^24 + b`):
    - `c = ((b + 0x17) / 64) % 2` (since `(prevByte * 2^24) / 64` is a multiple of `2^18`, hence even!)
    - `(0 - c) & prevByte` equals `prevByte` if `c = 1` else `0`
    - `(v >> 5) & 1` equals `(b / 32) % 2` (since `prevByte * 2^24` is a multiple of `64`). -/
def bcj2ProbIndexNat (prevByte b : Nat) : Nat :=
  let c := ((b + 0x17) / 64) % 2
  let maskedPrev := if c = 1 then prevByte else 0
  maskedPrev + c + ((b / 32) % 2)

def bcj2StreamSelectorNat (b : Nat) : Nat :=
  (((b + 0x57) / 64) % 2) + 1

/-- Theorem (`Bcj2.c:212-214, 242` Probability Table & Stream Selector Bounds):
    For every `prevByte < 256` and all three x86 branch marker classes (`0xe8`, `0xe9`, `0x80 ≤ b ≤ 0x8f`):
    - `0xe8` maps to `probs[prevByte + 2]` (`2..257`) and `BCJ2_STREAM_CALL` (`1`);
    - `0xe9` maps to `probs[1]` and `BCJ2_STREAM_JUMP` (`2`);
    - `0x80 ≤ b ≤ 0x8f` maps to `probs[0]` and `BCJ2_STREAM_JUMP` (`2`).
    Every reachable index satisfies `idx < 258`. -/
theorem bcj2_prob_index_and_selector_valid (prevByte b : Nat) (hprev : prevByte < 256) :
    (bcj2ProbIndexNat prevByte 0xe8 = prevByte + 2 ∧
     bcj2ProbIndexNat prevByte 0xe8 < 258 ∧
     bcj2StreamSelectorNat 0xe8 = 1) ∧
    (bcj2ProbIndexNat prevByte 0xe9 = 1 ∧
     bcj2ProbIndexNat prevByte 0xe9 < 258 ∧
     bcj2StreamSelectorNat 0xe9 = 2) ∧
    (0x80 ≤ b → b ≤ 0x8f →
     bcj2ProbIndexNat prevByte b = 0 ∧
     bcj2ProbIndexNat prevByte b < 258 ∧
     bcj2StreamSelectorNat b = 2) := by
  refine ⟨?_, ?_, fun hlo hhi => ?_⟩
  · simp [bcj2ProbIndexNat, bcj2StreamSelectorNat]
    omega
  · simp [bcj2ProbIndexNat, bcj2StreamSelectorNat]
  · have hc0 : ((b + 0x17) / 64) % 2 = 0 := by omega
    have hb5 : (b / 32) % 2 = 0 := by omega
    have hs : ((b + 0x57) / 64) % 2 = 1 := by omega
    simp [bcj2ProbIndexNat, bcj2StreamSelectorNat, hc0, hb5, hs]

/-- Cursor state of `CBcj2Dec` (`Bcj2.h:93-107`) for modeling the 4 input streams and
    in-place overlap between `dest` (`[dest, destLim)`) and `MAIN` (`[bufMain, limMain)`). -/
structure Bcj2Cursors where
  bufMain : Nat
  limMain : Nat
  bufCall : Nat
  limCall : Nat
  bufJump : Nat
  limJump : Nat
  bufRc : Nat
  limRc : Nat
  dest : Nat
  destLim : Nat
  /-- Number of pending converted displacement bytes (`0..4`) buffered in `p->temp`
      when `state ∈ {BCJ2_DEC_STATE_ORIG_0 .. ORIG_3}`. -/
  pendingTemp : Nat
  deriving DecidableEq, Repr

/-- Top-down cursor & in-place overlap safety invariant for `CBcj2Dec` (`Bcj2.h:46-90`):
    - Every cursor satisfies `buf ≤ lim`;
    - `CALL` and `JUMP` remaining byte counts are multiples of 4 (`Bcj2.h:47-48`);
    - `pendingTemp ≤ 4`;
    - In-place non-overtaking reserve invariant:
      `dest + (limCall - bufCall) + (limJump - bufJump) + pendingTemp ≤ bufMain`
      and `limMain ≤ destLim`. -/
def Bcj2OverlapInv (s : Bcj2Cursors) : Prop :=
  s.bufMain ≤ s.limMain ∧
  s.bufCall ≤ s.limCall ∧
  s.bufJump ≤ s.limJump ∧
  s.bufRc ≤ s.limRc ∧
  s.dest ≤ s.destLim ∧
  (s.limCall - s.bufCall) % 4 = 0 ∧
  (s.limJump - s.bufJump) % 4 = 0 ∧
  s.pendingTemp ≤ 4 ∧
  s.dest + (s.limCall - s.bufCall) + (s.limJump - s.bufJump) + s.pendingTemp ≤ s.bufMain ∧
  s.limMain ≤ s.destLim

/-- Initial setup in `SzFolder_Decode2` (`7zDec.c:458, 511-525`):
    `dest = 0`, `destLim = outSize`, `bufMain = outSize - tempSize3`, `limMain = outSize`,
    `limCall - bufCall = tempSizes0`, `limJump - bufJump = tempSizes1`, `pendingTemp = 0`. -/
theorem szFolderDecode2_establishes_bcj2OverlapInv
    (outSize tempSize3 tempSizes0 tempSizes1 s3Size : Nat)
    (halign0 : tempSizes0 % 4 = 0)
    (halign1 : tempSizes1 % 4 = 0)
    (hsum : tempSize3 + tempSizes0 + tempSizes1 = outSize) :
    Bcj2OverlapInv {
      bufMain := outSize - tempSize3
      limMain := outSize
      bufCall := 0, limCall := tempSizes0
      bufJump := 0, limJump := tempSizes1
      bufRc := 0, limRc := s3Size
      dest := 0, destLim := outSize
      pendingTemp := 0
    } := by
  simp only [Bcj2OverlapInv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Transition 1 (`ONE_ITER`, `Bcj2.c:128-135, 198-202`):
    copying `1` byte from `bufMain` to `dest` when `pendingTemp = 0`, `bufMain < limMain`,
    and `dest < destLim` preserves `Bcj2OverlapInv` and reads `bufMain` before `dest` writes
    (`dest ≤ bufMain`). -/
theorem bcj2_copy_main_byte_preserves_inv (s : Bcj2Cursors)
    (hinv : Bcj2OverlapInv s)
    (hpt : s.pendingTemp = 0)
    (hmain : s.bufMain < s.limMain)
    (hdest : s.dest < s.destLim) :
    s.dest ≤ s.bufMain ∧
    Bcj2OverlapInv { s with bufMain := s.bufMain + 1, dest := s.dest + 1 } := by
  rcases hinv with ⟨hm, hc, hj, hr, hd, hcm4, hjm4, _, hres, hlim⟩
  refine ⟨by omega, ?_⟩
  simp only [Bcj2OverlapInv]
  refine ⟨?_, hc, hj, hr, ?_, hcm4, hjm4, ?_, ?_, hlim⟩ <;> omega

/-- Transition 2 (`Bcj2.c:242-273` CALL stream 4-byte displacement decode):
    when `pendingTemp = 0` and `bufCall ≠ limCall`, the `(limCall - bufCall) % 4 = 0` invariant
    guarantees at least 4 readable bytes (`bufCall + 4 ≤ limCall` — proving why violating
    `(BUF_SIZE & 3) == 0` would read 1..3 bytes out-of-bounds!), and writing `written = min 4 (destLim - dest)`
    bytes while buffering `4 - written` bytes in `pendingTemp` strictly preserves `Bcj2OverlapInv`. -/
theorem bcj2_decode_call_disp_preserves_inv (s : Bcj2Cursors)
    (hinv : Bcj2OverlapInv s)
    (hpt : s.pendingTemp = 0)
    (hne : s.bufCall ≠ s.limCall) :
    s.bufCall + 4 ≤ s.limCall ∧
    let written := min 4 (s.destLim - s.dest)
    Bcj2OverlapInv {
      s with
      bufCall := s.bufCall + 4
      dest := s.dest + written
      pendingTemp := 4 - written
    } := by
  rcases hinv with ⟨hm, hc, hj, hr, hd, hcm4, hjm4, _, hres, hlim⟩
  have h4 : s.bufCall + 4 ≤ s.limCall := by omega
  refine ⟨h4, ?_⟩
  dsimp only
  simp only [Bcj2OverlapInv]
  refine ⟨hm, h4, hj, hr, ?_, ?_, hjm4, ?_, ?_, hlim⟩ <;> omega

/-- Transition 3 (`Bcj2.c:69-86` flushing 1 pending byte from `p->temp` to `dest`):
    when `0 < pendingTemp` and `dest < destLim`, writing 1 byte to `dest` does NOT overwrite
    unread `MAIN` bytes (`dest < bufMain`) and preserves `Bcj2OverlapInv`. -/
theorem bcj2_flush_temp_byte_preserves_inv (s : Bcj2Cursors)
    (hinv : Bcj2OverlapInv s)
    (hpt : 0 < s.pendingTemp)
    (hdest : s.dest < s.destLim) :
    s.dest < s.bufMain ∧
    Bcj2OverlapInv { s with dest := s.dest + 1, pendingTemp := s.pendingTemp - 1 } := by
  rcases hinv with ⟨hm, hc, hj, hr, hd, hcm4, hjm4, hpt4, hres, hlim⟩
  refine ⟨by omega, ?_⟩
  simp only [Bcj2OverlapInv]
  refine ⟨hm, hc, hj, hr, ?_, hcm4, hjm4, ?_, ?_, hlim⟩ <;> omega

end Bcj2

/-!
## 4. PPMd7 Custom Sub-Allocator, Context Model, and Range Decoder
   (`C/Ppmd.h`, `C/Ppmd7.h`, `C/Ppmd7.c`, `C/Ppmd7Dec.c`)

Models and proves:
1. **Custom Heap Sub-Allocator Arena Partition (`Ppmd7.c:1032-1093`):**
   `alignOffset ≤ text < unitsStart ≤ loUnit ≤ hiUnit ≤ alignOffset + size - 12`, with 4-byte
   alignment of every 12-byte unit (`(alignOffset + size) % 4 = 0` and `UNIT_SIZE = 12`).
   - Proves `restartModel_establishes_arenaInv` for all `size ≥ 2048` (`PPMD7_MIN_MEM_SIZE`).
   - Proves two direct-API bugs when `Ppmd7_Alloc` is called outside `SzDecodePpmd`:
     (a) `alloc_uint32_wraps_to_zero`: `UInt32` `AlignOffset + size` wraps to `0` for `size ≥ 0xFFFFFFFD` (`Ppmd7.c:98`);
     (b) `restartModel_overflows_small_size`: `size < 1824` overflows `[loUnit, hiUnit)` during `RestartModel` (`Ppmd7.c:364-367`).
   - Proves `allocContext_hiUnit_preserves_arenaInv`, `allocUnits_loUnit_preserves_arenaInv`,
     `allocUnitsRare_carve_preserves_arenaInv` (showing why strict `us - text > numBytes` at
     `Ppmd7.c:274` preserves `text < unitsStart`, and why `glueCount` never underflows).
2. **`Ppmd7_GlueFreeBlocks` Uninitialized `NU` Read (`Ppmd7.c:178-179, 222-224`):**
   Models the sentinel at `LoUnit` (`Stamp = 1`, `NU` left uninitialized in `[LoUnit, HiUnit)`)
   and proves that reading `node2->NU` *before* checking `node2->Stamp != EMPTY_NODE` reads
   uninitialized bytes whenever `LoUnit ≠ HiUnit`, whereas checking `Stamp` first avoids it.
3. **Range Decoder Division-by-Zero Freedom (`Ppmd7Dec.c:53, 78, 233`) & `CreateSuccessors` (`Ppmd7.c:527`):**
   Proves that `Range ≥ 2^24` and `1 ≤ total < 2^16` imply `Range / total ≥ 256 > 0` (and two
   `<< 8` normalizations restore `Range ≥ 2^24`), and `EscapeFreq ≥ 1` implies `2 * s0 ≥ 2 > 0`
   and `newFreq ≤ 125 ≤ 128` (`BinSumm[128][64]` indices strictly in bounds).
4. **Signed `Int32` `RunLength` Overflow UB (`Ppmd7Dec.c:159`, `Ppmd7.c:995`, `Ppmd7.h:78,130`):**
   Proves `runLength_overflows_int32` after `2^31 + 13` repeated binary-context symbols without
   unit allocation.
-/
namespace Ppmd7

def UNIT_SIZE : Nat := 12
def PPMD7_MIN_MEM_SIZE : Nat := 1 <<< 11           -- 2048
def PPMD7_MAX_MEM_SIZE : Nat := 0xFFFFFFFF - 12 * 3

/-- Sub-allocator arena cursors as byte offsets from `p->Base` (`Ppmd7.h:80-83`). -/
structure Ppmd7Arena where
  size : Nat
  alignOffset : Nat
  text : Nat
  unitsStart : Nat
  loUnit : Nat
  hiUnit : Nat
  glueCount : Nat
  deriving DecidableEq, Repr

/-- Full arena partition & alignment invariant (`Ppmd7.c:1032-1056`):
    - `alignOffset = (4 - size % 4) % 4`, making `alignOffset + size` a multiple of 4;
    - `alignOffset ≤ text < unitsStart ≤ loUnit ≤ hiUnit`;
    - `hiUnit + 12 ≤ alignOffset + size` (the top 12 bytes hold the permanent root order-0 context);
    - `unitsStart`, `loUnit`, and `hiUnit` sit at exact 12-byte (`UNIT_SIZE`) multiples below
      `alignOffset + size`, which also makes every unit 4-byte aligned relative to `Base`! -/
def ArenaInv (a : Ppmd7Arena) : Prop :=
  PPMD7_MIN_MEM_SIZE ≤ a.size ∧
  a.alignOffset = (4 - a.size % 4) % 4 ∧
  (a.alignOffset + a.size) % 4 = 0 ∧
  a.alignOffset ≤ a.text ∧
  a.text < a.unitsStart ∧
  a.unitsStart ≤ a.loUnit ∧
  a.loUnit ≤ a.hiUnit ∧
  a.hiUnit + UNIT_SIZE ≤ a.alignOffset + a.size ∧
  (a.alignOffset + a.size - a.hiUnit) % UNIT_SIZE = 0 ∧
  (a.hiUnit - a.loUnit) % UNIT_SIZE = 0 ∧
  (a.loUnit - a.unitsStart) % UNIT_SIZE = 0

/-- Theorem: every 12-byte unit boundary in `[unitsStart, alignOffset + size]` is 4-byte aligned
    relative to `p->Base` (`offset % 4 = 0`), justifying 4-byte alignment inside the unit arena. -/
theorem arenaInv_units_4byte_aligned (a : Ppmd7Arena) (hinv : ArenaInv a) :
    a.hiUnit % 4 = 0 ∧ a.loUnit % 4 = 0 ∧ a.unitsStart % 4 = 0 := by
  rcases hinv with ⟨_, _, htop4, _, _, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩
  simp only [UNIT_SIZE] at *
  omega

/-- State produced by `Ppmd7_RestartModel` (`Ppmd7.c:348-375`) for an allocated `size`. -/
def restartModelArena (size : Nat) : Ppmd7Arena :=
  let alignOffset := (4 - size % 4) % 4
  let text := alignOffset
  let hi0 := text + size
  let u0 := hi0 - (size / 8 / UNIT_SIZE) * 7 * UNIT_SIZE
  { size := size
    alignOffset := alignOffset
    text := text
    unitsStart := u0
    loUnit := u0 + 128 * UNIT_SIZE
    hiUnit := hi0 - UNIT_SIZE
    glueCount := 0 }

/-- Theorem (`Ppmd7_RestartModel` Establishes `ArenaInv` for all `size ≥ PPMD7_MIN_MEM_SIZE`):
    Because `2048 / 96 = 21` and `21 * 84 = 1764 ≥ 1536 + 12 = 1548`, `[loUnit, hiUnit)` is
    non-negative and `[text, unitsStart)` has at least `284 > 0` bytes of raw-text headroom. -/
theorem restartModel_establishes_arenaInv (size : Nat)
    (hmin : PPMD7_MIN_MEM_SIZE ≤ size) :
    ArenaInv (restartModelArena size) := by
  simp only [ArenaInv, restartModelArena, PPMD7_MIN_MEM_SIZE, UNIT_SIZE, Nat.shiftLeft_eq] at *
  have hdiv : 21 ≤ size / 8 / 12 := by omega
  have hbound : (size / 8 / 12) * 84 ≤ size := by omega
  refine ⟨hmin, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Direct-API Hazard 1 (`Ppmd7.c:97-98`):
    In `Ppmd7_Alloc(CPpmd7 *p, UInt32 size, ISzAllocPtr alloc)`, both `p->AlignOffset` and `size`
    have type `UInt32`, so `p->AlignOffset + size` wraps around modulo `2^32` to `0` BEFORE
    widening to `size_t` whenever `size ∈ {0xFFFFFFFD, 0xFFFFFFFE, 0xFFFFFFFF}`! -/
theorem alloc_uint32_wraps_to_zero :
    (∀ s : UInt32, s = 0xFFFFFFFD ∨ s = 0xFFFFFFFE ∨ s = 0xFFFFFFFF →
      let alignOffset : UInt32 := ((4 : UInt32) - s) &&& 3
      alignOffset + s = 0) := by
  intro s hs
  rcases hs with rfl | rfl | rfl <;> decide

/-- Direct-API Hazard 2 (`Ppmd7.c:356-367`):
    If `Ppmd7_Alloc` is called directly with `size < 1824` (below `PPMD7_MIN_MEM_SIZE = 2048`,
    since `Ppmd7_Alloc` lacks a minimum-size guard), `Ppmd7_RestartModel` advances `LoUnit`
    (`+ 1536` bytes for 256 `CPpmd_State`s) strictly past `HiUnit` (`- 12` bytes)! -/
theorem restartModel_overflows_small_size (size : Nat) (hsmall : size < 1824) :
    let hi0 := size
    let u0 := hi0 - (size / 8 / UNIT_SIZE) * 7 * UNIT_SIZE
    u0 + 128 * UNIT_SIZE > hi0 - UNIT_SIZE ∨ hi0 < UNIT_SIZE := by
  simp only [UNIT_SIZE]
  omega

/-- Context allocation from `HiUnit` (`Ppmd7.c:536-537`: `if (p->HiUnit != p->LoUnit) p->HiUnit -= 12`)
    preserves `ArenaInv`. -/
theorem allocContext_hiUnit_preserves_arenaInv (a : Ppmd7Arena)
    (hinv : ArenaInv a)
    (hne : a.hiUnit ≠ a.loUnit) :
    a.loUnit ≤ a.hiUnit - UNIT_SIZE ∧
    ArenaInv { a with hiUnit := a.hiUnit - UNIT_SIZE } := by
  rcases hinv with ⟨hsz, halOff, htop4, htxt, htxtUs, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩
  simp only [ArenaInv, UNIT_SIZE] at *
  have hgap : a.loUnit + 12 ≤ a.hiUnit := by omega
  refine ⟨by omega, hsz, halOff, htop4, htxt, htxtUs, huslo, ?_, ?_, ?_, ?_, hus12⟩ <;> omega

/-- State-vector allocation from `LoUnit` (`Ppmd7.c:292-298`: `(p->HiUnit - lo) >= numBytes`)
    for `nu ≥ 1` units preserves `ArenaInv`. -/
theorem allocUnits_loUnit_preserves_arenaInv (a : Ppmd7Arena) (nu : Nat)
    (hinv : ArenaInv a)
    (hnu : 1 ≤ nu)
    (hfit : nu * UNIT_SIZE ≤ a.hiUnit - a.loUnit) :
    ArenaInv { a with loUnit := a.loUnit + nu * UNIT_SIZE } := by
  rcases hinv with ⟨hsz, halOff, htop4, htxt, htxtUs, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩
  simp only [ArenaInv, UNIT_SIZE] at *
  refine ⟨hsz, halOff, htop4, htxt, htxtUs, ?_, ?_, hhiTop, hhi12, ?_, ?_⟩ <;> omega

/-- Rare fallback carving from `[Text, UnitsStart)` (`Ppmd7.c:258-275`):
    1. If `glueCount = 0`, `GlueFreeBlocks` resets `glueCount := 255` before `glueCount--`, so
       `glueCount` never underflows.
    2. Because `Ppmd7.c:274` checks strict inequality `(us - p->Text) > numBytes` (`numBytes < unitsStart - text`),
       the new `unitsStart' = unitsStart - numBytes` strictly preserves `text < unitsStart'`! -/
theorem allocUnitsRare_carve_preserves_arenaInv (a : Ppmd7Arena) (nu : Nat)
    (hinv : ArenaInv a)
    (hnu : 1 ≤ nu)
    (hstrict : nu * UNIT_SIZE < a.unitsStart - a.text) :
    let glueAfterCheck := if a.glueCount == 0 then 255 else a.glueCount
    1 ≤ glueAfterCheck ∧
    ArenaInv {
      a with
      unitsStart := a.unitsStart - nu * UNIT_SIZE
      glueCount := glueAfterCheck - 1
    } := by
  rcases hinv with ⟨hsz, halOff, htop4, htxt, htxtUs, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩
  simp only [ArenaInv, UNIT_SIZE] at *
  constructor
  · split
    · omega
    · next hne =>
      have : a.glueCount ≠ 0 := by simpa using hne
      omega
  · refine ⟨hsz, halOff, htop4, htxt, ?_, ?_, hlohi, hhiTop, hhi12, hlo12, ?_⟩ <;> omega

/-- Raw-text byte append (`Ppmd7.c:636-643`):
    Because `ArenaInv` guarantees `text < unitsStart` on entry, `*text++ = sym` writes strictly
    below `unitsStart` (`a.text < a.unitsStart`); and if `a.text + 1 < a.unitsStart`, `ArenaInv`
    continues to hold without restart (otherwise `Ppmd7.c:639` calls `Ppmd7_RestartModel`, which
    re-establishes `ArenaInv` by `restartModel_establishes_arenaInv`). -/
theorem text_append_in_bounds_and_preserves_inv (a : Ppmd7Arena)
    (hinv : ArenaInv a) :
    a.text < a.unitsStart ∧
    (a.text + 1 < a.unitsStart → ArenaInv { a with text := a.text + 1 }) := by
  rcases hinv with ⟨hsz, halOff, htop4, htxt, htxtUs, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩
  refine ⟨htxtUs, fun hlt => ?_⟩
  simp only [ArenaInv]
  exact ⟨hsz, halOff, htop4, by omega, hlt, huslo, hlohi, hhiTop, hhi12, hlo12, hus12⟩

/-- Model of a 12-byte unit's header fields (`Stamp`, `NU`) in `Ppmd7_GlueFreeBlocks` (`Ppmd7.c:162-230`),
    tracking whether `NU` has been initialized. -/
structure UnitHeader where
  stamp : Nat
  nuInit : Bool
  nuVal : Nat
  deriving DecidableEq, Repr

/-- Sentinel written at `p->LoUnit` when `p->LoUnit != p->HiUnit` (`Ppmd7.c:178-179`):
    `((CPpmd7_Node *)(void *)p->LoUnit)->Stamp = 1;` — `NU` is NOT written! -/
def loUnitGuardSentinel : UnitHeader :=
  { stamp := 1, nuInit := false, nuVal := 0 }

/-- Upstream `Ppmd7.c:222-225` coalescing check: reads `node2->NU` BEFORE checking `node2->Stamp != 0`. -/
def glueStepReadsInitializedUpstream (node2 : UnitHeader) : Bool :=
  node2.nuInit -- unconditionally read at line 223 `nu += node2->NU;`

/-- Repaired coalescing check: tests `node2->Stamp != 0` BEFORE reading `node2->NU`. -/
def glueStepReadsInitializedFixed (node2 : UnitHeader) : Bool :=
  if node2.stamp != 0 then true else node2.nuInit

theorem glueFreeBlocks_upstream_reads_uninit_at_loUnitGuard :
    glueStepReadsInitializedUpstream loUnitGuardSentinel = false ∧
    glueStepReadsInitializedFixed loUnitGuardSentinel = true := by
  decide

/-! ### `FreeList`, `Indx2Units` / `Units2Indx`, `SplitBlock`, and `GlueFreeBlocks` Conservation
    (`Ppmd7.c:58-63, 137-147, 208-249`) -/

def PPMD_NUM_INDEXES : Nat := 38

/-- Exact `Indx2Units[i]` mapping constructed by `Ppmd7_Construct` (`Ppmd7.c:58-63`):
    - `i ∈ 0..3`: `1, 2, 3, 4` (step 1)
    - `i ∈ 4..7`: `6, 8, 10, 12` (step 2)
    - `i ∈ 8..11`: `15, 18, 21, 24` (step 3)
    - `i ∈ 12..37`: `28, 32, ..., 128` (step 4). -/
def indx2Units (i : Nat) : Nat :=
  if i < 4 then i + 1
  else if i < 8 then 4 + (i - 3) * 2
  else if i < 12 then 12 + (i - 7) * 3
  else 24 + (i - 11) * 4

/-- Exact `Units2Indx[nu - 1]` ceiling-bucket mapping (`Ppmd7.c:23, 58-63`) for `1 ≤ nu ≤ 128`. -/
def units2Indx (nu : Nat) : Nat :=
  if nu ≤ 4 then nu - 1
  else if nu ≤ 12 then 4 + (nu - 5) / 2
  else if nu ≤ 24 then 8 + (nu - 13) / 3
  else 12 + (nu - 25) / 4

theorem indx2Units_strictMono_and_diff (oldIndx newIndx : Nat)
    (hnewLt : newIndx < oldIndx)
    (holdLt : oldIndx < PPMD_NUM_INDEXES) :
    1 ≤ indx2Units newIndx ∧
    indx2Units newIndx < indx2Units oldIndx ∧
    1 ≤ indx2Units oldIndx - indx2Units newIndx ∧
    indx2Units oldIndx - indx2Units newIndx ≤ 127 := by
  simp only [PPMD_NUM_INDEXES, indx2Units] at *
  by_cases h1 : oldIndx < 4 <;> by_cases h2 : oldIndx < 8 <;> by_cases h3 : oldIndx < 12 <;>
    by_cases n1 : newIndx < 4 <;> by_cases n2 : newIndx < 8 <;> by_cases n3 : newIndx < 12 <;>
    simp only [h1, h2, h3, n1, n2, n3, ↓reduceIte] <;> omega

theorem units2Indx_split_exact (nu : Nat) (hlo : 1 ≤ nu) (hhi : nu ≤ 127) :
    let i0 := units2Indx nu
    i0 < PPMD_NUM_INDEXES ∧
    (if indx2Units i0 = nu then True
     else
      1 ≤ i0 ∧
      let k := indx2Units (i0 - 1)
      k < nu ∧
      let remIdx := nu - k - 1
      remIdx < PPMD_NUM_INDEXES ∧
      k + indx2Units remIdx = nu) := by
  dsimp only
  by_cases c1 : nu ≤ 4
  · have hi0 : units2Indx nu = nu - 1 := by simp [units2Indx, c1]
    rw [hi0]
    have hlt4 : nu - 1 < 4 := by omega
    have hval : indx2Units (nu - 1) = nu := by simp [indx2Units, hlt4]; omega
    simp [PPMD_NUM_INDEXES, hval]
    omega
  · by_cases c2 : nu ≤ 12
    · have hi0 : units2Indx nu = 4 + (nu - 5) / 2 := by simp [units2Indx, c1, c2]
      rw [hi0]
      have hge4 : ¬ (4 + (nu - 5) / 2 < 4) := by omega
      have hlt8 : 4 + (nu - 5) / 2 < 8 := by omega
      have hval : indx2Units (4 + (nu - 5) / 2) = 4 + (4 + (nu - 5) / 2 - 3) * 2 := by
        simp [indx2Units, hge4, hlt8]
      rw [hval]
      by_cases heq : 4 + (4 + (nu - 5) / 2 - 3) * 2 = nu
      · simp [PPMD_NUM_INDEXES, heq]; omega
      · simp only [PPMD_NUM_INDEXES, heq, ↓reduceIte]
        have hprev : indx2Units (4 + (nu - 5) / 2 - 1) = nu - 1 := by
          unfold indx2Units
          split <;> (try split) <;> (try split) <;> omega
        rw [hprev]
        have hrem0 : nu - (nu - 1) - 1 = 0 := by omega
        rw [hrem0]
        simp [indx2Units]
        omega
    · by_cases c3 : nu ≤ 24
      · have hi0 : units2Indx nu = 8 + (nu - 13) / 3 := by simp [units2Indx, c1, c2, c3]
        rw [hi0]
        have hge4 : ¬ (8 + (nu - 13) / 3 < 4) := by omega
        have hge8 : ¬ (8 + (nu - 13) / 3 < 8) := by omega
        have hlt12 : 8 + (nu - 13) / 3 < 12 := by omega
        have hval : indx2Units (8 + (nu - 13) / 3) = 12 + (8 + (nu - 13) / 3 - 7) * 3 := by
          simp [indx2Units, hge4, hge8, hlt12]
        rw [hval]
        by_cases heq : 12 + (8 + (nu - 13) / 3 - 7) * 3 = nu
        · simp [PPMD_NUM_INDEXES, heq]; omega
        · simp only [PPMD_NUM_INDEXES, heq, ↓reduceIte]
          have hprev : indx2Units (8 + (nu - 13) / 3 - 1) = 12 + ((nu - 13) / 3) * 3 := by
            unfold indx2Units
            split <;> (try split) <;> (try split) <;> omega
          rw [hprev]
          have hremLt : nu - (12 + ((nu - 13) / 3) * 3) - 1 < 4 := by omega
          simp [indx2Units, hremLt]
          omega
      · have hi0 : units2Indx nu = 12 + (nu - 25) / 4 := by simp [units2Indx, c1, c2, c3]
        rw [hi0]
        have hge4 : ¬ (12 + (nu - 25) / 4 < 4) := by omega
        have hge8 : ¬ (12 + (nu - 25) / 4 < 8) := by omega
        have hge12 : ¬ (12 + (nu - 25) / 4 < 12) := by omega
        have hval : indx2Units (12 + (nu - 25) / 4) = 24 + (12 + (nu - 25) / 4 - 11) * 4 := by
          simp [indx2Units, hge4, hge8, hge12]
        rw [hval]
        by_cases heq : 24 + (12 + (nu - 25) / 4 - 11) * 4 = nu
        · simp [PPMD_NUM_INDEXES, heq]; omega
        · simp only [PPMD_NUM_INDEXES, heq, ↓reduceIte]
          have hprev : indx2Units (12 + (nu - 25) / 4 - 1) = 24 + ((nu - 25) / 4) * 4 := by
            unfold indx2Units
            split <;> (try split) <;> (try split) <;> omega
          rw [hprev]
          have hremLt : nu - (24 + ((nu - 25) / 4) * 4) - 1 < 4 := by omega
          simp [indx2Units, hremLt]
          omega

/-- Theorem (`Ppmd7_SplitBlock` Exact Unit Conservation & `FreeList` Index Bounds, `Ppmd7.c:137-147`):
    Whenever a free block of bucket `oldIndx` is split to satisfy an allocation of bucket `newIndx`
    (`newIndx < oldIndx < 38`), the remainder `nu = I2U(oldIndx) - I2U(newIndx)` (`1 ≤ nu ≤ 127`)
    either:
    1. Matches a single bucket `i = U2I(nu) < 38` with `I2U(i) = nu`, OR
    2. Splits into TWO valid buckets `i - 1 < 38` (size `k = I2U(i - 1)`) and `remIdx = nu - k - 1 < 3`
       (size `I2U(remIdx) = nu - k`), such that `I2U(newIndx) + k + I2U(remIdx) = I2U(oldIndx)`
       with zero leaked or overlapping units! -/
theorem ppmd7_splitBlock_conserves_units_and_bounds (oldIndx newIndx : Nat)
    (hnewLt : newIndx < oldIndx)
    (holdLt : oldIndx < PPMD_NUM_INDEXES) :
    let nu := indx2Units oldIndx - indx2Units newIndx
    let i0 := units2Indx nu
    1 ≤ nu ∧ nu ≤ 127 ∧ i0 < PPMD_NUM_INDEXES ∧
    (if indx2Units i0 = nu then
      indx2Units newIndx + indx2Units i0 = indx2Units oldIndx
     else
      1 ≤ i0 ∧
      let k := indx2Units (i0 - 1)
      k < nu ∧
      let remIdx := nu - k - 1
      remIdx < PPMD_NUM_INDEXES ∧
      indx2Units newIndx + k + indx2Units remIdx = indx2Units oldIndx) := by
  rcases indx2Units_strictMono_and_diff oldIndx newIndx hnewLt holdLt with
    ⟨_, hltU, hnuLo, hnuHi⟩
  dsimp only
  rcases units2Indx_split_exact (indx2Units oldIndx - indx2Units newIndx) hnuLo hnuHi with
    ⟨hi0Lt, hsplit⟩
  refine ⟨hnuLo, hnuHi, hi0Lt, ?_⟩
  by_cases heq : indx2Units (units2Indx (indx2Units oldIndx - indx2Units newIndx)) =
      indx2Units oldIndx - indx2Units newIndx
  · simp only [heq, ↓reduceIte]
    omega
  · simp only [heq, ↓reduceIte] at hsplit ⊢
    rcases hsplit with ⟨hi0Pos, hkLt, hremLt, hsum⟩
    exact ⟨hi0Pos, hkLt, hremLt, by omega⟩

/-- Theorem (`Ppmd7_GlueFreeBlocks` Coalescing `UInt16` Bound & Conservation, `Ppmd7.c:220-228`):
    When coalescing adjacent free blocks of sizes `nu1 ≥ 1` and `nu2 ≥ 1`, checking
    `!(nu1 + nu2 ≥ 0x10000)` before `node->NU = (UInt16)(nu1 + nu2)` guarantees that the merged
    unit count fits in 16-bit `UInt16` (`< 65536`) without truncation and preserves total units. -/
theorem ppmd7_glue_merge_no_u16_overflow (nu1 nu2 : Nat)
    (h1 : 1 ≤ nu1) (h2 : 1 ≤ nu2)
    (hguard : ¬ (nu1 + nu2 ≥ 0x10000)) :
    (nu1 + nu2) % 65536 = nu1 + nu2 ∧ 2 ≤ nu1 + nu2 := by
  omega

/-- Range decoder `RC_GetThreshold` safety in `Ppmd7Dec.c:53, 78, 233`:
    Unlike `Ppmd7aDec.c` (where carryless `kBot = 2^15` allows `Range` down to `1`, requiring
    `if (summFreq > R->Range)`), `Ppmd7Dec.c` maintains `Range ≥ 2^24` (`16,777,216`).
    For every `1 ≤ total < 2^16` (`SummFreq` is `UInt16`, and `freqSum ≤ 39,811`),
    `Range / total ≥ 256 > 0` (no division by zero!) and at most two `<< 8` shifts (`RC_NORM`)
    restore `Range' ≥ 2^24` for any `1 ≤ symFreq`. -/
def ppmd7zNormTwo (range : Nat) : Nat :=
  let r1 := if range < (1 <<< 24) then range * 256 else range
  if r1 < (1 <<< 24) then r1 * 256 else r1

theorem ppmd7z_rc_no_div_by_zero_and_renorm (range total symFreq : Nat)
    (hrange : (1 <<< 24) ≤ range)
    (htotalPos : 1 ≤ total)
    (htotalHi : total < (1 <<< 16))
    (hsymPos : 1 ≤ symFreq) :
    256 ≤ range / total ∧
    range / total ≠ 0 ∧
    (1 <<< 24) ≤ ppmd7zNormTwo ((range / total) * symFreq) := by
  simp only [ppmd7zNormTwo, Nat.shiftLeft_eq] at *
  have hdiv : 256 ≤ range / total := by
    have hmul : 256 * total ≤ 16777216 := by omega
    have hle : 256 * total ≤ range := by omega
    exact (Nat.le_div_iff_mul_le htotalPos).mpr hle
  have hprod : 256 ≤ (range / total) * symFreq := by
    have h1 : 256 * 1 ≤ (range / total) * 1 := Nat.mul_le_mul_right 1 hdiv
    have h2 : (range / total) * 1 ≤ (range / total) * symFreq :=
      Nat.mul_le_mul_left (range / total) hsymPos
    omega
  refine ⟨hdiv, by omega, ?_⟩
  split
  · split <;> omega
  · omega

/-- `Ppmd7_CreateSuccessors` (`Ppmd7.c:518-527`) division-by-zero freedom & `BinSumm` frequency bound:
    In any multi-symbol context (`numStats ≥ 2`) where every symbol has `1 ≤ freq ≤ 124` (`MAX_FREQ`)
    and `escapeFreq ≥ 1` (`summFreq ≥ numStats + (freq - 1) + 1`), `s0 ≥ 1` (`2 * s0 ≥ 2 > 0`)
    and the computed `newFreq` satisfies `1 ≤ newFreq ≤ 125 ≤ 128`, keeping `BinSumm[newFreq - 1]`
    strictly within `[0, 127]`. -/
theorem ppmd7_createSuccessors_freq_safe (freq numStats summFreq : Nat)
    (hfreqLo : 1 ≤ freq) (hfreqHi : freq ≤ 124)
    (_hns : 2 ≤ numStats)
    (hesc : numStats + (freq - 1) + 1 ≤ summFreq) :
    let cf := freq - 1
    let s0 := summFreq - numStats - cf
    0 < 2 * s0 ∧
    let newFreq :=
      1 + (if 2 * cf ≤ s0 then (if 5 * cf > s0 then 1 else 0)
           else (2 * cf + s0 - 1) / (2 * s0) + 1)
    1 ≤ newFreq ∧ newFreq ≤ 125 ∧ newFreq - 1 < 128 := by
  dsimp only
  generalize hcf : freq - 1 = cf
  generalize hs0Eq : summFreq - numStats - cf = s0
  have hs0 : 1 ≤ s0 := by omega
  have hcfHi : cf ≤ 123 := by omega
  refine ⟨by omega, ?_⟩
  split
  · split <;> omega
  · have hdivHi : (2 * cf + s0 - 1) / (2 * s0) ≤ cf := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      have hmul : 1 * cf ≤ s0 * cf := Nat.mul_le_mul_right cf hs0
      have hcomm : (2 * s0) * cf = 2 * (s0 * cf) := by
        rw [Nat.mul_assoc]
      omega
    generalize (2 * cf + s0 - 1) / (2 * s0) = q at hdivHi ⊢
    omega

/-- Second dimension of `BinSumm[128][64]` (`Ppmd7.h:128-133`) is always `< 64`. -/
theorem ppmd7_binSumm_col_in_bounds (prevSuccess runBit ns2bs hi4 hi3 : Nat)
    (hps : prevSuccess ≤ 1)
    (hrb : runBit = 0 ∨ runBit = 0x20)
    (hns : ns2bs = 0 ∨ ns2bs = 2 ∨ ns2bs = 4 ∨ ns2bs = 6)
    (h4 : hi4 = 0 ∨ hi4 = 16)
    (h3 : hi3 = 0 ∨ hi3 = 8) :
    prevSuccess + runBit + ns2bs + hi4 + hi3 < 64 := by
  omega

/-- Signed `Int32` `RunLength` overflow (`Ppmd7Dec.c:159`, `Ppmd7.c:995`, `Ppmd7.h:78`):
    Starting from `InitRL = -13` (`MaxOrder ≥ 12`), decoding `2^31 + 13` consecutive symbols
    in a single-state max-order context increments `RunLength` to `2^31 > INT32_MAX` (`2^31 - 1`),
    triggering C11 §6.5p5 signed 32-bit integer overflow UB! -/
def int32Max : Int := 2147483647

theorem ppmd7_runLength_overflows_int32 :
    let initRL : Int := -13
    let steps : Nat := 2147483661 -- 2^31 + 13 (~2.0 GiB of repeated bytes)
    initRL + (steps : Int) > int32Max := by
  simp [int32Max]

end Ppmd7

/-!
## 5. LZMA & LZMA2 Decoders (`C/LzmaDec.h`, `C/LzmaDec.c`, `C/Lzma2Dec.h`, `C/Lzma2Dec.c`)

Models and proves:
1. **Probability table sizing (`1984 + (0x300 << (lc + lp))`), `probs_1664 + SpecPos` non-negativity,
   and literal subcoder index bounds (`LzmaDec.c:129-165, 267-317, 1290-1298`).**
2. **Circular dictionary index bounds (`LzmaDec.c:269, 291, 350, 567, 648`):**
   Under `LzmaDicInv`, both `(dicPos == 0 ? dicBufSize : dicPos) - 1` and
   `dicPos - rep0 + (dicPos < rep0 ? dicBufSize : 0)` lie strictly inside `[0, dicBufSize)`.
3. **Fast-loop lookahead margin (`LZMA_REQUIRED_INPUT_MAX = 20`, `LzmaDec.c:1086`):**
   When `inSize ≥ 20` and `bufLimit = inSize - 20`, any iteration starting at `buf < bufLimit`
   consuming `≤ 20` bytes stays strictly within `[0, inSize]`.
4. **LZMA2 chunk state machine invariants (`Lzma2Dec.c:97-304`):**
   - `state = .control → unpackSize = 0`: essential because `LZMA2_STATE_UNPACK0`/`UNPACK1`
     use bitwise `|=` (`Lzma2Dec.c:125, 129`) without clearing `unpackSize` on uncompressed
     chunks (`control ∈ {1, 2}`);
   - `needInitLevel` monotonicity (`0xE0 → 0xC0 → 0`): guarantees `prop` and `probs` are always
     initialized before `LZMA_DECODE_REAL` can execute.
-/
namespace Lzma

def NUM_BASE_PROBS : Nat := 1984
def LZMA_LIT_SIZE : Nat := 0x300
def LZMA_DIC_MIN : Nat := 1 <<< 12
def LZMA_REQUIRED_INPUT_MAX : Nat := 20

structure LzmaProps where
  lc : Nat
  lp : Nat
  pb : Nat
  dicSize : Nat
  deriving DecidableEq, Repr

def LzmaPropsValid (p : LzmaProps) : Prop :=
  p.lc ≤ 8 ∧ p.lp ≤ 4 ∧ p.pb ≤ 4 ∧ LZMA_DIC_MIN ≤ p.dicSize ∧ p.dicSize < (1 <<< 32)

def numProbs (p : LzmaProps) : Nat :=
  NUM_BASE_PROBS + (LZMA_LIT_SIZE <<< (p.lc + p.lp))

/-- Theorem (`LzmaDec.c:1290-1298`):
    For all valid `(lc, lp)` (`lc ≤ 8, lp ≤ 4`), `2752 ≤ numProbs ≤ 3,147,712`, so
    `numProbs * sizeof(CLzmaProb)` (`≤ 12,590,848` bytes) never overflows 32-bit `UInt32` or `SizeT`,
    and `probs_1664 = probs + 1664` lies strictly inside `probs[0 .. numProbs]` with
    `1664 + SpecPos = 0` (`SpecPos = -1664`). -/
theorem lzma_numProbs_bounds (p : LzmaProps) (hv : LzmaPropsValid p) :
    1664 < numProbs p ∧
    2752 ≤ numProbs p ∧
    numProbs p ≤ 3147712 ∧
    numProbs p * 4 < (1 <<< 32) := by
  rcases hv with ⟨hlc, hlp, _, _, _⟩
  simp only [numProbs, NUM_BASE_PROBS, LZMA_LIT_SIZE, Nat.shiftLeft_eq]
  have hsum : p.lc + p.lp ≤ 12 := by omega
  have hpowLo : 1 ≤ 2 ^ (p.lc + p.lp) := Nat.one_le_pow (p.lc + p.lp) 2 (by omega)
  have hpowHi : 2 ^ (p.lc + p.lp) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) hsum
  omega

/-- Theorem (`LzmaDec.c:64, 267-317, 738-766` Literal Probability Subtable Bounds):
    For any context index `ctxIdx < 2^(lc + lp)`, match-literal state `offs + bit ≤ 0x200`,
    and tree symbol `1 ≤ symbol < 0x100`, the accessed index `1984 + 0x300 * ctxIdx + offs + bit + symbol`
    is strictly `< numProbs p`. -/
theorem lzma_lit_prob_index_in_bounds (p : LzmaProps) (ctxIdx offsBit symbol : Nat)
    (hctx : ctxIdx < (1 <<< (p.lc + p.lp)))
    (hob : offsBit ≤ 0x200)
    (hsym : symbol < 0x100) :
    NUM_BASE_PROBS + LZMA_LIT_SIZE * ctxIdx + offsBit + symbol < numProbs p := by
  simp only [numProbs, NUM_BASE_PROBS, LZMA_LIT_SIZE, Nat.shiftLeft_eq] at *
  omega

/-- Circular dictionary safety invariant for `CLzmaDec` (`LzmaDec.c:268, 291, 539, 567, 688`):
    - Either stream is at the very beginning (`processedPos = 0 ∧ checkDicSize = 0 ∧ dicPos ≤ dicBufSize`),
      OR at least 1 byte has been produced (`0 < dicBufSize ∧ dicPos ≤ dicBufSize`) and every
      active repeat distance `rep0` satisfies `1 ≤ rep0 ≤ activeWindow ≤ dicBufSize`. -/
def LzmaDicWindowInv (dicBufSize dicPos processedPos checkDicSize rep0 : Nat) : Prop :=
  0 < dicBufSize ∧
  dicPos < dicBufSize ∧
  checkDicSize ≤ dicBufSize ∧
  (checkDicSize = 0 → processedPos ≤ dicPos) ∧
  1 ≤ rep0 ∧
  rep0 ≤ (if checkDicSize = 0 then processedPos else checkDicSize)

/-- Theorem (`LzmaDec.c:269, 291, 350, 567, 648` Circular Dictionary Index Bounds):
    Under `LzmaDicWindowInv` (when `processedPos ≠ 0 ∨ checkDicSize ≠ 0`), BOTH:
    1. `prevIdx = (dicPos == 0 ? dicBufSize : dicPos) - 1` (previous byte for literal context), and
    2. `matchIdx = if dicPos < rep0 then dicPos + dicBufSize - rep0 else dicPos - rep0` (match source)
    lie strictly inside `[0, dicBufSize)`. -/
theorem lzma_circular_dic_indices_in_bounds
    (dicBufSize dicPos processedPos checkDicSize rep0 : Nat)
    (hinv : LzmaDicWindowInv dicBufSize dicPos processedPos checkDicSize rep0) :
    let prevIdx := (if dicPos = 0 then dicBufSize else dicPos) - 1
    let matchIdx := if dicPos < rep0 then dicPos + dicBufSize - rep0 else dicPos - rep0
    prevIdx < dicBufSize ∧ matchIdx < dicBufSize := by
  rcases hinv with ⟨hbufPos, hdicLt, hchkLe, hprocLe, hrepLo, hrepHi⟩
  dsimp only
  constructor
  · split <;> omega
  · by_cases hchk : checkDicSize = 0
    · simp [hchk] at hrepHi
      have h1 := hprocLe hchk
      split <;> omega
    · simp [hchk] at hrepHi
      split <;> omega

/-- Theorem (`LzmaDec.c:1086` Fast-Loop Lookahead Margin):
    When `LZMA_REQUIRED_INPUT_MAX ≤ inSize` and `bufLimit = inSize - LZMA_REQUIRED_INPUT_MAX`,
    any fast-loop symbol decode starting at `buf < bufLimit` that consumes `stepBytes ≤ 20` bytes
    (at most 22 probability decisions + 26 direct bits < 160 bits = 20 bytes) satisfies
    `buf + stepBytes < inSize`, never reading past `src + inSize`. -/
theorem lzma_fast_loop_lookahead_in_bounds (inSize buf stepBytes : Nat)
    (hin : LZMA_REQUIRED_INPUT_MAX ≤ inSize)
    (hbuf : buf < inSize - LZMA_REQUIRED_INPUT_MAX)
    (hstep : stepBytes ≤ LZMA_REQUIRED_INPUT_MAX) :
    buf + stepBytes < inSize := by
  simp only [LZMA_REQUIRED_INPUT_MAX] at *
  omega

/-! ### `CLzma2Dec` Header & Chunk State Machine (`Lzma2Dec.c:43-304`) -/

inductive Lzma2Phase where
  | control
  | unpack0
  | unpack1
  | pack0
  | pack1
  | prop
  | data
  | dataCont
  | finished
  | error
  deriving DecidableEq, Repr

structure Lzma2HeaderState where
  phase : Lzma2Phase
  control : UInt8
  needInitLevel : UInt8
  unpackSize : Nat
  packSize : Nat
  dicInitialized : Bool
  stateAndPropsInitialized : Bool
  deriving DecidableEq, Repr

def lzma2InitState : Lzma2HeaderState :=
  { phase := .control
    control := 0
    needInitLevel := 0xE0
    unpackSize := 0
    packSize := 0
    dicInitialized := false
    stateAndPropsInitialized := false }

/-- Crucial `CLzma2Dec` invariant (`Lzma2Dec.c:86-164`):
    1. `phase = .control → unpackSize = 0` (required because `LZMA2_STATE_UNPACK0`/`UNPACK1`
       use `|=` without clearing `unpackSize` when `(control & 0x80) == 0`!).
    2. `needInitLevel` tracks uninitialized decoder components:
       - `0xE0`: neither dictionary nor LZMA probs/props initialized;
       - `0xC0`: dictionary initialized (e.g., via `0x01` uncompressed reset), LZMA probs/props NOT yet initialized;
       - `0x00`: both dictionary and LZMA probs/props initialized. -/
def Lzma2StateInv (s : Lzma2HeaderState) : Prop :=
  (s.phase = .control → s.unpackSize = 0) ∧
  (s.needInitLevel = 0xE0 ∨
   (s.needInitLevel = 0xC0 ∧ s.dicInitialized = true) ∨
   (s.needInitLevel = 0 ∧ s.dicInitialized = true ∧ s.stateAndPropsInitialized = true))

theorem lzma2Init_establishes_inv : Lzma2StateInv lzma2InitState := by
  simp [Lzma2StateInv, lzma2InitState]

/-- Models `Lzma2Dec_UpdateState` on `LZMA2_STATE_CONTROL` (`Lzma2Dec.c:101-122`) together with
    the initialization flags triggered upon reaching `LZMA2_STATE_DATA`. -/
def lzma2StepControl (s : Lzma2HeaderState) (b : UInt8) : Lzma2HeaderState :=
  if b == 0 then
    { s with control := b, phase := .finished }
  else if (b &&& 0x80) == 0 then
    if b == 1 then
      { s with
        control := b
        needInitLevel := 0xC0
        dicInitialized := true
        phase := .unpack0 }
    else if b > 2 || s.needInitLevel == 0xE0 then
      { s with control := b, phase := .error }
    else
      { s with control := b, phase := .unpack0 }
  else if b < s.needInitLevel then
    { s with control := b, phase := .error }
  else
    { s with
      control := b
      needInitLevel := 0
      unpackSize := (b &&& 0x1F).toNat <<< 16
      dicInitialized := if b ≥ 0xE0 then true else s.dicInitialized
      stateAndPropsInitialized := if b ≥ 0xC0 then true else s.stateAndPropsInitialized
      phase := .unpack0 }

/-- Theorem (`Lzma2Dec_UpdateState` Guards Uninitialized Dictionary & Probs/Props, `Lzma2Dec.c:108-122`):
    Starting from any state in `.control` satisfying `Lzma2StateInv`:
    1. `lzma2StepControl` preserves `Lzma2StateInv`;
    2. If `lzma2StepControl` transitions to `.unpack0` for an uncompressed chunk (`b < 0x80`),
       `unpackSize` is guaranteed to be `0` (so `|=` in `.unpack0`/`.unpack1` computes the exact
       16-bit uncompressed length without stale high bits!) and `dicInitialized = true`;
    3. If `lzma2StepControl` transitions to `.unpack0` for an LZMA chunk (`b ≥ 0x80`),
       BOTH `dicInitialized = true` AND `stateAndPropsInitialized = true` hold! -/
theorem lzma2StepControl_preserves_and_guards (s : Lzma2HeaderState) (b : UInt8)
    (hctrl : s.phase = .control)
    (hinv : Lzma2StateInv s) :
    let s' := lzma2StepControl s b
    Lzma2StateInv s' ∧
    (s'.phase = .unpack0 ∧ (b &&& 0x80) = 0 →
      s'.unpackSize = 0 ∧ s'.dicInitialized = true) ∧
    (s'.phase = .unpack0 ∧ (b &&& 0x80) ≠ 0 →
      s'.dicInitialized = true ∧ s'.stateAndPropsInitialized = true) := by
  rcases hinv with ⟨hunp0, hlevel⟩
  have husZero : s.unpackSize = 0 := hunp0 hctrl
  dsimp only [lzma2StepControl]
  by_cases hb0 : (b == 0) = true
  · simp [hb0, Lzma2StateInv, hlevel]
  · simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    by_cases hunc : ((b &&& 0x80) == 0) = true
    · have huncEq : b &&& 0x80 = 0 := by simpa using hunc
      simp only [huncEq, beq_self_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, and_false,
                 false_implies, and_true]
      by_cases hb1 : (b == 1) = true
      · simp [hb1, Lzma2StateInv, husZero]
      · simp only [hb1, Bool.false_eq_true, ↓reduceIte]
        by_cases herr : (b > 2 || s.needInitLevel == 0xE0) = true
        · simp [herr, Lzma2StateInv, hlevel]
        · simp only [herr, Bool.false_eq_true, ↓reduceIte]
          have hnotE0 : s.needInitLevel ≠ 0xE0 := by
            intro heq
            simp [heq] at herr
          rcases hlevel with he0 | ⟨hc0, hdic⟩ | ⟨hz, hdic, hsp⟩
          · exact absurd he0 hnotE0
          · simp [Lzma2StateInv, hc0, hdic, husZero]
          · simp [Lzma2StateInv, hz, hdic, hsp, husZero]
    · have huncNe : b &&& 0x80 ≠ 0 := by
        intro heq
        simp [heq] at hunc
      simp only [hunc, Bool.false_eq_true, ↓reduceIte, huncNe, not_false_eq_true, and_false,
                 false_implies, true_and, ne_eq]
      by_cases hlt : b < s.needInitLevel
      · simp [hlt, Lzma2StateInv, hlevel]
      · simp only [hlt, ↓reduceIte]
        have hge : s.needInitLevel ≤ b :=
          Nat.not_lt.mp (by simpa [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] using hlt)
        rcases hlevel with he0 | ⟨hc0, hdic⟩ | ⟨hz, hdic, hsp⟩
        · have hbE0 : (0xE0 : UInt8) ≤ b := by rw [← he0]; exact hge
          have hbC0 : (0xC0 : UInt8) ≤ b := by
            have : (0xC0 : Nat) ≤ b.toNat := by
              have : (0xE0 : Nat) ≤ b.toNat := hbE0
              omega
            exact this
          simp [Lzma2StateInv, hbE0, hbC0]
        · have hbC0 : (0xC0 : UInt8) ≤ b := by rw [← hc0]; exact hge
          by_cases hbE0 : (0xE0 : UInt8) ≤ b
          · simp [Lzma2StateInv, hbE0, hbC0]
          · simp [Lzma2StateInv, hbE0, hbC0, hdic]
        · by_cases hbE0 : (0xE0 : UInt8) ≤ b
          · have hbC0 : (0xC0 : UInt8) ≤ b := by
              have : (0xE0 : Nat) ≤ b.toNat := hbE0
              exact (by omega : (0xC0 : Nat) ≤ b.toNat)
            simp [Lzma2StateInv, hbE0, hbC0]
          · by_cases hbC0 : (0xC0 : UInt8) ≤ b
            · simp [Lzma2StateInv, hbE0, hbC0, hdic]
            · simp [Lzma2StateInv, hbE0, hbC0, hdic, hsp]

end Lzma

end SevenZipF.Model
