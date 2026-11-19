import ZlibNgF.Spec.Common.Inflate

/-!
# Safety goals of the inflate side (`ZlibNgF`)

`inflate.c` (with `inftrees.c`, `inffast_tpl.h`, `chunkset_tpl.h`) and `uncompr.c`. Each goal says that the call
does not fault (no undefined behaviour, and it returns) for every stream the function accepts
(`InflateHandle`: `Z_NULL`, a stream with no state, or a reachable stream) and valid caller buffers, and that it
changes only what the frame names: the stream record, the library's own block, the registered header record, and
the caller buffers the function writes. That a successful call keeps the stream reachable is part of
`InflateReachable` itself; the content of the goals is that no reachable state lets a call fault. The narrowings
are in the module comment of `ZlibNgF.Spec.Common.Inflate` and on the deviations page.

None of these goals is proved yet.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Safety
open ZlibNgF.Spec C

/-! ## Initialisation -/

/-- `int inflateInit_(z_stream *strm, const char *version, int stream_size)`: for a `Z_NULL` stream or a live
`z_stream` with the default allocator, a `NULL` or readable `version` and any `stream_size`, does not fault and
changes only the stream record and fresh blocks. -/
def Goal.inflateInit__safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (version : BPtr) (size : Int32),
    CrcGlobals h → InitReady h s → VersionOk h version →
    ∃ r h', C.run (ZlibNg.Inflate.inflateInit_ s version size) h = .ok (r, h') ∧
      Frame h h' (streamIds s) [] [] []

/-- `int inflateInit2_(z_stream *strm, int windowBits, const char *version, int stream_size)`: as `inflateInit_`,
for every `windowBits`. -/
def Goal.inflateInit2__safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (windowBits : Int32) (version : BPtr) (size : Int32),
    CrcGlobals h → InitReady h s → VersionOk h version →
    ∃ r h', C.run (ZlibNg.Inflate.inflateInit2_ s windowBits version size) h = .ok (r, h') ∧
      Frame h h' (streamIds s) [] [] []

/-- Non-vacuity of `InflateReachable`: `inflateInit_` on a fresh zero `z_stream` (as `uncompress` makes it) with
the library's version string succeeds, so reachable streams exist. -/
def Goal.inflateInit_nonvacuous : Prop :=
  ∃ h h' s, CrcGlobals h ∧ InitReady h s ∧
    C.run (do let v ← strLitRef "1.3.2.zlib-ng"; ZlibNg.Inflate.inflateInit_ s v 112) h =
      .ok (ZlibNg.Inflate.Z_OK, h') ∧
    InflateReachable h' s

/-! ## Decompression -/

/-- `int inflate(z_stream *strm, int flush)`: for every accepted stream with valid, disjoint buffers and every
`flush`, does not fault and writes only the output buffer, the registered header's buffers, the stream record,
the header record and the library's block. -/
def Goal.inflate_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (flush : Int32),
    CrcGlobals h → InflateHandle h s → (InflateReachable h s → StreamIO h s) →
    ∃ r h', C.run (ZlibNg.Inflate.inflate s flush) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) (headerIds h s) (outputRanges h s)

/-- Non-vacuity of `inflate_safety`: a reachable stream with valid buffers on which one `inflate(Z_FINISH)` decodes
a whole zlib stream and returns `Z_STREAM_END`. -/
def Goal.inflate_nonvacuous : Prop :=
  ∃ h s h', CrcGlobals h ∧ InflateReachable h s ∧ StreamIO h s ∧
    C.run (ZlibNg.Inflate.inflate s 4) h = .ok (ZlibNg.Inflate.Z_STREAM_END, h')

/-- `int inflateEnd(z_stream *strm)`: does not fault and frees only the stream's state block. -/
def Goal.inflateEnd_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflateEnd s) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateSync(z_stream *strm)`: for every accepted stream with valid buffers (a `NULL` `next_in` only with
`avail_in == 0`), does not fault and changes only the stream record and the library's block. -/
def Goal.inflateSync_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s → (InflateReachable h s → StreamIO h s ∧ SyncInput h s) →
    ∃ r h', C.run (ZlibNg.Inflate.inflateSync s) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateSyncPoint(z_stream *strm)`: does not fault and changes nothing. -/
def Goal.inflateSyncPoint_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r, C.run (ZlibNg.Inflate.inflateSyncPoint s) h = .ok (r, h)

/-! ## Dictionaries and headers -/

/-- `int inflateSetDictionary(z_stream *strm, const Bytef *dictionary, uInt dictLength)`: for a `NULL` or readable
dictionary of `dictLength` bytes outside the library's block, does not fault and changes only the stream record and
the library's block. -/
def Goal.inflateSetDictionary_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (d : BPtr) (n : UInt32),
    CrcGlobals h → InflateHandle h s → NullOrRead h d n.toNat → (∀ b, StateBlock h s b → NotInBlock b d) →
    ∃ r h', C.run (ZlibNg.Inflate.inflateSetDictionary s d n) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateGetDictionary(z_stream *strm, Bytef *dictionary, uInt *dictLength)`: for a `NULL` dictionary or one
of at least 32768 writable bytes outside the library's block, with or without a length cell, does not fault and
writes only the dictionary buffer. -/
def Goal.inflateGetDictionary_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (d : BPtr) (hasLen : Bool),
    CrcGlobals h → InflateHandle h s → NullOrWrite h d 32768 → (∀ b, StateBlock h s b → NotInBlock b d) →
    ∃ r h', C.run (ZlibNg.Inflate.inflateGetDictionary s d hasLen) h = .ok (r, h') ∧
      Frame h h' [] [] [] [(d, 32768)]

/-- `int inflateGetHeader(z_stream *strm, gz_headerp head)`: for a `Z_NULL` or valid header, does not fault and
changes only the library's block and the header record. -/
def Goal.inflateGetHeader_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (hp : HeaderPtr),
    CrcGlobals h → InflateHandle h s → HeaderOk h hp →
    ∃ r h', C.run (ZlibNg.Inflate.inflateGetHeader s hp) h = .ok (r, h') ∧
      Frame h h' [] (stateIds h s) (match hp with | none => [] | some k => [k]) []

/-! ## Control -/

/-- `int inflatePrime(z_stream *strm, int bits, int value)`: for every `bits` and `value`, does not fault and
changes only the library's block. -/
def Goal.inflatePrime_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (bits value : Int32),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflatePrime s bits value) h = .ok (r, h') ∧
      Frame h h' [] (stateIds h s) [] []

/-- `int inflateReset(z_stream *strm)`: does not fault and changes only the stream record and the library's
block. -/
def Goal.inflateReset_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflateReset s) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateResetKeep(z_stream *strm)`: as `inflateReset`. -/
def Goal.inflateResetKeep_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflateResetKeep s) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateReset2(z_stream *strm, int windowBits)`: as `inflateReset`, for every `windowBits`. -/
def Goal.inflateReset2_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (windowBits : Int32),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflateReset2 s windowBits) h = .ok (r, h') ∧
      Frame h h' (streamIds s) (stateIds h s) [] []

/-- `int inflateValidate(z_stream *strm, int check)`: does not fault and changes only the library's block. -/
def Goal.inflateValidate_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (check : Int32),
    CrcGlobals h → InflateHandle h s →
    ∃ r h', C.run (ZlibNg.Inflate.inflateValidate s check) h = .ok (r, h') ∧
      Frame h h' [] (stateIds h s) [] []

/-- `int inflateUndermine(z_stream *strm, int subvert)`: does not fault and changes nothing. -/
def Goal.inflateUndermine_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (subvert : Int32),
    CrcGlobals h → InflateHandle h s →
    ∃ r, C.run (ZlibNg.Inflate.inflateUndermine s subvert) h = .ok (r, h)

/-- `long inflateMark(z_stream *strm)`: does not fault and changes nothing. -/
def Goal.inflateMark_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r, C.run (ZlibNg.Inflate.inflateMark s) h = .ok (r, h)

/-- `unsigned long inflateCodesUsed(z_stream *strm)`: does not fault and changes nothing. -/
def Goal.inflateCodesUsed_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    CrcGlobals h → InflateHandle h s →
    ∃ r, C.run (ZlibNg.Inflate.inflateCodesUsed s) h = .ok (r, h)

/-- `int inflateCopy(z_stream *dest, z_stream *source)`: for an accepted source and a distinct destination ready
for initialisation, does not fault and changes only the destination record and fresh blocks. -/
def Goal.inflateCopy_safety : Prop :=
  ∀ (h : Heap) (dst src : StreamPtr),
    CrcGlobals h → InflateHandle h src → InitReady h dst → dst ≠ src →
    ∃ r h', C.run (ZlibNg.Inflate.inflateCopy dst src) h = .ok (r, h') ∧
      Frame h h' (streamIds dst) [] [] []

/-! ## One-shot decompression (`uncompr.c`)

The length cells are values (`none`: a `NULL` cell). The destination is `NULL` or has `*destLen` writable bytes, the
source is `NULL` or has `*sourceLen` readable bytes, and the two do not overlap. -/

/-- `int uncompress2_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source, z_size_t *sourceLen)`:
does not fault and writes only `dest[0, *destLen)` (and fresh blocks, freed again). -/
def Goal.uncompress2_z_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen sourceLen : Option UInt64),
    CrcGlobals h → NullOrWrite h dest (destLen.getD 0).toNat → NullOrRead h source (sourceLen.getD 0).toNat →
    Disjoint dest (destLen.getD 0).toNat source (sourceLen.getD 0).toNat →
    ∃ r h', C.run (ZlibNg.Uncompr.uncompress2_z dest destLen source sourceLen) h = .ok (r, h') ∧
      Frame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int uncompress2(unsigned char *dest, unsigned long *destLen, const unsigned char *source,
unsigned long *sourceLen)`: as `uncompress2_z`. -/
def Goal.uncompress2_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen sourceLen : Option UInt64),
    CrcGlobals h → NullOrWrite h dest (destLen.getD 0).toNat → NullOrRead h source (sourceLen.getD 0).toNat →
    Disjoint dest (destLen.getD 0).toNat source (sourceLen.getD 0).toNat →
    ∃ r h', C.run (ZlibNg.Uncompr.uncompress2 dest destLen source sourceLen) h = .ok (r, h') ∧
      Frame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int uncompress(unsigned char *dest, unsigned long *destLen, const unsigned char *source,
unsigned long sourceLen)`: as `uncompress2_z`. -/
def Goal.uncompress_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64),
    CrcGlobals h → NullOrWrite h dest (destLen.getD 0).toNat → NullOrRead h source sourceLen.toNat →
    Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Uncompr.uncompress dest destLen source sourceLen) h = .ok (r, h') ∧
      Frame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int uncompress_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source, z_size_t sourceLen)`:
as `uncompress2_z`. -/
def Goal.uncompress_z_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64),
    CrcGlobals h → NullOrWrite h dest (destLen.getD 0).toNat → NullOrRead h source sourceLen.toNat →
    Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Uncompr.uncompress_z dest destLen source sourceLen) h = .ok (r, h') ∧
      Frame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

end ZlibNgF.Spec.Safety
