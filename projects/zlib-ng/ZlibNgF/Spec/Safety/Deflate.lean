import ZlibNgF.Spec.Common.Deflate

/-!
# Safety goals of the deflate side (`ZlibNgF`)

`deflate.c` (with `trees.c`, the strategies, `insert_string.c`, `compare256_c.c`, `slide_hash_c.c`) and the
one-shot functions of `compress.c`. Each goal says that the call does not fault (no undefined behaviour, and it
returns) for every stream the function accepts (`DeflateHandle`: `Z_NULL`, a stream with no state, or a reachable
stream) and valid caller buffers, and that it changes only what the frame names: the stream record, the library's
own block, and the caller buffers the function writes. That a successful call keeps the stream reachable is part of
`DeflateReachable` itself; the content of the goals is that no reachable state lets a call fault. The narrowings are
in the module comment of `ZlibNgF.Spec.Common.Deflate` and on the deviations page.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec.Safety
open ZlibNgF.Spec C

/-! ## Initialisation -/

/-- `int deflateInit_(z_stream *strm, int level, const char *version, int stream_size)`: for a `Z_NULL` stream or a
live `z_stream` with the default allocator, every `level`, a `NULL` or readable `version` and any `stream_size`,
does not fault and changes only the stream record and fresh blocks. The heap is well formed (`DFreshBlocks`). -/
def Goal.deflateInit__safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (level : Int32) (version : BPtr) (size : Int32),
    DFreshBlocks h → DInitReady h s → VersionOk h version →
    ∃ r h', C.run (ZlibNg.Deflate.deflateInit_ s level version size) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) [] [] []

/-- `int deflateInit2_(z_stream *strm, int level, int method, int windowBits, int memLevel, int strategy,
const char *version, int stream_size)`: as `deflateInit_`, for every parameter value. -/
def Goal.deflateInit2__safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (level method windowBits memLevel strategy : Int32) (version : BPtr) (size : Int32),
    DFreshBlocks h → DInitReady h s → VersionOk h version →
    ∃ r h', C.run (ZlibNg.Deflate.deflateInit2_ s level method windowBits memLevel strategy version size) h =
      .ok (r, h') ∧
      DFrame h h' (streamIds s) [] [] []

/-- Non-vacuity of `DeflateReachable`: `deflateInit_` on a fresh zero `z_stream` (as `compress` makes it) with the
library's version string succeeds, so reachable streams exist. -/
def Goal.deflateInit_nonvacuous : Prop :=
  ∃ h h' s, DFreshBlocks h ∧ DInitReady h s ∧
    C.run (do let v ← strLitRef "1.3.2.zlib-ng"; ZlibNg.Deflate.deflateInit_ s 6 v 112) h =
      .ok (ZlibNg.Inflate.Z_OK, h') ∧
    DeflateReachable h' s

/-! ## Compression -/

/-- `int deflate(z_stream *strm, int flush)`: for every accepted stream with valid buffers (the output disjoint from
the input and the header buffers, all outside the library's block) and every `flush`, does not fault and writes
only the output buffer, the stream record and the library's block. -/
def Goal.deflate_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (flush : Int32),
    CrcGlobals h → DeflateHandle h s → (DeflateReachable h s → DStreamIO h s) →
    ∃ r h', C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s)

/-- Non-vacuity of `deflate_safety`: its premises hold together on a reachable stream whose input and output
buffers are non-null and non-empty, and one `deflate(Z_FINISH)` call on it returns. It does not say which result
the call returns. -/
def Goal.deflate_nonvacuous : Prop :=
  ∃ h s h' r z, CrcGlobals h ∧ DeflateReachable h s ∧ DStreamIO h s ∧ StreamAt h s z ∧
    z.next_in ≠ .null ∧ z.next_out ≠ .null ∧ 0 < z.avail_in ∧ 0 < z.avail_out ∧
    C.run (ZlibNg.Deflate.deflate s 4) h = .ok (r, h')

/-- `int deflateEnd(z_stream *strm)`: does not fault and frees only the stream's state block. -/
def Goal.deflateEnd_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflateEnd s) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] []

/-- `int deflateParams(z_stream *strm, int level, int strategy)`: for every `level` and `strategy`, with valid
buffers as for `deflate` (it may call `deflate(strm, Z_BLOCK)`), does not fault and writes only the output buffer,
the stream record and the library's block. -/
def Goal.deflateParams_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (level strategy : Int32),
    CrcGlobals h → DeflateHandle h s → (DeflateReachable h s → DStreamIO h s) →
    ∃ r h', C.run (ZlibNg.Deflate.deflateParams s level strategy) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] (dOutputRanges h s)

/-- `int deflateTune(z_stream *strm, int good_length, int max_lazy, int nice_length, int max_chain)`: for every value,
does not fault and changes only the library's block. -/
def Goal.deflateTune_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (g l n c : Int32),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflateTune s g l n c) h = .ok (r, h') ∧
      DFrame h h' [] (stateIds h s) [] []

/-- `int deflatePrime(z_stream *strm, int bits, int value)`: for every `bits` and `value`, does not fault and
changes only the library's block. -/
def Goal.deflatePrime_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (bits value : Int32),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflatePrime s bits value) h = .ok (r, h') ∧
      DFrame h h' [] (stateIds h s) [] []

/-! ## Dictionaries and headers -/

/-- `int deflateSetDictionary(z_stream *strm, const Bytef *dictionary, uInt dictLength)`: for a `NULL` or readable
dictionary of `dictLength` bytes outside the library's block, does not fault and changes only the stream record and
the library's block. -/
def Goal.deflateSetDictionary_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (d : BPtr) (n : UInt32),
    DeflateHandle h s → NullOrRead h d n.toNat → (∀ b, StateBlock h s b → NotInBlock b d) →
    ∃ r h', C.run (ZlibNg.Deflate.deflateSetDictionary s d n) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] []

/-- `int deflateGetDictionary(z_stream *strm, Bytef *dictionary, uInt *dictLength)`: for a `NULL` dictionary or one of
at least 32768 writable bytes outside the library's block, with or without a length cell, does not fault and writes
only the dictionary buffer. -/
def Goal.deflateGetDictionary_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (d : BPtr) (hasLen : Bool),
    DeflateHandle h s → NullOrWrite h d 32768 → (∀ b, StateBlock h s b → NotInBlock b d) →
    ∃ r h', C.run (ZlibNg.Deflate.deflateGetDictionary s d hasLen) h = .ok (r, h') ∧
      DFrame h h' [] [] [] [(d, 32768)]

/-- `int deflateSetHeader(z_stream *strm, gz_headerp head)`: for every header pointer, does not fault and changes
only the library's block (it stores the pointer; the header is read by later calls). -/
def Goal.deflateSetHeader_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (hp : HeaderPtr),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflateSetHeader s hp) h = .ok (r, h') ∧
      DFrame h h' [] (stateIds h s) [] []

/-! ## Queries -/

/-- `int deflatePending(z_stream *strm, unsigned *pending, int *bits)`: with or without each out-cell, does not fault
and changes nothing (the values for the out-cells are returned). -/
def Goal.deflatePending_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (hp hb : Bool),
    DeflateHandle h s →
    ∃ r, C.run (ZlibNg.Deflate.deflatePending s hp hb) h = .ok (r, h)

/-- `int deflateUsed(z_stream *strm, int *bits)`: does not fault and changes nothing. -/
def Goal.deflateUsed_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (hb : Bool),
    DeflateHandle h s →
    ∃ r, C.run (ZlibNg.Deflate.deflateUsed s hb) h = .ok (r, h)

/-- `uLong deflateBound(z_stream *strm, uLong sourceLen)`: for every `sourceLen`, on an accepted stream whose
registered header is readable, does not fault and changes nothing. -/
def Goal.deflateBound_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (n : UInt64),
    DeflateHandle h s → DHeaderReadable h s →
    ∃ r, C.run (ZlibNg.Deflate.deflateBound s n) h = .ok (r, h)

/-- `z_size_t deflateBound_z(z_stream *strm, z_size_t sourceLen)`: as `deflateBound`. -/
def Goal.deflateBound_z_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr) (n : UInt64),
    DeflateHandle h s → DHeaderReadable h s →
    ∃ r, C.run (ZlibNg.Deflate.deflateBound_z s n) h = .ok (r, h)

/-! ## Control -/

/-- `int deflateReset(z_stream *strm)`: does not fault and changes only the stream record and the library's
block. -/
def Goal.deflateReset_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflateReset s) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] []

/-- `int deflateResetKeep(z_stream *strm)`: as `deflateReset`. -/
def Goal.deflateResetKeep_safety : Prop :=
  ∀ (h : Heap) (s : StreamPtr),
    DeflateHandle h s →
    ∃ r h', C.run (ZlibNg.Deflate.deflateResetKeep s) h = .ok (r, h') ∧
      DFrame h h' (streamIds s) (stateIds h s) [] []

/-- `int deflateCopy(z_stream *dest, z_stream *source)`: for an accepted source and a distinct live destination,
does not fault and changes only the destination record and fresh blocks. -/
def Goal.deflateCopy_safety : Prop :=
  ∀ (h : Heap) (dst src : StreamPtr),
    DFreshBlocks h → DeflateHandle h src → InitReady h dst → dst ≠ src →
    ∃ r h', C.run (ZlibNg.Deflate.deflateCopy dst src) h = .ok (r, h') ∧
      DFrame h h' (streamIds dst) [] [] []

/-! ## One-shot compression

The destination is `NULL` or has `*destLen` writable bytes, the source is `NULL` or has `sourceLen` readable bytes,
and the two do not overlap. The heap is well formed (`DFreshBlocks`: `compress` allocates a deflate state) and
every object has fewer than `2^63` bytes (`ObjBound`: the model bounds the number of trips of a loop by `2^64`). -/

/-- `int compress2_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source, z_size_t sourceLen,
int level)`: does not fault and writes only `dest[0, *destLen)` (and fresh blocks, freed again). -/
def Goal.compress2_z_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64) (level : Int32),
    CrcGlobals h → DFreshBlocks h → ObjBound h → NullOrWrite h dest (destLen.getD 0).toNat →
    NullOrRead h source sourceLen.toNat → Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Compress.compress2_z dest destLen source sourceLen level) h = .ok (r, h') ∧
      DFrame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int compress2(unsigned char *dest, unsigned long *destLen, const unsigned char *source, unsigned long sourceLen,
int level)`: as `compress2_z`. -/
def Goal.compress2_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64) (level : Int32),
    CrcGlobals h → DFreshBlocks h → ObjBound h → NullOrWrite h dest (destLen.getD 0).toNat →
    NullOrRead h source sourceLen.toNat → Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Compress.compress2 dest destLen source sourceLen level) h = .ok (r, h') ∧
      DFrame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int compress(unsigned char *dest, unsigned long *destLen, const unsigned char *source, unsigned long sourceLen)`:
as `compress2_z`. -/
def Goal.compress_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64),
    CrcGlobals h → DFreshBlocks h → ObjBound h → NullOrWrite h dest (destLen.getD 0).toNat →
    NullOrRead h source sourceLen.toNat → Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Compress.compress dest destLen source sourceLen) h = .ok (r, h') ∧
      DFrame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

/-- `int compress_z(unsigned char *dest, z_size_t *destLen, const unsigned char *source, z_size_t sourceLen)`: as
`compress2_z`. -/
def Goal.compress_z_safety : Prop :=
  ∀ (h : Heap) (dest source : BPtr) (destLen : Option UInt64) (sourceLen : UInt64),
    CrcGlobals h → DFreshBlocks h → ObjBound h → NullOrWrite h dest (destLen.getD 0).toNat →
    NullOrRead h source sourceLen.toNat → Disjoint dest (destLen.getD 0).toNat source sourceLen.toNat →
    ∃ r h', C.run (ZlibNg.Compress.compress_z dest destLen source sourceLen) h = .ok (r, h') ∧
      DFrame h h' [] [] [] [(dest, (destLen.getD 0).toNat)]

end ZlibNgF.Spec.Safety
