import ZlibNgF.Spec.Common.Inflate
import ZlibNgF.ZlibNg.«compress.c»

/-!
# Deflate specification vocabulary (`ZlibNgF`)

Caller buffers, the streams that the deflate functions accept, and the frame of what a call may change. No `Goal.*`
definitions live here; the goals are in `ZlibNgF.Spec.Safety.Deflate`. The buffer predicates (`ReadSlice`,
`NullOrWrite`, `PairwiseDisjoint`, ...) are those of `ZlibNgF.Spec.Common.Inflate`.

**The representation invariant.** A deflate stream is accepted when it is *reachable* (`DeflateReachable`): made
by a successful `deflateInit_` / `deflateInit2_` (or `deflateCopy`) and then changed only by public deflate calls
with valid arguments and by the caller, who may change the four buffer fields of the `z_stream` (`next_in`,
`avail_in`, `next_out`, `avail_out`) and any memory the library does not own, but not the other `z_stream` fields or
the block of the stream's state. A `gz_header` registered by `deflateSetHeader` stays allocated (`deflateBound` and
`deflate` read it). While `deflate` is writing the gzip header (status `EXTRA_STATE` .. `HCRC_STATE`, the header was
begun by an earlier call), the caller keeps the header's `extra`, `extra_len`, `name` and `comment` fields and the
lengths of the `name` and `comment` strings: `deflate` resumes the copy at the saved index `gzindex`, so these values
must be those the earlier call used. That is the only caller-owned data that safety needs to stay put between calls.

**Narrowings** (listed in the deviations page): the default allocator only (`zalloc` / `zfree` are `Z_NULL` at
`deflateInit*`, or already `zcalloc` / `zcfree`); caller buffers (input, output, dictionary, header buffers)
pairwise disjoint where one of them is written, and outside the library's own block; `deflateGetDictionary` writes
into a buffer of at least 32768 bytes, the size `zlib.h` names as always enough; `deflateCopy` with distinct source
and destination, on a heap whose unallocated blocks hold no object (`DFreshBlocks`, as its goal assumes); `deflateSetHeader` registers a header for the stream only before the first `deflate` call (status
`GZIP_STATE`), `deflatePrime` is called only before any pending output was flushed (`PrimeReady`), and
`deflateSetDictionary` only with no tallied symbols (`DictReady`), as `zlib.h` requires; the buffer of
`deflateGetDictionary` does not overlap the registered header's buffers.
-/

set_option autoImplicit false

namespace ZlibNgF.Spec
open C

/-! ## Heap well-formedness -/

/-- `FreshBlocks` for the deflate objects as well: no byte block, inflate or deflate object lives in a block that
the allocator has not handed out yet (true of every heap a C program reaches; see `FreshBlocks`). -/
def DFreshBlocks (h : Heap) : Prop :=
  FreshBlocks h ∧ ∀ b, h.nextBlk ≤ b → h.dstates b = none ∧ h.dallocs b = none

/-! ## Caller data -/

/-- `p` is a C string of `n` characters: `n + 1` readable bytes, the last one zero and no zero before it. -/
def CStringLen (h : Heap) (p : BPtr) (n : Nat) : Prop :=
  ∃ r off data, p = .ref r off ∧ Space.get h r = some data ∧ off + n + 1 ≤ data.size ∧
    data[off + n]! = 0 ∧ ∀ i, i < n → data[off + i]! ≠ 0

/-- A `gz_header` that `deflate` may read: a live record whose `extra` is `Z_NULL` or has `extra_len` readable bytes
and whose `name` and `comment` are `Z_NULL` or C strings (`zlib.h`, `deflateSetHeader`). -/
def DHeaderOk (h : Heap) (k : Nat) : Prop :=
  ∃ g, h.gzheaders k = some g ∧ NullOrRead h g.extra g.extra_len.toNat ∧
    (g.name = .null ∨ ∃ n, CStringLen h g.name n) ∧ (g.comment = .null ∨ ∃ n, CStringLen h g.comment n)

/-- The ranges `deflate` reads from header `k`, given as a predicate on ranges: the extra field, and each string
with its zero byte. -/
def DHeaderRange (h : Heap) (k : Nat) (r : BPtr × Nat) : Prop :=
  ∃ g, h.gzheaders k = some g ∧
    (r = (g.extra, g.extra_len.toNat) ∨ (∃ n, CStringLen h g.name n ∧ r = (g.name, n + 1)) ∨
      (∃ n, CStringLen h g.comment n ∧ r = (g.comment, n + 1)))

/-! ## Streams -/

/-- The `deflate_state` of stream `s` (its block and the record). -/
def DStateOf (h : Heap) (s : StreamPtr) (b : Nat) (st : DeflateState) : Prop :=
  StateBlock h s b ∧ h.dstate b = some st

/-- The `gz_header` registered on the state of `s` by `deflateSetHeader` (`none`: no header). -/
def DRegisteredHeader (h : Heap) (s : StreamPtr) (hp : HeaderPtr) : Prop :=
  ∃ b st, DStateOf h s b st ∧ st.gzhead = .val hp

/-- The caller ranges a `deflate` call only reads: the input buffer and the registered header's buffers. -/
def DReadRange (h : Heap) (z : ZStream) (hp : HeaderPtr) (r : BPtr × Nat) : Prop :=
  r = (z.next_in, z.avail_in.toNat) ∨ ∃ k, hp = some k ∧ DHeaderRange h k r

/-- The buffers of a stream are valid for a call that reads input and writes output: `next_in` is `NULL` or has
`avail_in` readable bytes, `next_out` is `NULL` or has `avail_out` writable bytes, a registered header is
readable (`DHeaderOk`), the output range is disjoint from the input and the header buffers, and all of them are
outside the library's block `b`. (The input and the header buffers are only read and may overlap each other.) -/
def DStreamIO (h : Heap) (s : StreamPtr) : Prop :=
  ∃ z b hp, StreamAt h s z ∧ z.state = some b ∧ DRegisteredHeader h s hp ∧
    (∀ k, hp = some k → DHeaderOk h k) ∧
    NullOrRead h z.next_in z.avail_in.toNat ∧ NullOrWrite h z.next_out z.avail_out.toNat ∧
    NotInBlock b z.next_out ∧
    ∀ r, DReadRange h z hp r → Disjoint z.next_out z.avail_out.toNat r.1 r.2 ∧ NotInBlock b r.1

/-- A stream ready for `deflateInit*` (same as for `inflateInit*`). -/
abbrev DInitReady := InitReady

/-- The caller's changes between library calls, seen from stream `s` (see the module comment): only the four buffer
fields of the `z_stream` change; the library's block `b` (bytes, `deflate_state`, `deflate_allocs`) and the origin
addresses stay; a registered header stays allocated, and while its writing is in progress its `extra`,
`extra_len`, `name` and `comment` fields and the lengths of its strings stay; blocks are never reused. -/
def DCallerStep (h h' : Heap) (s : StreamPtr) : Prop :=
  ∃ i z z' b st, s = some i ∧ h.streams i = some z ∧ h'.streams i = some z' ∧ z.state = some b ∧
    h.dstate b = some st ∧
    z' = { z with next_in := z'.next_in, avail_in := z'.avail_in, next_out := z'.next_out,
                  avail_out := z'.avail_out } ∧
    h'.bytes b = h.bytes b ∧ h'.dstates b = h.dstates b ∧ h'.dallocs b = h.dallocs b ∧
    (∀ k g, st.gzhead = .val (some k) → h.gzheaders k = some g → ∃ g', h'.gzheaders k = some g' ∧
      ((st.status = ZlibNg.Deflate.EXTRA_STATE ∨ st.status = ZlibNg.Deflate.NAME_STATE ∨
        st.status = ZlibNg.Deflate.COMMENT_STATE ∨ st.status = ZlibNg.Deflate.HCRC_STATE) →
        g'.extra = g.extra ∧ g'.extra_len = g.extra_len ∧ g'.name = g.name ∧ g'.comment = g.comment ∧
        (∀ n, CStringLen h g.name n → CStringLen h' g.name n) ∧
        (∀ n, CStringLen h g.comment n → CStringLen h' g.comment n))) ∧
    h'.baseAddr = h.baseAddr ∧ h.nextBlk ≤ h'.nextBlk

/-- The status of the deflate state of `s` is `GZIP_STATE` (no `deflate` call has begun the gzip header). -/
def BeforeFirstDeflate (h : Heap) (s : StreamPtr) : Prop :=
  ∃ b st, DStateOf h s b st ∧ st.status = ZlibNg.Deflate.GZIP_STATE

/-- No pending output has been flushed since the last `deflateInit*` / `deflateReset`: `pending_out` is
`pending_buf`. `zlib.h` allows `deflatePrime` only before the first `deflate` call after `deflateInit2` or
`deflateReset`, when this holds; `deflatePrime` writes its bytes at `pending_buf + pending`, so after a partial flush
(`pending_out` past `pending_buf`) the pending range moves past `pending_buf` with every primed byte. -/
def PrimeReady (h : Heap) (s : StreamPtr) : Prop :=
  ∃ b st, DStateOf h s b st ∧ st.pending_out = st.pending_buf

/-- No symbol is tallied in the deflate state of `s` (`sym_next == 0`). `zlib.h` allows `deflateSetDictionary`
only before the first `deflate` call or, for raw deflate, right after a completed block (all input consumed and all
output delivered with `Z_BLOCK`, `Z_PARTIAL_FLUSH`, `Z_SYNC_FLUSH` or `Z_FULL_FLUSH`), when this holds; the call sets
`block_start` to `strstart`, which in the middle of a block would detach the tallied symbols from their window
bytes. -/
def DictReady (h : Heap) (s : StreamPtr) : Prop :=
  ∃ b st, DStateOf h s b st ∧ st.sym_next = 0

/-- One public deflate call on stream `s` with valid arguments that returns (any result); `deflateEnd` is not a
step (it ends the stream). -/
def DeflateStep (h h' : Heap) (s : StreamPtr) : Prop :=
  (∃ flush r, CrcGlobals h ∧ DStreamIO h s ∧ C.run (ZlibNg.Deflate.deflate s flush) h = .ok (r, h')) ∨
  (∃ level strategy r, CrcGlobals h ∧ DStreamIO h s ∧
    C.run (ZlibNg.Deflate.deflateParams s level strategy) h = .ok (r, h')) ∨
  (∃ d n r, DictReady h s ∧ NullOrRead h d n.toNat ∧ (∀ b, StateBlock h s b → NotInBlock b d) ∧
    C.run (ZlibNg.Deflate.deflateSetDictionary s d n) h = .ok (r, h')) ∨
  (∃ d hasLen r, NullOrWrite h d 32768 ∧ (∀ b, StateBlock h s b → NotInBlock b d) ∧
    (∀ k, DRegisteredHeader h s (some k) → ∀ r, DHeaderRange h k r → Disjoint d 32768 r.1 r.2) ∧
    C.run (ZlibNg.Deflate.deflateGetDictionary s d hasLen) h = .ok (r, h')) ∨
  (∃ hp r, BeforeFirstDeflate h s ∧ (∀ k, hp = some k → DHeaderOk h k) ∧
    C.run (ZlibNg.Deflate.deflateSetHeader s hp) h = .ok (r, h')) ∨
  (∃ hp hb r, C.run (ZlibNg.Deflate.deflatePending s hp hb) h = .ok (r, h')) ∨
  (∃ hb r, C.run (ZlibNg.Deflate.deflateUsed s hb) h = .ok (r, h')) ∨
  (∃ bits value r, PrimeReady h s ∧ C.run (ZlibNg.Deflate.deflatePrime s bits value) h = .ok (r, h')) ∨
  (∃ g l n c r, C.run (ZlibNg.Deflate.deflateTune s g l n c) h = .ok (r, h')) ∨
  (∃ n r, C.run (ZlibNg.Deflate.deflateBound s n) h = .ok (r, h')) ∨
  (∃ n r, C.run (ZlibNg.Deflate.deflateBound_z s n) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Deflate.deflateReset s) h = .ok (r, h')) ∨
  (∃ r, C.run (ZlibNg.Deflate.deflateResetKeep s) h = .ok (r, h')) ∨
  (∃ dst r, InitReady h dst ∧ dst ≠ s ∧ C.run (ZlibNg.Deflate.deflateCopy dst s) h = .ok (r, h'))

/-- The deflate streams reachable through `zlib.h` (see the module comment). -/
inductive DeflateReachable : Heap → StreamPtr → Prop where
  | init (h h' : Heap) (s : StreamPtr) (level : Int32) (version : BPtr) (size : Int32) :
      DInitReady h s → VersionOk h version →
      C.run (ZlibNg.Deflate.deflateInit_ s level version size) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      DeflateReachable h' s
  | init2 (h h' : Heap) (s : StreamPtr) (level method windowBits memLevel strategy : Int32) (version : BPtr)
      (size : Int32) :
      DInitReady h s → VersionOk h version →
      C.run (ZlibNg.Deflate.deflateInit2_ s level method windowBits memLevel strategy version size) h =
        .ok (ZlibNg.Inflate.Z_OK, h') →
      DeflateReachable h' s
  | copy (h h' : Heap) (src dst : StreamPtr) :
      DeflateReachable h src → DFreshBlocks h → InitReady h dst → dst ≠ src →
      C.run (ZlibNg.Deflate.deflateCopy dst src) h = .ok (ZlibNg.Inflate.Z_OK, h') →
      DeflateReachable h' dst
  | step (h h' : Heap) (s : StreamPtr) : DeflateReachable h s → DeflateStep h h' s → DeflateReachable h' s
  | caller (h h' : Heap) (s : StreamPtr) : DeflateReachable h s → DCallerStep h h' s → DeflateReachable h' s

/-- A stream that any deflate function accepts: `Z_NULL`, a live `z_stream` with no state (never initialised with
the zero `state` field, or after `deflateEnd`), or a reachable stream. -/
def DeflateHandle (h : Heap) (s : StreamPtr) : Prop :=
  s = none ∨ (∃ z, StreamAt h s z ∧ z.state = none) ∨ DeflateReachable h s

/-- The registered header of a reachable stream is readable (`deflateBound` reads it). -/
def DHeaderReadable (h : Heap) (s : StreamPtr) : Prop :=
  ∀ k, DRegisteredHeader h s (some k) → DHeaderOk h k

/-! ## Frames -/

/-- `Frame` (see `ZlibNgF.Spec.Common.Inflate`), and the deflate objects of blocks outside `lib` stay. -/
def DFrame (h h' : Heap) (streams : List Nat) (lib : List Nat) (headers : List Nat) (writes : List (BPtr × Nat)) :
    Prop :=
  Frame h h' streams lib headers writes ∧
  ∀ b, b < h.nextBlk → b ∉ lib → h'.dstates b = h.dstates b ∧ h'.dallocs b = h.dallocs b

/-- The caller range a `deflate` call may write: the output buffer. -/
def dOutputRanges (h : Heap) (s : StreamPtr) : List (BPtr × Nat) :=
  match s with
  | none => []
  | some i => match h.streams i with
    | some z => [(z.next_out, z.avail_out.toNat)]
    | none => []

end ZlibNgF.Spec
