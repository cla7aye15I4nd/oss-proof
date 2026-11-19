import ZlibNgF.Runtime.Space
import ZlibNgF.Runtime.InffixedTbl

/-!
# Runtime heap (`ZlibNgF`)

Byte-addressed and static-table object heap for LP64 Linux translations of `zlib-ng` under strict ISO C17 pointer rules.
-/

set_option autoImplicit false

namespace C

/-- Source string literals compiled into `zlib-ng` (`ZLIB_COMPAT` build). -/
def strTable : Array String := #[
  "1.3.2.zlib-ng",
  " zlib-ng 2.3.90 devel",
  "need dictionary",
  "stream end",
  "",
  "file error",
  "stream error",
  "data error",
  "insufficient memory",
  "buffer error",
  "incompatible version",
  "header crc mismatch",
  "incorrect data check",
  "incorrect header check",
  "incorrect length check",
  "invalid bit length repeat",
  "invalid block type",
  "invalid code -- missing end-of-block",
  "invalid code lengths set",
  "invalid distance code",
  "invalid distance too far back",
  "invalid distances set",
  "invalid literal/length code",
  "invalid literal/lengths set",
  "invalid stored block lengths",
  "invalid window size",
  "too many length or distance symbols",
  "unknown compression method",
  "unknown header flags set"
]

/-- Reference to a byte array: a dynamically allocated heap block, a read-only static block, or a source string literal. -/
inductive BRef where
  | heap (b : Nat)
  | const (b : Nat)
  | str (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a static `uint32_t` array (`crc_table` or `x2n_table`). -/
inductive URef where
  | st_crc_table
  | st_x2n_table
  deriving DecidableEq, Repr, Inhabited

abbrev BPtr := Ptr BRef
abbrev UPtr := Ptr URef

/-! ## Typed objects of the inflate side

A `z_stream` and a `gz_header` are caller objects, one per entry of `Heap.streams` / `Heap.gzheaders`. An
`inflate_state` and an `inflate_allocs` record live inside the single byte block that `alloc_inflate` gets from
`zalloc`; they are typed objects keyed by the number of that block (`Heap.istates`, `Heap.iallocs`), made by the
carve primitives of `Runtime/Inflate.lean`. A typed object is alive while its byte block is alive. -/

/-- A pointer to a `z_stream`: null, or the entry of `Heap.streams`. -/
abbrev StreamPtr := Option Nat
/-- A pointer to a `gz_header`: null, or the entry of `Heap.gzheaders`. -/
abbrev HeaderPtr := Option Nat
/-- A pointer to an `inflate_state` (`struct internal_state *` of an inflate stream): null, or the byte block that
holds it. -/
abbrev StatePtr := Option Nat
/-- A pointer to an `inflate_allocs` record: null, or the byte block that holds it. -/
abbrev AllocsPtr := Option Nat

/-- A function pointer of type `alloc_func` / `free_func`: null, the library's default `zcalloc` / `zcfree`, or a
caller function (not modelled: calling it faults). -/
inductive FnPtr where
  | null
  | zcalloc
  | zcfree
  | other (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The value of a pointer field of a typed object that was carved from uninitialised memory: `uninit` until the
field is written. Reading an `uninit` pointer faults (`Runtime/Inflate.lean`, `Ival.get`). -/
inductive Ival (α : Type) where
  | uninit
  | val (a : α)
  deriving DecidableEq, Repr

instance {α : Type} : Inhabited (Ival α) := ⟨.uninit⟩

/-- Where an array of `code` lives: the `codes` array of the `inflate_state` in block `b`, or a static table. -/
inductive CodeRef where
  | codes (b : Nat)
  | lenfix
  | distfix
  deriving DecidableEq, Repr, Inhabited

/-- Where an array of `uint16_t` lives: `lens` or `work` of the `inflate_state` in block `b`. -/
inductive WRef where
  | lens (b : Nat)
  | work (b : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev CodePtr := Ptr CodeRef
abbrev WPtr := Ptr WRef

/-- `typedef struct z_stream_s` (`zlib.h`, `ZLIB_COMPAT`, LP64). -/
structure ZStream where
  next_in : BPtr := .null
  avail_in : UInt32 := 0
  total_in : UInt64 := 0
  next_out : BPtr := .null
  avail_out : UInt32 := 0
  total_out : UInt64 := 0
  msg : BPtr := .null
  state : StatePtr := none
  zalloc : FnPtr := .null
  zfree : FnPtr := .null
  «opaque» : BPtr := .null
  data_type : Int32 := 0
  adler : UInt64 := 0
  reserved : UInt64 := 0
  deriving Inhabited

/-- `typedef struct gz_header_s` (`zlib.h`). -/
structure GzHeader where
  text : Int32 := 0
  time : UInt64 := 0
  xflags : Int32 := 0
  os : Int32 := 0
  extra : BPtr := .null
  extra_len : UInt32 := 0
  extra_max : UInt32 := 0
  name : BPtr := .null
  name_max : UInt32 := 0
  comment : BPtr := .null
  comm_max : UInt32 := 0
  hcrc : Int32 := 0
  done : Int32 := 0
  deriving Inhabited

/-- `struct inflate_state` (`inflate.h`, verified configuration: no `INFLATE_STRICT`, no
`INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`, no arch state, LP64). The enum `mode` is an `unsigned int`. -/
structure InflateState where
  strm : Ival StreamPtr
  mode : UInt32
  last : Int32
  wrap : Int32
  havedict : Int32
  flags : Int32
  was : UInt32
  check : UInt64
  total : UInt64
  head : Ival HeaderPtr
  back : Int32
  wbits : UInt32
  wsize : UInt32
  wbufsize : UInt32
  whave : UInt32
  wnext : UInt32
  window : Ival BPtr
  hold : UInt64
  bits : UInt32
  lenbits : UInt32
  lencode : Ival CodePtr
  distcode : Ival CodePtr
  distbits : UInt32
  length : UInt32
  offset : UInt32
  extra : UInt32
  ncode : UInt32
  nlen : UInt32
  ndist : UInt32
  «have» : UInt32
  next : Ival CodePtr
  lens : Array UInt16
  work : Array UInt16
  codes : Array Code
  alloc_bufs : Ival AllocsPtr
  reqbits : UInt32
  deriving Inhabited

/-- `typedef struct inflate_allocs_s` (`inflate.h`). -/
structure InflateAllocs where
  buf_start : Ival BPtr
  zfree : Ival FnPtr
  state : Ival StatePtr
  window : Ival BPtr
  deriving Inhabited

/-- `sizeof(struct inflate_state)` on LP64 (`ALIGNED_(64)`), measured on the built configuration. -/
def SIZEOF_INFLATE_STATE : Nat := 9088
/-- `_Alignof(struct inflate_state)`. -/
def ALIGNOF_INFLATE_STATE : Nat := 64
/-- `sizeof(inflate_allocs)` on LP64. -/
def SIZEOF_INFLATE_ALLOCS : Nat := 32
/-- `_Alignof(inflate_allocs)` on LP64. -/
def ALIGNOF_INFLATE_ALLOCS : Nat := 8
/-- `sizeof(z_stream)` on LP64 (`ZLIB_COMPAT`). -/
def SIZEOF_Z_STREAM : Nat := 112
/-- `ENOUGH = ENOUGH_LENS + ENOUGH_DISTS` (`inftrees.h`). -/
def ENOUGH : Nat := 1332 + 592

/-- Heap state with byte blocks, read-only static blocks, CRC static tables, pointer-header metadata for
`zng_alloc_aligned` / `zng_free_aligned`, origin-address residue oracle, allocation oracle, and garbage oracle. -/
structure Heap where
  bytes : Tbl (Option (Array UInt8)) := .empty
  consts : Tbl (Option (Array UInt8)) := .empty
  crcTable : Array UInt32 := #[]
  x2nTable : Array UInt32 := #[]
  savedPtrs : Tbl (Option (Nat × BPtr)) := .empty
  nextBlk : Nat := 0
  nalloc : Nat := 0
  allocOk : Nat → Bool := fun _ => true
  garbage : Nat → Nat → UInt64 := fun _ _ => 0
  baseAddr : BRef → UInt64 := fun _ => 0
  /-- caller `z_stream` objects -/
  streams : Tbl (Option ZStream) := .empty
  /-- caller `gz_header` objects -/
  gzheaders : Tbl (Option GzHeader) := .empty
  /-- the `inflate_state` carved from byte block `b` -/
  istates : Tbl (Option InflateState) := .empty
  /-- the `inflate_allocs` record carved from byte block `b` -/
  iallocs : Tbl (Option InflateAllocs) := .empty

namespace Heap

def empty : Heap := {}

def litBytes (s : String) : Array UInt8 := s.toUTF8.data.push 0

def getBytes (h : Heap) : BRef → Option (Array UInt8)
  | .heap b => h.bytes b
  | .const b => h.consts b
  | .str i => strTable[i]?.map litBytes

def putBytes (h : Heap) (r : BRef) (a : Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := upd h.bytes b (some a) }
  | .const b => { h with consts := upd h.consts b (some a) }
  | .str _ => h

def isRo (_h : Heap) : BRef → Bool
  | .heap _ => false
  | .const _ => true
  | .str _ => true

def modifyBytes (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := h.bytes.modify b (Option.map f) }
  | .const b => { h with consts := h.consts.modify b (Option.map f) }
  | .str _ => h

theorem modifyBytes_eq (h : Heap) (r : BRef) (a : Array UInt8) (f : Array UInt8 → Array UInt8)
    (hg : getBytes h r = some a) (hro : isRo h r = false) :
    modifyBytes h r f = putBytes h r (f a) := by
  cases r with
  | heap b =>
    simp only [getBytes] at hg
    simp only [modifyBytes, putBytes, Tbl.modify_opt h.bytes b f a hg]
  | const _ => simp [isRo] at hro
  | str _ => simp [isRo] at hro

def getU32 (h : Heap) : URef → Option (Array UInt32)
  | .st_crc_table => some h.crcTable
  | .st_x2n_table => some h.x2nTable

def putU32 (h : Heap) (_r : URef) (_a : Array UInt32) : Heap := h
def isRoU32 (_h : Heap) (_r : URef) : Bool := true
def modifyU32 (h : Heap) (_r : URef) (_f : Array UInt32 → Array UInt32) : Heap := h

theorem modifyU32_eq (h : Heap) (r : URef) (a : Array UInt32) (f : Array UInt32 → Array UInt32)
    (_hg : getU32 h r = some a) (hro : isRoU32 h r = false) :
    modifyU32 h r f = putU32 h r (f a) := by
  simp [isRoU32] at hro

end Heap

instance : Space Heap BRef UInt8 where
  get := Heap.getBytes
  put := Heap.putBytes
  ro := Heap.isRo
  modify := Heap.modifyBytes
  modify_eq := Heap.modifyBytes_eq

instance : Space Heap URef UInt32 where
  get := Heap.getU32
  put := Heap.putU32
  ro := Heap.isRoU32
  modify := Heap.modifyU32
  modify_eq := Heap.modifyU32_eq

end C
