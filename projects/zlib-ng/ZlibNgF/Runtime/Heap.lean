import ZlibNgF.Runtime.Space

/-!
# Runtime heap (`ZlibNgF`)

Byte-addressed and static-table object heap for LP64 Linux translations of `zlib-ng` under strict ISO C17 pointer rules.
-/

set_option autoImplicit false

namespace C

/-- Source string literals compiled into `zlib-ng` (`ZLIB_COMPAT` build). -/
def strTable : Array String := #[
  "1.3.1.zlib-ng",
  " zlib-ng 2.3.3",
  "need dictionary",
  "stream end",
  "",
  "file error",
  "stream error",
  "data error",
  "insufficient memory",
  "buffer error",
  "incompatible version"
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
