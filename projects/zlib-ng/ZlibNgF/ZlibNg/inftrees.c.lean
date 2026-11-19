import ZlibNgF.ZlibNg.«inflate_p.h»

/-!
# `inftrees.c` — Huffman decoding table builder (`ZlibNgF`)

Source: `zlib-ng/inftrees.c`, x86_64: `count_lengths` takes its `__SSE2__` branch (SSE2 is part of the x86_64
baseline; `__AVX2__` is not defined). The SSE2 intrinsics are modelled by their documented lane semantics:
`_mm_load_si128` is an aligned 16-byte load (`one` is `ALIGNED_(16)`, so `&one[16 * k]` is aligned; an index
`16 * k` outside the table faults), `_mm_add_epi8` / `_mm_add_epi16` are lane-wise wrapping additions, and
`_mm_unpacklo/hi_epi8` with zero widen bytes to 16-bit lanes.

Local arrays (`count`, `offs`) are Lean arrays with checked indexing. `code **table` and `unsigned *bits` are passed
by value and returned with the result (normalisation 1). `zng_memread_4(&here)` / `zng_memwrite_4(&slot, v)` move
the four bytes of a `code` (`bits`, `op`, `val` little-endian) as a `uint32_t`; the model packs and unpacks the
record. `zng_bitreverse16` (`fallback_builtins.h`: `__builtin_bitreverse16`, or a portable bit reversal) is the
reversal of the 16 bits.
-/

set_option autoImplicit false

namespace ZlibNg.Inftrees
open C ZlibNg.Zbuild ZlibNg.InflateP

/-- `typedef enum { CODES, LENS, DISTS } codetype;` (`inftrees.h:57-61`). -/
def CODES : UInt32 := 0
def LENS : UInt32 := 1
def DISTS : UInt32 := 2
/-- `#define ENOUGH_LENS 1332` -/
def ENOUGH_LENS : UInt32 := 1332
/-- `#define ENOUGH_DISTS 592` -/
def ENOUGH_DISTS : UInt32 := 592

/-- `a[i]` for a local array: faults outside it. -/
def aget {α : Type} [Inhabited α] (a : Array α) (i : Nat) : M α :=
  if h : i < a.size then pure a[i] else ub "local array index outside its array"

/-- `a[i] = v` for a local array: faults outside it. -/
def aset {α : Type} (a : Array α) (i : Nat) (v : α) : M (Array α) :=
  if i < a.size then pure (a.set! i v) else ub "local array index outside its array"

/-- `zng_bitreverse16(value)`. -/
def zng_bitreverse16 (value : UInt16) : UInt16 := Id.run do
  let mut r : UInt16 := 0
  for i in [0:16] do
    if (value >>> i.toUInt16) &&& 1 != 0 then
      r := r ||| ((1 : UInt16) <<< (15 - i).toUInt16)
  return r

/-- The bytes of a `code` read as a `uint32_t` (`zng_memread_4(&here)`). -/
def packCode (c : Code) : UInt32 := c.bits.toUInt32 ||| (c.op.toUInt32 <<< 8) ||| (c.val.toUInt32 <<< 16)

/-- A `uint32_t` written over a `code` (`zng_memwrite_4(&slot, v)`). -/
def unpackCode (v : UInt32) : Code := ⟨v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt16⟩

/-- `static const ALIGNED_(16) uint8_t one[256]`: row `k` has a 1 in lane `k`. -/
def oneRow (k : UInt16) : M (Array UInt8) :=
  if k < 16 then pure (Array.ofFn (n := 16) fun i => if i.val == k.toNat then 1 else 0)
  else ub "_mm_load_si128 outside the table one"

/-- Lane-wise wrapping byte addition (`_mm_add_epi8`). -/
def addEpi8 (a b : Array UInt8) : Array UInt8 := Array.ofFn (n := 16) fun i => a[i]! + b[i]!

/-- `static inline void count_lengths(uint16_t *lens, int codes, uint16_t *count)` (`inftrees.c:30-114`,
`__SSE2__` branch). Returns `count[0..15]`. -/
def count_lengths (lens : WPtr) (codes : Int32) : M (Array UInt16) := do
  let zero : Array UInt8 := Array.replicate 16 0
  let s1 ← if codes &&& 1 != 0 then do oneRow (← Ptr.index lens 0) else pure zero
  let s2 := zero
  let (s1, s2, _) ← cwhile
    (fun ((s1, s2, sym) : Array UInt8 × Array UInt8 × Int32) => pure (sym < codes, (s1, s2, sym)))
    (fun ((s1, s2, sym) : Array UInt8 × Array UInt8 × Int32) => do
      let l0 ← Ptr.index lens sym.toInt
      let s1 := addEpi8 s1 (← oneRow l0)
      let l1 ← Ptr.index lens (sym.toInt + 1)
      let s2 := addEpi8 s2 (← oneRow l1)
      pure (s1, s2, ← chkI32 (sym.toInt + 2)))
    (s1, s2, codes &&& 1)
  -- sum_lo = s1_lo + s2_lo (lanes 0..7), sum_hi = s1_hi + s2_hi (lanes 8..15), 16-bit wrapping
  return Array.ofFn (n := 16) fun i => s1[i]!.toUInt16 + s2[i]!.toUInt16

/-- A pointer to an array of `uint16_t` used as `base` / `extra`: the caller's `work`, or a static table. -/
inductive U16Src where
  | ptr (p : WPtr)
  | st (a : Array UInt16)

def U16Src.at (s : U16Src) (i : Nat) : M UInt16 :=
  match s with
  | .ptr p => Ptr.index p (Int.ofNat i)
  | .st a => aget a i

/-- `static const uint16_t lbase[31]` -/
def lbase : Array UInt16 := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0]
/-- `static const uint16_t lext[31]` -/
def lext : Array UInt16 := #[16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18,
  19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 199, 75]
/-- `static const uint16_t dbase[32]` -/
def dbase : Array UInt16 := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 0, 0]
/-- `static const uint16_t dext[32]` -/
def dext : Array UInt16 := #[16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22,
  23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 64, 64]

/-- Store a `code` at `p[i]`. -/
def stCode (p : CodePtr) (i : Int) (c : Code) : M Unit := do
  Ptr.store (← p.add i) c

/-- The locals of the table-filling loop of `zng_inflate_table`. -/
structure TL where
  len : UInt32
  sym : UInt32
  min : UInt32
  curr : UInt32
  drop : UInt32
  left : Int32
  used : UInt32
  rhuff : UInt16
  huff : UInt32
  low : UInt32
  here : Code
  next : CodePtr
  count : Array UInt16
  ret : Option Int32

/-- `int Z_INTERNAL zng_inflate_table(codetype type, uint16_t *lens, unsigned codes, code * *table,
unsigned *bits, uint16_t *work)` (`inftrees.c:145-421`). Returns `(result, *table, *bits)`. -/
def zng_inflate_table (type : UInt32) (lens : WPtr) (codes : UInt32) (table : CodePtr) (bits : UInt32)
    (work : WPtr) : M (Int32 × CodePtr × UInt32) := do
  let mut table := table
  let count ← count_lengths lens codes.toInt32
  let mut root := bits
  -- for (max = MAX_BITS; max >= 1; max--) if (count[max] != 0) break;
  let (max, _) ← cwhile
    (fun ((max, done) : UInt32 × Bool) => pure (!done && max >= 1, (max, done)))
    (fun ((max, _) : UInt32 × Bool) => do
      if (← aget count max.toNat) != 0 then pure (max, true) else pure (max - 1, false))
    (MAX_BITS, false)
  root := if root > max then max else root
  if max == 0 then
    let here : Code := ⟨1, 64, 0⟩
    stCode table 0 here
    table ← table.add 1
    stCode table 0 here
    table ← table.add 1
    return (0, table, 1)
  let (min, _) ← cwhile
    (fun ((min, done) : UInt32 × Bool) => pure (!done && min < max, (min, done)))
    (fun ((min, _) : UInt32 × Bool) => do
      if (← aget count min.toNat) != 0 then pure (min, true) else pure (min + 1, false))
    ((1 : UInt32), false)
  root := if root > min then root else min
  -- check for an over-subscribed or incomplete set of lengths
  let (left, _, over) ← cwhile
    (fun ((left, len, over) : Int32 × UInt32 × Bool) => pure (!over && len <= MAX_BITS, (left, len, over)))
    (fun ((left, len, _) : Int32 × UInt32 × Bool) => do
      let left ← chkI32 (left.toInt * 2)
      let left ← chkI32 (left.toInt - ((← aget count len.toNat).toNat : Int))
      if left < 0 then pure (left, len, true) else pure (left, len + 1, false))
    ((1 : Int32), (1 : UInt32), false)
  if over then return (-1, table, bits)
  if left > 0 && (type == CODES || max != 1) then return (-1, table, bits)
  -- generate offsets into symbol table for each length for sorting
  let mut offs : Array UInt16 := Array.replicate 16 0
  offs ← aset offs 1 0
  for len in [1:15] do
    offs ← aset offs (len + 1) ((← aget offs len) + (← aget count len))
  -- sort symbols by length, by symbol order within each length
  let (offs2, _) ← cwhile
    (fun ((offs, sym) : Array UInt16 × UInt32) => pure (sym < codes, (offs, sym)))
    (fun ((offs, sym) : Array UInt16 × UInt32) => do
      let l ← Ptr.index lens (Int.ofNat sym.toNat)
      if l != 0 then
        let o ← aget offs l.toNat
        Ptr.store (← work.add (Int.ofNat o.toNat)) sym.toUInt16
        let offs ← aset offs l.toNat (o + 1)
        pure (offs, sym + 1)
      else pure (offs, sym + 1))
    (offs, 0)
  let _ := offs2
  -- set up for code type
  let (base, extra, match_) : U16Src × U16Src × UInt32 :=
    if type == CODES then (.ptr work, .ptr work, 20)
    else if type == LENS then (.st lbase, .st lext, 257)
    else if type == DISTS then (.st dbase, .st dext, 0)
    else (.st #[], .st #[], 0)
  let used : UInt32 ← shl32 1 root
  let mask := used - 1
  if (type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS) then
    return (1, table, bits)
  let t0 : TL := ⟨min, 0, min, root, 0, left, used, 0, 0, (-1 : Int32).toUInt32, ⟨0, 0, 0⟩, table, count, none⟩
  let t ← cwhile
    (fun (t : TL) => pure (t.ret.isNone, t))
    (fun (t : TL) => do
      -- create table entry
      let mut here : Code := { t.here with bits := (t.len - t.drop).toUInt8 }
      let _ := here
      let ws ← Ptr.index work (Int.ofNat t.sym.toNat)
      if ws.toUInt32 >= match_ then
        let op := (← extra.at (ws.toUInt32 - match_).toNat).toUInt32
        here := { here with op := COMBINE_OP op here.bits }
        here := { here with bits := COMBINE_BITS here.bits op }
        let v ← base.at (ws.toUInt32 - match_).toNat
        here := { here with val := v }
      else if ws.toUInt32 + 1 < match_ then
        here := { here with op := 0, val := ws }
      else
        here := { here with op := 32 + 64, val := 0 }
      -- replicate for those indices with low len bits equal to huff
      let incr ← shl32 1 (t.len - t.drop)
      let fill ← shl32 1 t.curr
      let min := fill
      let here_u32 := packCode here
      let base_ptr ← t.next.add (Int.ofNat (← shr32 t.huff t.drop).toNat)
      let step4 := incr <<< 2
      let fill ← cwhile
        (fun (fill : UInt32) => pure (fill >= step4, fill))
        (fun (fill : UInt32) => do
          stCode base_ptr (Int.ofNat (fill - 1 * incr).toNat) (unpackCode here_u32)
          stCode base_ptr (Int.ofNat (fill - 2 * incr).toNat) (unpackCode here_u32)
          stCode base_ptr (Int.ofNat (fill - 3 * incr).toNat) (unpackCode here_u32)
          stCode base_ptr (Int.ofNat (fill - 4 * incr).toNat) (unpackCode here_u32)
          pure (fill - step4))
        fill
      let _ ← cwhile
        (fun (fill : UInt32) => pure (fill != 0, fill))
        (fun (fill : UInt32) => do
          let fill := fill - incr
          stCode base_ptr (Int.ofNat fill.toNat) (unpackCode here_u32)
          pure fill)
        fill
      -- backwards increment the len-bit code huff
      let rhuff := (t.rhuff.toUInt32 + (← shr32 0x8000 (t.len - 1))).toUInt16
      let huff := (zng_bitreverse16 rhuff).toUInt32
      -- go to next symbol, update count, len
      let sym := t.sym + 1
      let c ← aget t.count t.len.toNat
      let count ← aset t.count t.len.toNat (c - 1)
      let mut len := t.len
      if c - 1 == 0 then
        if len == max then
          return { t with here, min, rhuff, huff, sym, count, ret := some 0 }
        len := (← Ptr.index lens (Int.ofNat (← Ptr.index work (Int.ofNat sym.toNat)).toNat)).toUInt32
      -- create new sub-table if needed
      if len > root && (huff &&& mask) != t.low then
        let drop := if t.drop == 0 then root else t.drop
        let next ← t.next.add (Int.ofNat min.toNat)
        let curr := len - drop
        let left ← chkI32 (← shl32 1 curr).toNat
        let (curr, _, _) ← cwhile
          (fun ((curr, left, done) : UInt32 × Int32 × Bool) => pure (!done && curr + drop < max, (curr, left, done)))
          (fun ((curr, left, _) : UInt32 × Int32 × Bool) => do
            let left ← chkI32 (left.toInt - ((← aget count (curr + drop).toNat).toNat : Int))
            if left <= 0 then pure (curr, left, true)
            else pure (curr + 1, ← chkI32 (left.toInt * 2), false))
          (curr, left, false)
        let used := t.used + (← shl32 1 curr)
        if (type == LENS && used > ENOUGH_LENS) || (type == DISTS && used > ENOUGH_DISTS) then
          return { t with ret := some 1 }
        let low := huff &&& mask
        let slot ← table.add (Int.ofNat low.toNat)
        let e : Code ← Ptr.load slot
        Ptr.store slot { e with op := curr.toUInt8 }
        let e : Code ← Ptr.load slot
        Ptr.store slot { e with bits := root.toUInt8 }
        let d ← Ptr.diff next table
        let e : Code ← Ptr.load slot
        Ptr.store slot { e with val := d.toUInt64.toUInt16 }
        return { t with len, sym, min, curr, drop, used, rhuff, huff, low, here, next, count }
      return { t with len, sym, min, rhuff, huff, here, count })
    t0
  if t.ret == some 1 then return (1, table, bits)
  if t.huff != 0 then
    let here : Code := ⟨(t.len - t.drop).toUInt8, 64, 0⟩
    stCode t.next (Int.ofNat t.huff.toNat) here
  table ← table.add (Int.ofNat t.used.toNat)
  return (0, table, root)

end ZlibNg.Inftrees
