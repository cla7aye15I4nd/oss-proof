import ZlibNgF.Proof.«inftrees.c.base»

/-!
# The table-filling loop of `zng_inflate_table`: verbatim copies of its pieces (`ZlibNgF`)

`tblBody` is the body of the loop, copied verbatim from the translation (`ZlibNg/inftrees.c.lean`), so that the
loop of `zng_inflate_table` is definitionally `cwhile (fun t => pure (t.ret.isNone, t)) (tblBody ...)`. `tblCont`
is the part of the body after the entry `here` is made, and `tblSub` the part after `len` is updated; the
`do`-notation of the body passes them `here` and `len` through join points, which unfold to these definitions.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Inftrees
open C ZlibNg.Inftrees ZlibNg.InflateP

/-- The body of the table-filling loop. -/
def tblBody (type : UInt32) (lens work : WPtr) (table : CodePtr) (base extra : U16Src)
    (match_ max root mask : UInt32) (t : TL) : M TL := do
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
  return { t with len, sym, min, rhuff, huff, here, count }

/-- The body after the entry `here` is made. -/
def tblCont (type : UInt32) (lens work : WPtr) (table : CodePtr) (max root mask : UInt32) (t : TL)
    (here : Code) : M TL := do
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
  return { t with len, sym, min, rhuff, huff, here, count }

/-- The body after `len` is updated. -/
def tblSub (type : UInt32) (table : CodePtr) (max root mask : UInt32) (t : TL) (here : Code)
    (min : UInt32) (rhuff : UInt16) (huff sym : UInt32) (count : Array UInt16) (len : UInt32) : M TL := do
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
  return { t with len, sym, min, rhuff, huff, here, count }

end ZlibNgF.Proof.Inftrees
