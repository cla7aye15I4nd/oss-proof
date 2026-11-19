import ZlibNgF.ZlibNg.«infback.c»
import DiffTest.Common

/-!
Lean side of the differential test for `infback.c` (format: `tests/c/infback.c`). It runs the same calls on the
translation in `ZlibNgF/ZlibNg/infback.c.lean` with call-backs that do what the C call-backs do: `in()` frees the block
it handed out before and hands out the next bytes in a fresh block of the exact size; `out()` appends the window bytes
it is given to a log. The call-backs keep their counters in heap blocks of their own (they are caller code running on
the shared heap).
-/

open DiffTest C

/-- The starting heap: a garbage oracle with no zero pattern, so that a read of an uninitialised local or of fresh
`malloc` memory shows up as a difference from the C. -/
def junkHeap : Heap :=
  { Heap.empty with
    garbage := fun a b => (UInt64.ofNat (a * 0x9E3779B97F4A7C15 + b * 0xBF58476D1CE4E5B9 + 0x94D049BB133111EB)) ^^^ 0x5555555555555555 }

/-- A new heap block holding `a` (a `malloc` of the exact size, filled; at least one byte). -/
def mkBlock (a : Array UInt8) : M BPtr := fun h =>
  let b := h.nextBlk
  let a' := if a.size == 0 then #[0] else a
  .ok (.ref (.heap b) 0, { h with bytes := upd h.bytes b (some a'), nextBlk := b + 1, nalloc := h.nalloc + 1 })

def blockNo (p : BPtr) : Nat := match p with | .ref (.heap b) _ => b | _ => 0
def offOf (p : BPtr) : Nat := match p with | .ref _ o => o | .null => 0

/-- The bytes of the caller block `b` (driver bookkeeping). -/
def getBlk (b : Nat) : M (Array UInt8) := fun h =>
  match h.bytes b with
  | some a => .ok (a, h)
  | none => .error (.ub "driver: dead bookkeeping block")

def setBlk (b : Nat) (a : Array UInt8) : M Unit := fun h => .ok ((), { h with bytes := upd h.bytes b (some a) })

def word (a : Array UInt8) (i : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc + a[8 * i + k]!.toNat * 256 ^ k) 0

def setWord (a : Array UInt8) (i n : Nat) : Array UInt8 :=
  (List.range 8).foldl (fun a k => a.set! (8 * i + k) (UInt8.ofNat (n / 256 ^ k))) a

def hexOf (a : Array UInt8) : String :=
  if a.isEmpty then "-" else
  String.join (a.toList.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

/-- A C string (at most 255 bytes). -/
def readStr (p : BPtr) : M String := do
  if p == .null then return "-"
  let mut a : Array UInt8 := #[]
  for i in [0:256] do
    let b ← index8 p i
    if b == 0 then break
    a := a.push b
  return String.fromUTF8! (ByteArray.mk a)

/-- `in()`: state block `stB` holds the words `pos`, `ci`, `calls`, `cur + 1` (0: no block). -/
def inCb (data : Array UInt8) (limit : Nat) (chunks : Array Nat) (stB : Nat) : ZlibNg.Infback.InCb :=
  fun _ cur => do
    let st ← getBlk stB
    let pos := word st 0
    let ci := word st 1
    let calls := word st 2 + 1
    let curB := word st 3
    if curB != 0 then freeB (.ref (.heap (curB - 1)) 0)
    let end_ := Nat.min limit data.size
    if pos ≥ end_ then
      setBlk stB (setWord (setWord st 2 calls) 3 0)
      return (0, cur)
    let mut n := end_ - pos
    let mut ci := ci
    if chunks.size > 0 then
      n := Nat.min n chunks[ci % chunks.size]!
      ci := ci + 1
    let blk ← mkBlock (data.extract pos (pos + n))
    setBlk stB (setWord (setWord (setWord (setWord st 0 (pos + n)) 1 ci) 2 calls) 3 (blockNo blk + 1))
    return (n.toUInt32, blk)

/-- `out()`: state block `stB` holds the word `calls`; the window bytes go to the log block `accB`, the lengths to
the block `lensB` (one word each). -/
def outCb (abortAt : Int) (stB accB lensB : Nat) : ZlibNg.Infback.OutCb :=
  fun _ buf len => do
    let st ← getBlk stB
    let calls := word st 0 + 1
    setBlk stB (setWord st 0 calls)
    let lens ← getBlk lensB
    setBlk lensB (setWord (lens ++ Array.replicate 8 0) (lens.size / 8) len.toNat)
    let mut acc ← getBlk accB
    for i in [0:len.toNat] do
      acc := acc.push (← index8 buf i)
    setBlk accB acc
    return if (calls : Int) == abortAt then 1 else 0

def runBack (wbits : Int32) (first : String) (chunks : Array Nat) (limit : Option Nat) (abortAt : Int)
    (calls : Nat) (data : Array UInt8) : M String := do
  let limit := limit.getD data.size
  let window ← mkBlock (Array.replicate (2 ^ wbits.toInt.toNat) 0)
  let s ← newStream {}
  let ver ← strLitRef "1.3.2.zlib-ng"
  let r ← ZlibNg.Infback.inflateBackInit_ s wbits window ver 112
  let mut acc := s!"init:{r}"
  if r != 0 then return acc
  for _ in [0:calls] do
    let inSt ← mkBlock (Array.replicate 32 0)
    let outSt ← mkBlock (Array.replicate 8 0)
    let accB ← mkBlock #[]
    setBlk (blockNo accB) #[]
    let lensB ← mkBlock #[]
    setBlk (blockNo lensB) #[]
    let mut fb : BPtr := .null
    let z ← ldStream s
    if first == "null" then
      stStream s { z with next_in := .null, avail_in := 12345 }
    else if first == "z" then
      fb ← mkBlock #[0]
      stStream s { z with next_in := fb, avail_in := 0 }
    else
      let f := Nat.min (Nat.min (first.toNat?.getD 0) data.size) limit
      fb ← mkBlock (data.extract 0 f)
      stStream s { z with next_in := fb, avail_in := f.toUInt32 }
      setBlk (blockNo inSt) (setWord (Array.replicate 32 0) 0 f)
    let r ← ZlibNg.Infback.inflateBack s (inCb data limit chunks (blockNo inSt)) inSt
      (outCb abortAt (blockNo outSt) (blockNo accB) (blockNo lensB)) outSt
    let z ← ldStream s
    let ist ← getBlk (blockNo inSt)
    let nin :=
      if z.next_in == .null then "N"
      else if word ist 3 != 0 then s!"c{word ist 2}+{offOf z.next_in}"
      else s!"f+{offOf z.next_in}"
    let lens ← getBlk (blockNo lensB)
    let lensS := if lens.isEmpty then "-" else
      ",".intercalate ((List.range (lens.size / 8)).map fun i => toString (word lens i))
    let bytes ← getBlk (blockNo accB)
    acc := acc ++ s!" back:{r}:{nin}:{z.avail_in}:{← readStr z.msg}:{word ist 2}:{lensS}:{hexOf bytes}"
    if word ist 3 != 0 then freeB (.ref (.heap (word ist 3 - 1)) 0)
  acc := acc ++ s!" end:{← ZlibNg.Infback.inflateBackEnd s}"
  return acc

def runInit (wbits : Int32) (wnull : Bool) (ver : Option String) (size : Int32) : M String := do
  let window ← if wnull then pure .null else mkBlock (Array.replicate (2 ^ 15) 0)
  let vp ← match ver with
    | none => pure .null
    | some v => mkBlock (v.toUTF8.data.push 0)
  let s ← newStream {}
  let r ← ZlibNg.Infback.inflateBackInit_ s wbits window vp size
  let e ← if r == 0 then ZlibNg.Infback.inflateBackEnd s else pure 99
  return s!"init:{r} end:{e}"

def runMisc : M String := do
  let s ← newStream {}
  let inNone : ZlibNg.Infback.InCb := fun _ cur => pure (0, cur)
  let outNone : ZlibNg.Infback.OutCb := fun _ _ _ => pure 0
  let a ← ZlibNg.Infback.inflateBack none inNone .null outNone .null
  let b ← ZlibNg.Infback.inflateBackEnd none
  let c ← ZlibNg.Infback.inflateBack s inNone .null outNone .null
  let d ← ZlibNg.Infback.inflateBackEnd s
  return s!"misc:{a}:{b}:{c}:{d}"

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "back", [w, first, ch, lim, ab, calls, d] => do
    let wbits := Int32.ofInt (← parseI64 w).toInt
    let chunks ← if ch == "-" then pure #[] else (ch.splitOn ",").toArray.mapM parseNat
    let limit ← if lim == "-" then pure none else do pure (some (← parseNat lim))
    let abortAt ← if ab == "-" then pure (-1) else do pure (← parseI64 ab).toInt
    let data ← if d == "-" then pure #[] else parseHex d
    match C.run (runBack wbits first chunks limit abortAt (← parseNat calls) data) junkHeap with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | "init", [w, wn, v, sz] => do
    let wbits := Int32.ofInt (← parseI64 w).toInt
    let sz := Int32.ofInt (← parseI64 sz).toInt
    match C.run (runInit wbits (wn == "null") (if v == "null" then none else some v) sz) junkHeap with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | "misc", [] =>
    match C.run runMisc junkHeap with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
