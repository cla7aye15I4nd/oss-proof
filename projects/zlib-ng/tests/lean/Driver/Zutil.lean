import ZlibNgF.ZlibNg.«zutil.c»
import DiffTest.Common

/-!
Lean side of the differential test for `zutil.c`. It calls the translation in
`ZlibNgF/ZlibNg/zutil.c.lean` (the module the proofs are about), nothing else.
-/

open DiffTest

/-- The text of a `const char *` result, read byte by byte from the object it points into (at most 255
bytes before the terminating NUL). -/
def readStr (p : C.BPtr) : C.M String := do
  let mut a : Array UInt8 := #[]
  for i in [0:256] do
    let b ← C.index8 p i
    if b == 0 then break
    a := a.push b
  pure (String.fromUTF8! (ByteArray.mk a))

def showStr (m : C.M String) : String :=
  match C.run m C.Heap.empty with
  | .ok (s, _) => s!"[{s}]"
  | .error f => showFault f

def showText (r : Except C.Fault (String × C.Heap)) : String :=
  match r with
  | .ok (s, _) => s
  | .error f => showFault f

/-- Write `n` bytes `f i` through `p`, read them back and return their sum. -/
def fillAndSum (p : C.BPtr) (n : Nat) (f : Nat → UInt8) : C.M UInt64 := do
  for i in [0:n] do
    C.store8 (← p.add i) (f i)
  let mut sum : UInt64 := 0
  for i in [0:n] do
    sum := sum + (← C.load8 (← p.add i)).toUInt64
  pure sum

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "zlibVersion", [] => .ok (showStr (do readStr (← ZlibNg.Zutil.zlibVersion)))
  | "zlibCompileFlags", [] => .ok (showResult (C.run ZlibNg.Zutil.zlibCompileFlags C.Heap.empty))
  | "zError", [e] => do
    let n ← parseI64 e
    if n.toInt < -(2 ^ 31 : Int) || n.toInt ≥ 2 ^ 31 then throw "does not fit int"
    return showStr (do readStr (← ZlibNg.Zutil.zError (Int32.ofInt n.toInt)))
  | "zcalloc_free", [i, s] => do
    let items ← parseU32 i
    let size ← parseU32 s
    let n := items.toNat * size.toNat
    if n > 2 ^ 16 then throw "test sizes stay below 2^16 bytes"
    let m : C.M String := do
      let p ← ZlibNg.Zutil.zcalloc .null items size
      if p == .null then return "null"
      let sum ← fillAndSum p n fun i => (UInt64.ofNat i * 31 + 7).toUInt8
      ZlibNg.Zutil.zcfree .null p
      pure s!"{n} {sum}"
    return showText (C.run m C.Heap.empty)
  | "zng_alloc_aligned", [s, a] => do
    let size ← parseU32 s
    let align ← parseU32 a
    if align != 0 && size.toNat + align.toNat > 2 ^ 16 then throw "test blocks stay below 2^16 bytes"
    let m : C.M String := do
      let p ← ZlibNg.Zutil.zng_alloc_aligned size align
      if p == .null then return "null"
      let addr ← C.addrOf p
      let aligned := if addr % align.toUInt64 == 0 then 1 else 0
      let sum ← fillAndSum p size.toNat fun i => (UInt64.ofNat i * 13 + 5).toUInt8
      ZlibNg.Zutil.zng_free_aligned p
      pure s!"ok {aligned} {size.toNat} {sum}"
    return showText (C.run m C.Heap.empty)
  | "zng_free_aligned_null", [] =>
    return showText (C.run (do ZlibNg.Zutil.zng_free_aligned .null; pure "ok") C.Heap.empty)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
