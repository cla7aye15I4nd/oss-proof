import ZlibNgF.ZlibNg.«adler32.c»
import DiffTest.Common

/-!
Lean side of the differential test for `adler32.c` and `arch/generic/adler32_c.c`. It calls the
translation in `ZlibNgF/ZlibNg/adler32.c.lean` (the module the proofs are about), nothing else.
-/

open DiffTest

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "adler32_z", [a, b] => do
    let a ← parseU64 a
    let buf ← parseBuf b
    if bufLen buf ≥ 2 ^ 64 then throw "length does not fit size_t"
    return withBuf C.Heap.empty buf fun p len => ZlibNg.Adler32.adler32_z a p (UInt64.ofNat len)
  | "adler32", [a, b] => do
    let a ← parseU64 a
    let buf ← parseBuf b
    if bufLen buf ≥ 2 ^ 32 then throw "length does not fit uInt"
    return withBuf C.Heap.empty buf fun p len => ZlibNg.Adler32.adler32 a p (UInt32.ofNat len)
  | "adler32_combine", [a1, a2, l] => do
    let r := ZlibNg.Adler32.adler32_combine (← parseU64 a1) (← parseU64 a2) (← parseI64 l)
    return showResult (C.run r C.Heap.empty)
  | "adler32_combine64", [a1, a2, l] => do
    let r := ZlibNg.Adler32.adler32_combine64 (← parseU64 a1) (← parseU64 a2) (← parseI64 l)
    return showResult (C.run r C.Heap.empty)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
