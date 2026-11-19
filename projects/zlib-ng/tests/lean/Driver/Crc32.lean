import ZlibNgF.ZlibNg.«crc32.c»
import DiffTest.Common

/-!
Lean side of the differential test for `crc32.c`, `arch/generic/crc32_braid_c.c` and
`crc32_braid_comb.c`. It calls the translations in `ZlibNgF/ZlibNg/` (the modules the proofs are
about), nothing else.
-/

open DiffTest

/-- The heap of the test: nothing allocated, the static tables of `crc32_braid_tbl.h` set. -/
def heap0 : C.Heap := ZlibNg.Crc32.initStatics C.Heap.empty

def showM (m : C.M UInt64) : String := showResult (C.run m heap0)

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "crc32_z", [a, b] => do
    let a ← parseU64 a
    let buf ← parseBuf b
    if bufLen buf ≥ 2 ^ 64 then throw "length does not fit size_t"
    return withBuf heap0 buf fun p len => ZlibNg.Crc32.crc32_z a p (UInt64.ofNat len)
  | "crc32", [a, b] => do
    let a ← parseU64 a
    let buf ← parseBuf b
    if bufLen buf ≥ 2 ^ 32 then throw "length does not fit uInt"
    return withBuf heap0 buf fun p len => ZlibNg.Crc32.crc32 a p (UInt32.ofNat len)
  | "crc32_combine", [a1, a2, l] => do
    return showM (ZlibNg.Crc32Comb.crc32_combine (← parseU64 a1) (← parseU64 a2) (← parseI64 l))
  | "crc32_combine64", [a1, a2, l] => do
    return showM (ZlibNg.Crc32Comb.crc32_combine64 (← parseU64 a1) (← parseU64 a2) (← parseI64 l))
  | "crc32_combine_gen", [l] => do return showM (ZlibNg.Crc32Comb.crc32_combine_gen (← parseI64 l))
  | "crc32_combine_gen64", [l] => do return showM (ZlibNg.Crc32Comb.crc32_combine_gen64 (← parseI64 l))
  | "crc32_combine_op", [a1, a2, op] => do
    return showM (ZlibNg.Crc32Comb.crc32_combine_op (← parseU64 a1) (← parseU64 a2) (← parseU64 op))
  | "get_crc_table", [] =>
    -- read the 256 entries through the returned pointer
    let m : C.M (Array UInt32) := do
      let p ← ZlibNg.Crc32.get_crc_table
      let mut a : Array UInt32 := #[]
      for i in [0:256] do
        a := a.push (← C.Ptr.index p i)
      pure a
    match C.run m heap0 with
    | .ok (a, _) => .ok (" ".intercalate (a.toList.map fun x => toString x.toNat))
    | .error f => .ok (showFault f)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
