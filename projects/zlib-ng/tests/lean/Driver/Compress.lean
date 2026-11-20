import ZlibNgF.ZlibNg.«compress.c»
import DiffTest.Common

/-!
Lean side of the differential test for `compressBound` and `compressBound_z` (`compress.c`). It calls the translation in
`ZlibNgF/ZlibNg/compress.c.lean` (the module the proofs are about), nothing else.
-/

open DiffTest

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "compressBound", [n] => do
    return showResult (C.run (ZlibNg.Compress.compressBound (← parseU64 n)) C.Heap.empty)
  | "compressBound_z", [n] => do
    return showResult (C.run (ZlibNg.Compress.compressBound_z (← parseU64 n)) C.Heap.empty)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
