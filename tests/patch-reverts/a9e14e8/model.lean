import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«deflate.c»
import DiffTest.Heap

/-! a9e14e8: the calls of `trigger.c` on the translation, each in its own run as in `trigger.c`.
It prints the lines `trigger.c` prints, or the fault of each run. -/

open C DiffTest

def stream : M ZStreamPtr := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  return s

def version : M BPtr := allocBytesRO ("1.4".toUTF8.data.push 0)

def report (name : String) (r : Except Fault (Int32 × Heap)) : String :=
  match r with
  | .ok (rc, _) => s!"{name}={rc.toInt}"
  | .error f => showFault f

def main : IO Unit := do
  IO.println <| report "inflateInit2" <| C.run (do
    Zlib.Inflate.inflateInit2_ (← stream) (-2147483648) (← version) 112) fullHeap
  IO.println <| report "deflateInit2" <| C.run (do
    Zlib.Deflate.deflateInit2_ (← stream) (-1) 8 (-2147483648) 8 0 (← version) 112) fullHeap
