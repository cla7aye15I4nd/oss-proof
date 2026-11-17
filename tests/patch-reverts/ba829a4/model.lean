import ZlibF.Zlib.«crc32.c»
import DiffTest.Heap

/-! ba829a4: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. With the revert the loop of `x2nmodp` would end in `Fault.outOfFuel`
only after 2^64 iterations: the run does not return. -/

open C Zlib.Crc32 DiffTest

def calls : M String := do
  let abc ← allocBytesRO "abc".toUTF8.data
  let def_ ← allocBytesRO "def".toUTF8.data
  let c1 ← crc32 0 abc 3
  let c2 ← crc32 0 def_ 3
  let c ← crc32_combine c1 c2 (-1)
  return s!"combine={c.toNat}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
