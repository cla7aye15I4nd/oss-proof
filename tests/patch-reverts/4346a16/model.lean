import ZlibF.Zlib.«deflate.c»
import DiffTest.Heap

/-! 4346a16: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Deflate DiffTest

def calls : M String := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let rc ← deflateInit_ s (-1) ver 112
  let p1 ← deflatePrime s 1 1
  let p2 ← deflatePrime s (-1) 0
  let e ← deflateEnd s
  return s!"init={rc.toInt} prime1={p1.toInt} prime-1={p2.toInt} end={e.toInt}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
