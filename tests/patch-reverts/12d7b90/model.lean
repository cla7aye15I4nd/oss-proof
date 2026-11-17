import ZlibF.Zlib.«deflate.c»
import DiffTest.Heap

/-! 12d7b90: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Deflate DiffTest

def calls : M String := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let rc ← deflateInit2_ s (-1) 8 15 1 0 ver 112
  let mut ok := 0
  let mut last : Int32 := 0
  for _ in [0:300] do
    last ← deflatePrime s 16 0x1234
    if last != 0 then break
    ok := ok + 1
  let e ← deflateEnd s
  return s!"init={rc.toInt} primed={ok} last={last.toInt} end={e.toInt}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
