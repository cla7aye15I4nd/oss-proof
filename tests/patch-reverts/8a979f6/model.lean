import ZlibF.Zlib.«deflate.c»
import DiffTest.Heap

/-! 8a979f6: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Deflate DiffTest

def calls : M String := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let out ← allocBytes (Array.replicate 100 0)
  let hello ← allocBytesRO "hello".toUTF8.data
  let rc ← deflateInit_ s (-1) ver 112
  zwr s fun z => { z with next_out := out, avail_out := 100 }
  let r1 ← deflate s Z_NO_FLUSH
  zwr s fun z => { z with next_in := hello, avail_in := 5 }
  let r2 ← deflate s Z_FINISH
  let n := (← ldZStream s).total_out
  let e ← deflateEnd s
  return s!"init={rc.toInt} first={r1.toInt} finish={r2.toInt} out={n.toNat} end={e.toInt}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
