import ZlibF.Zlib.«inflate.c»
import DiffTest.Heap

/-! local-0001: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Inflate DiffTest

def input : Array UInt8 := #[0x78, 0x01, 0x73, 0x74, 0x1c, 0x58, 0x00, 0x00, 0x31, 0x38, 0x20, 0x81]

def calls : M String := do
  let src ← allocZStream
  stZStream src ZStream.zeroed
  let dst ← allocZStream
  stZStream dst ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let inp ← allocBytesRO input
  let out ← allocBytes (Array.replicate 128 0)
  let rc ← inflateInit_ src ver 112
  wrZ src fun z => { z with next_in := inp, avail_in := input.size.toUInt32, next_out := out, avail_out := 7 }
  let r1 ← inflate src Z_NO_FLUSH
  let rcopy ← inflateCopy dst src
  let _ ← inflateEnd src
  wrZ dst fun z => { z with avail_out := 128 - 7 }
  let r2 ← inflate dst Z_NO_FLUSH
  let z ← ldZStream dst
  let mut ok := r2 == Z_STREAM_END && z.total_out == 128
  for i in [0:128] do
    ok := ok && (← index8 out i) == 65
  let _ ← inflateEnd dst
  return s!"init={rc.toInt} inflate={r1.toInt} copy={rcopy.toInt} finish={r2.toInt} output {if ok then "ok" else "WRONG"}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
