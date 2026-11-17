import ZlibF.Zlib.«inflate.c»
import DiffTest.Heap

/-! e7bb978: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Inflate DiffTest

def stream : Array UInt8 := #[0x4a, 0x04, 0x2c, 0x29, 0x39, 0x25, 0x35, 0x2d, 0x3d, 0x23,
  0x33, 0x2b, 0x3b, 0x27, 0x37, 0x2f, 0xbf, 0x00, 0x00]

def calls : M String := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let inp ← allocBytes (stream.extract 4 stream.size)
  let out ← allocBytes (Array.replicate 1000 0)
  let rc ← inflateInit2_ s (-15) ver 112
  let p1 ← inflatePrime s 16 (Int32.ofNat (stream[0]!.toNat ||| stream[1]!.toNat <<< 8))
  let p2 ← inflatePrime s 16 (Int32.ofNat (stream[2]!.toNat ||| stream[3]!.toNat <<< 8))
  let n := (stream.size - 4).toUInt32
  wrZ s fun z => { z with next_in := inp, avail_in := n, next_out := out, avail_out := 1000 }
  let r ← inflate s Z_NO_FLUSH
  let z ← ldZStream s
  let mut ok := r == Z_STREAM_END && z.total_out == 16
  let want := "abcdefghijklmnop".toUTF8.data
  for i in [0:16] do
    ok := ok && (← index8 out i) == want[i]!
  let _ ← inflateEnd s
  return s!"init={rc.toInt} prime={p1.toInt},{p2.toInt} inflate={r.toInt} out={z.total_out.toNat} output {if ok then "ok" else "WRONG"}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
