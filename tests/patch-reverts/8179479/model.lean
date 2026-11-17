import ZlibF.Zlib.«inflate.c»
import DiffTest.Heap

/-! 8179479: the calls of `trigger.c` on the translation. It prints the line `trigger.c` prints, or
the fault of the translation. -/

open C Zlib.Inflate DiffTest

def first : Array UInt8 := #[0x00, 0x00, 0xff, 0xff,
  0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x57, 0xc8, 0x40, 0x90, 0x00]

def second : Array UInt8 := #[
  0x78, 0x9c, 0x0b, 0xc9, 0x48, 0x55, 0x28, 0x2c, 0xcd, 0x4c, 0xce, 0x56, 0x48, 0x2a,
  0xca, 0x2f, 0xcf, 0x53, 0x48, 0xcb, 0xaf, 0x50, 0xc8, 0x2a, 0xcd, 0x2d, 0x28, 0x56,
  0xc8, 0x2f, 0x4b, 0x2d, 0x52, 0x28, 0x01, 0x4a, 0xe7, 0x24, 0x56, 0x55, 0x2a, 0xa4,
  0xe4, 0xa7, 0xeb, 0x29, 0x84, 0xd0, 0x4c, 0x31, 0x00, 0xf9, 0x3c, 0x30, 0x76]

def calls : M String := do
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let in1 ← allocBytesRO first
  let in2 ← allocBytesRO second
  let out ← allocBytes (Array.replicate 200 0)
  let rc ← inflateInit2_ s 0 ver 112
  wrZ s fun z => { z with next_in := in1, avail_in := first.size.toUInt32 }
  let sync ← inflateSync s
  wrZ s fun z => { z with next_out := out, avail_out := 200 }
  let r1 ← inflate s Z_NO_FLUSH
  let o1 := (← ldZStream s).total_out
  let reset ← inflateReset s
  wrZ s fun z => { z with next_in := in2, avail_in := (second.size - 4).toUInt32, next_out := out, avail_out := 200 }
  let r2 ← inflate s Z_NO_FLUSH
  let o2 := (← ldZStream s).total_out
  wrZ s fun z => { z with avail_in := 4 }
  let r3 ← inflate s Z_NO_FLUSH
  let _ ← inflateEnd s
  return s!"init={rc.toInt} sync={sync.toInt} raw={r1.toInt},{o1.toNat} reset={reset.toInt} zlib={r2.toInt},{o2.toNat} check={r3.toInt}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
