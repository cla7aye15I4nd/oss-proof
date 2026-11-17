import ZlibF.Zlib.«infback.c»
import DiffTest.Heap

/-! 2333419: the calls of `trigger.c` on the translation. The heap's garbage oracle of `fullHeap`
gives 0 for every uninitialised field, as the zero-filled allocation of `trigger.c`. It prints the
line `trigger.c` prints, or the fault of the translation. -/

open C Zlib.Infback DiffTest
open Zlib.Inflate (wrZ)

def input : Array UInt8 := #[0x03, 0xe6, 0x73, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def calls : M String := do
  let inb ← allocBytes input
  let ctl ← allocBytes #[0, 0, 0, 0]       -- byte 0: input given; bytes 1..3: unused
  let outs ← allocBytes #[0, 0, 0, 0]      -- the output count, little-endian
  let inCb : InCb := fun d _ => do
    if (← index8 d 0) != 0 then return (0, .null)
    store8 d 1
    return (input.size.toUInt32, inb)
  let outCb : OutCb := fun _ _ len => do
    let mut n : UInt32 := 0
    for i in [0:4] do n := n ||| ((← index8 outs i).toUInt32 <<< (8 * i).toUInt32)
    n := n + len
    for i in [0:4] do store8 (← outs.add i) (n >>> (8 * i).toUInt32).toUInt8
    return 0
  let window ← allocBytes (Array.replicate 512 0)
  let s ← allocZStream
  stZStream s ZStream.zeroed
  let ver ← allocBytesRO ("1.4".toUTF8.data.push 0)
  let rc ← inflateBackInit_ s 9 window ver 112
  let r ← inflateBack s inCb ctl outCb ctl
  let z ← ldZStream s
  let mut msg := ""
  if z.msg == .null then msg := "-"
  else
    for i in [0:64] do
      let b ← index8 z.msg i
      if b == 0 then break
      msg := msg.push (Char.ofNat b.toNat)
  let mut n := 0
  for i in [0:4] do n := n + (← index8 outs i).toNat * 256 ^ i
  let e ← inflateBackEnd s
  return s!"init={rc.toInt} back={r.toInt} out={n} msg={msg} end={e.toInt}"

def main : IO Unit :=
  IO.println <| match C.run calls fullHeap with
    | .ok (s, _) => s
    | .error f => showFault f
