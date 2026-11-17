import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! e3dc0a8: the calls of `trigger.c` on the translation and the file model. It prints the line
`trigger.c` prints, or the fault of the translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzlib Zlib.Gzread Zlib.Gzwrite Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let path ← allocBytesRO (cstr "out.gz")
  let f ← gzopen path (← allocBytesRO (cstr "w"))
  if f.isNone then return "gzopen failed"
  -- vsnprintf is an external call: its oracle gets the output glibc gives, from the model's formatter
  let fmt ← allocBytesRO (cstr "hello")
  let text ← formatBytes (← cstring fmt) []
  modify fun w => { w with
    printfRet := fun m => if m == w.nprintf then Int32.ofNat text.size else w.printfRet m,
    printfOut := fun m => if m == w.nprintf then text else w.printfOut m }
  let p ← gzprintf f fmt []
  let c ← gzclose f
  let r ← gzopen path (← allocBytesRO (cstr "r"))
  let buf ← allocBytes (Array.replicate 16 0)
  let n ← if r.isNone then pure (-1) else gzread r buf 15
  if !r.isNone then let _ ← gzclose r
  let mut s := ""
  for i in [0:16] do
    let b ← index8 buf i
    if b == 0 then break
    s := s.push (Char.ofNat b.toNat)
  return s!"printf={p.toInt} close={c.toInt} read={n.toInt}:{s}"

def main : IO Unit :=
  IO.println <| match (calls.run {}) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
