import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! 7dd6aa7: the calls of `trigger.c` on the translation and the file model. `gzgetc` here is the
function, as the macro of `zlib.h` reaches it when nothing is buffered. It prints the line
`trigger.c` prints, or the fault of the translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzlib Zlib.Gzread Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let path ← allocBytesRO (cstr "raw.dat")
  let mode ← allocBytesRO (cstr "rb")
  let f ← gzopen path mode
  if f.isNone then return "gzopen failed"
  let u ← gzungetc 120 f
  let g ← gzgetc f
  let buf ← allocBytes (Array.replicate 8 0)
  let n ← gzread f buf 7
  let mut s := ""
  for i in [0:8] do
    let b ← index8 buf i
    if b == 0 then break
    s := s.push (Char.ofNat b.toNat)
  let c ← gzclose f
  return s!"ungetc={u.toInt} getc={g.toInt} read={n.toInt}:{s} close={c.toInt}"

def main : IO Unit :=
  let fs : Fs := ({} : Fs).put "raw.dat".toUTF8.data "abc".toUTF8.data
  IO.println <| match (calls.run fs) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
