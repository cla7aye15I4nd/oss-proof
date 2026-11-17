import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! local-0002: the calls of `trigger.c` on the translation and the file model. It prints the line
`trigger.c` prints, or the fault of the translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzlib Zlib.Gzread Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let path ← allocBytesRO (cstr "raw.dat")
  let mode ← allocBytesRO (cstr "rb")
  let f ← gzopen path mode
  if f.isNone then return "gzopen failed"
  let u ← gzungetc 81 f
  let s ← gzseek f 1 SEEK_CUR
  let c ← gzclose f
  return s!"ungetc={u.toInt} seek={s.toInt} close={c.toInt}"

def main : IO Unit :=
  let fs : Fs := ({} : Fs).put "raw.dat".toUTF8.data "abc".toUTF8.data
  IO.println <| match (calls.run fs) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
