import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! local-0003: the calls of `trigger.c` on the translation and the file model. The read oracle of
the model plays the replaced `read()`: from the first read after the 48 `gzgetc` calls, one byte,
then `EIO`. It prints the line `trigger.c` prints, or the fault of the translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let path ← allocBytesRO (cstr "raw.dat")
  let mode ← allocBytesRO (cstr "rb")
  let f ← gzopen path mode
  if f.isNone then return "gzopen failed"
  let b ← gzbuffer f 16
  let mut got := 0
  for _ in [0:48] do
    if (← gzgetc f) == 0 then got := got + 1
  modify fun w => { w with readChoice := fun m =>
    if m = w.nos then .bytes #[0] else if m > w.nos then .fail EIO else .regular }
  let buf ← allocBytes #[0]
  let n ← gzread f buf 1
  let err := (← ldS (castState f)).err
  let c ← gzclose f
  return s!"buffer={b.toInt} getc={got} read={n.toInt} err={err.toInt} close={c.toInt}"

def main : IO Unit :=
  let fs : Fs := ({} : Fs).put "raw.dat".toUTF8.data (Array.replicate 128 0)
  IO.println <| match (calls.run fs) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
