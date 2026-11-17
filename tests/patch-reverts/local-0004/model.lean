import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! local-0004: the calls of `trigger.c` on the translation and the file model. `/dev/zero` is a
file of zeros, and the `lseek` oracle of the file model plays the `lseek` of `/dev/zero`: the call
of the `gzseek` returns 0 without moving. It prints the line `trigger.c` prints, or the fault of the
translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzread Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let fd ← fsOpen "/dev/zero".toUTF8.data 0
  let mode ← allocBytesRO (cstr "r")
  let f ← gzdopen fd mode
  if f.isNone then return "gzdopen failed"
  let buf ← allocBytes (Array.replicate 16 0)
  let r1 ← gzread f buf 1
  modify fun w => { w with lseekChoice := fun m => if m = w.nos then .value 0 else .regular }
  let s ← gzseek f 9223372036854775807 SEEK_SET
  let r16 ← gzread f buf 16
  let err := (← ldS (castState f)).err
  let c ← gzclose f
  return s!"read1={r1.toInt} seek={s.toInt} read16={r16.toInt} err={err.toInt} close={c.toInt}"

def main : IO Unit :=
  let fs : Fs := ({} : Fs).put "/dev/zero".toUTF8.data (Array.replicate 65536 0)
  IO.println <| match (calls.run fs) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
