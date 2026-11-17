import ZlibF.Zlib.«gzclose.c»
import DiffTest.Heap

/-! df84af2: the calls of `trigger.c` on the translation and the file model. The write oracle of
the model plays the replaced `write()`: the first write of the large `gzwrite` fails with `EAGAIN`.
It prints the line `trigger.c` prints, or the fault of the translation. -/

open C DiffTest Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite Zlib.Gzclose

def cstr (s : String) : Array UInt8 := s.toUTF8.data.push 0

def calls : G String := do
  let path ← allocBytesRO (cstr "out.dat")
  let mode ← allocBytesRO (cstr "wT")
  let f ← gzopen path mode
  if f.isNone then return "gzopen failed"
  let b ← gzbuffer f 64
  let big ← allocBytes (Array.replicate 100 65)
  modify fun w => { w with writeChoice := fun m => if m = w.nos then .fail EAGAIN else .regular }
  let w1 ← gzwrite f big 100
  let x ← allocBytesRO "x".toUTF8.data
  let w2 ← gzwrite f x 1
  let c ← gzclose f
  freeB big
  let size : Int := match (← get).get? "out.dat".toUTF8.data with
    | some d => d.size
    | none => -1
  return s!"buffer={b.toInt} write100={w1.toInt} write1={w2.toInt} close={c.toInt} file={size}"

def main : IO Unit :=
  IO.println <| match (calls.run {}) fullHeap with
    | .ok ((s, _), _) => s
    | .error f => showFault f
