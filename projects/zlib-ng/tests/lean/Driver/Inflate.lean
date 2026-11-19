import ZlibNgF.ZlibNg.«inflate.c»
import DiffTest.Common

/-!
Lean side of the differential test for `inflate.c` (format: `tests/c/inflate.c`). It runs the same call sequence on
the translation in `ZlibNgF/ZlibNg/inflate.c.lean` and prints the same fields.
-/

open DiffTest C

/-- A new heap block holding `a` (a `malloc` of the exact size, filled). -/
def mkBlock (a : Array UInt8) : M BPtr := fun h =>
  let b := h.nextBlk
  let a' := if a.size == 0 then #[0] else a
  .ok (.ref (.heap b) 0, { h with bytes := upd h.bytes b (some a'), nextBlk := b + 1, nalloc := h.nalloc + 1 })

/-- The offset of a pointer into a block. -/
def offOf (p : BPtr) : Nat := match p with | .ref _ o => o | .null => 0

/-- The bytes of a block from 0 to `n`. -/
def blockBytes (p : BPtr) (n : Nat) : M (Array UInt8) := do
  let mut a : Array UInt8 := #[]
  for i in [0:n] do
    a := a.push (← index8 p i)
  return a

def hexOf (a : Array UInt8) : String :=
  if a.isEmpty then "-" else
  String.join (a.toList.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

/-- A C string (at most 255 bytes). -/
def readStr (p : BPtr) : M String := do
  if p == .null then return "-"
  let mut a : Array UInt8 := #[]
  for i in [0:256] do
    let b ← index8 p i
    if b == 0 then break
    a := a.push b
  return String.fromUTF8! (ByteArray.mk a)

/-- The decode loop of `tests/c/inflate.c`. -/
def decode (s : StreamPtr) (inB : BPtr) (inlen : Nat) (outB : BPtr) (outcap : Nat) (flush : Int32)
    (inchunk outchunk : Nat) (dict : BPtr) (dictlen : Nat) (havedict : Bool) : M String := do
  let z ← ldStream s
  stStream s { z with next_in := inB, next_out := outB }
  let mut acc := ""
  let mut havedict := havedict
  for _ in [0:20000] do
    let z ← ldStream s
    let inleft := inlen - offOf z.next_in
    let outleft := outcap - offOf z.next_out
    stStream s { z with avail_in := (Nat.min inleft inchunk).toUInt32, avail_out := (Nat.min outleft outchunk).toUInt32 }
    let ni := z.next_in
    let no := z.next_out
    let r ← ZlibNg.Inflate.inflate s flush
    let z ← ldStream s
    acc := acc ++ s!" {r}:{offOf z.next_in}:{z.avail_in}:{offOf z.next_out}:{z.avail_out}:{z.total_in}:{z.total_out}:{z.adler}:{z.data_type}:{← readStr z.msg}"
    if r == ZlibNg.Inflate.Z_NEED_DICT && havedict then
      let d ← ZlibNg.Inflate.inflateSetDictionary s dict dictlen.toUInt32
      acc := acc ++ s!" setdict:{d}"
      havedict := false
      continue
    if r != ZlibNg.Inflate.Z_OK && r != ZlibNg.Inflate.Z_BUF_ERROR then return acc
    if z.next_in == ni && z.next_out == no then return acc
  return acc ++ " LIMIT"

def parseHexOrDash (s : String) : Except String (Array UInt8) :=
  if s == "-" then pure #[] else parseHex s

def run (wbits flush : Int32) (inchunk outchunk outcap : Nat) (data dict : Array UInt8) (hasDict : Bool)
    (hdr : Option (Nat × Nat × Nat)) (reset : String) : M String := do
  let inB ← mkBlock data
  let dictB ← mkBlock dict
  let s ← newStream {}
  let ver ← strLitRef "1.3.2.zlib-ng"
  let r ← ZlibNg.Inflate.inflateInit2_ s wbits ver 112
  let mut acc := s!"init:{r}"
  if r != 0 then return acc
  let mut hp : HeaderPtr := none
  if let some (em, nm, cm) := hdr then
    let eb ← if em == 0 then pure .null else mkBlock (Array.replicate em 0xaa)
    let nb ← if nm == 0 then pure .null else mkBlock (Array.replicate nm 0xaa)
    let cb ← if cm == 0 then pure .null else mkBlock (Array.replicate cm 0xaa)
    let g0 : GzHeader := ⟨7, 7, 7, 7, eb, 7, em.toUInt32, nb, nm.toUInt32, cb, cm.toUInt32, 7, 7⟩
    hp ← newHeader g0
    acc := acc ++ s!" gethdr:{← ZlibNg.Inflate.inflateGetHeader s hp}"
  let outB ← mkBlock (Array.replicate outcap 0)
  acc := acc ++ (← decode s inB data.size outB outcap flush inchunk outchunk dictB dict.size hasDict)
  let z ← ldStream s
  acc := acc ++ s!" out:{hexOf (← blockBytes outB (offOf z.next_out))}"
  if let some (em, nm, cm) := hdr then
    let g ← ldHeader hp
    acc := acc ++ s!" hdr:{g.text}:{g.time}:{g.xflags}:{g.os}:{g.extra_len}:{g.hcrc}:{g.done}:"
    acc := acc ++ s!"{if g.extra != .null then "p" else "n"}:{if g.name != .null then "p" else "n"}:{if g.comment != .null then "p" else "n"}:"
    let ex ← if g.extra != .null then do pure (hexOf (← blockBytes g.extra em)) else pure "-"
    let na ← if g.name != .null then do pure (hexOf (← blockBytes g.name nm)) else pure "-"
    let co ← if g.comment != .null then do pure (hexOf (← blockBytes g.comment cm)) else pure "-"
    acc := acc ++ ex ++ ":" ++ na ++ ":" ++ co
  if reset != "-" then
    let r ← if reset.startsWith "R" then ZlibNg.Inflate.inflateReset s
      else if reset.startsWith "K" then ZlibNg.Inflate.inflateResetKeep s
      else ZlibNg.Inflate.inflateReset2 s (Int32.ofInt ((reset.drop 1).toString.toInt?.getD 0))
    acc := acc ++ s!" reset:{r}"
    let out2 ← mkBlock (Array.replicate outcap 0)
    acc := acc ++ (← decode s inB data.size out2 outcap flush inchunk outchunk dictB dict.size hasDict)
    let z ← ldStream s
    acc := acc ++ s!" out:{hexOf (← blockBytes out2 (offOf z.next_out))}"
  acc := acc ++ s!" end:{← ZlibNg.Inflate.inflateEnd s}"
  return acc

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "inf", [w, f, ic, oc, cap, d, dc, hd, rs] => do
    let wbits := Int32.ofInt (← parseI64 w).toInt
    let flush := Int32.ofInt (← parseI64 f).toInt
    let data ← parseHexOrDash d
    let dict ← parseHexOrDash dc
    let hdr : Option (Nat × Nat × Nat) ← if hd == "-" then pure none else
      match hd.splitOn "," with
      | [a, b, c] => pure (some (← parseNat a, ← parseNat b, ← parseNat c))
      | _ => throw "bad hdr"
    let h0 := ZlibNg.Crc32.initStatics Heap.empty
    match C.run (run wbits flush (← parseNat ic) (← parseNat oc) (← parseNat cap) data dict (dc != "-") hdr rs) h0 with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
