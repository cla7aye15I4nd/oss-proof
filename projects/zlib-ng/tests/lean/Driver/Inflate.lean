import ZlibNgF.ZlibNg.«uncompr.c»
import DiffTest.Common

/-!
Lean side of the differential test for `inflate.c` (format: `tests/c/inflate.c`). It runs the same call sequence on
the translation in `ZlibNgF/ZlibNg/inflate.c.lean` and prints the same fields.
-/

open DiffTest C

/-- The starting heap: static CRC tables, and a garbage oracle with no zero pattern, so that a read of an
uninitialised local or of fresh `malloc` memory shows up as a difference from the C. -/
def junkHeap : Heap :=
  { ZlibNg.Crc32.initStatics Heap.empty with
    garbage := fun a b => (UInt64.ofNat (a * 0x9E3779B97F4A7C15 + b * 0xBF58476D1CE4E5B9 + 0x94D049BB133111EB)) ^^^ 0x5555555555555555 }

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

/-- `:in_off:avail_in:out_off:avail_out:total_in:total_out:adler:data_type:msg` -/
def fieldsOf (s : StreamPtr) : M String := do
  let z ← ldStream s
  return s!":{offOf z.next_in}:{z.avail_in}:{offOf z.next_out}:{z.avail_out}:{z.total_in}:{z.total_out}:{z.adler}:{z.data_type}:{← readStr z.msg}"

def runOps (wbits : Int32) (outcap : Nat) (data dict : Array UInt8) (script : List String) : M String := do
  let inB ← mkBlock data
  let dictB ← mkBlock dict
  let outB ← mkBlock (Array.replicate outcap 0)
  let s1 ← newStream {}
  let s2 ← newStream {}
  let mut s := s1
  let ver ← strLitRef "1.3.2.zlib-ng"
  let r ← ZlibNg.Inflate.inflateInit2_ s wbits ver 112
  let mut acc := s!"init:{r}"
  if r != 0 then return acc
  let z ← ldStream s
  stStream s { z with next_in := inB, next_out := outB }
  for op in script do
    let c := op.front
    let arg := (op.drop 1).toString
    if c == 'i' then
      let z ← ldStream s
      let left := data.size - offOf z.next_in
      stStream s { z with avail_in := (Nat.min left (arg.toNat?.getD 0)).toUInt32 }
      continue
    if c == 'o' then
      let z ← ldStream s
      let left := outcap - offOf z.next_out
      stStream s { z with avail_out := (Nat.min left (arg.toNat?.getD 0)).toUInt32 }
      continue
    acc := acc ++ s!" {op}"
    let num (t : String) : Int32 := Int32.ofInt (t.toInt?.getD 0)
    if c == 'f' then
      let r ← ZlibNg.Inflate.inflate s (num arg)
      acc := acc ++ s!"={r}" ++ (← fieldsOf s)
    else if c == 'P' then
      match arg.splitOn "/" with
      | [b, v] => acc := acc ++ s!"={← ZlibNg.Inflate.inflatePrime s (num b) (num v)}"
      | _ => acc := acc ++ "BAD"
    else if c == 'S' then
      let r ← ZlibNg.Inflate.inflateSync s
      acc := acc ++ s!"={r}" ++ (← fieldsOf s)
    else if c == 'Y' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateSyncPoint s}"
    else if c == 'C' then
      let r ← ZlibNg.Inflate.inflateCopy s2 s
      acc := acc ++ s!"={r}"
      if r == 0 then
        acc := acc ++ s!":{← ZlibNg.Inflate.inflateEnd s}"
        s := s2
    else if c == 'G' then
      let n := arg.toNat?.getD 0
      let b ← if n == 0 then pure .null else mkBlock (Array.replicate n 0xaa)
      let (r, len) ← ZlibNg.Inflate.inflateGetDictionary s b true
      let bs ← if n == 0 then pure "-" else do pure (hexOf (← blockBytes b n))
      acc := acc ++ s!"={r}:{len.getD 12345}:{bs}"
    else if c == 'g' then
      let (r, _) ← ZlibNg.Inflate.inflateGetDictionary s .null false
      acc := acc ++ s!"={r}"
    else if c == 'd' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateSetDictionary s dictB dict.size.toUInt32}"
    else if c == 'n' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateSetDictionary s .null 0}"
    else if c == 'U' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateUndermine s (num arg)}"
    else if c == 'V' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateValidate s (num arg)}"
    else if c == 'M' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateMark s}"
    else if c == 'N' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateCodesUsed s}"
    else if c == 'R' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateReset s}"
    else if c == 'K' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateResetKeep s}"
    else if c == 'W' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateReset2 s (num arg)}"
    else if c == 'E' then
      acc := acc ++ s!"={← ZlibNg.Inflate.inflateEnd s}"
    else
      acc := acc ++ "BADOP"
  let z ← ldStream s
  acc := acc ++ s!" out:{hexOf (← blockBytes outB (offOf z.next_out))}"
  acc := acc ++ s!" end:{← ZlibNg.Inflate.inflateEnd s}"
  if s != s1 then
    let _ ← ZlibNg.Inflate.inflateEnd s1
  return acc

def runUnc (v : String) (dsize : Option Nat) (dl sl : Option UInt64) (src : Option (Array UInt8)) : M String := do
  let dest ← match dsize with
    | none => pure .null
    | some n => mkBlock (Array.replicate (if n == 0 then 1 else n) 0xaa)
  let srcB ← match src with
    | none => pure .null
    | some a => mkBlock a
  let (r, dl', sl') ←
    if v == "u" then do
      let (r, d) ← ZlibNg.Uncompr.uncompress dest dl srcB (sl.getD 0)
      pure (r, d, sl)
    else if v == "u2" then ZlibNg.Uncompr.uncompress2 dest dl srcB sl
    else if v == "uz" then do
      let (r, d) ← ZlibNg.Uncompr.uncompress_z dest dl srcB (sl.getD 0)
      pure (r, d, sl)
    else ZlibNg.Uncompr.uncompress2_z dest dl srcB sl
  let bs ← match dsize with
    | none => pure "-"
    | some n => do pure (hexOf (← blockBytes dest n))
  return s!"{r}:{dl'.getD 0}:{sl'.getD 0}:{bs}"

def runVer (ver : Option String) (size : Int32) (wb : Option Int32) : M String := do
  let vp ← match ver with
    | none => pure .null
    | some v => mkBlock (v.toUTF8.data.push 0)
  let s ← newStream {}
  let r ← match wb with
    | none => ZlibNg.Inflate.inflateInit_ s vp size
    | some w => ZlibNg.Inflate.inflateInit2_ s w vp size
  let e ← if r == 0 then ZlibNg.Inflate.inflateEnd s else pure 99
  return s!"init:{r} end:{e}"

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
    let h0 := junkHeap
    match C.run (run wbits flush (← parseNat ic) (← parseNat oc) (← parseNat cap) data dict (dc != "-") hdr rs) h0 with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | "ops", [w, cap, d, dc, sc] => do
    let h0 := junkHeap
    let w := Int32.ofInt (← parseI64 w).toInt
    match C.run (runOps w (← parseNat cap) (← parseHexOrDash d) (← parseHexOrDash dc) (sc.splitOn ",")) h0 with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | "unc", [v, ds, dl, sl, sn, src] => do
    let h0 := junkHeap
    let opt (t : String) : Except String (Option Nat) := if t == "null" then pure none else do pure (some (← parseNat t))
    let ds ← opt ds
    let dl ← opt dl
    let sl ← opt sl
    let src ← if sn == "null" then pure none else do pure (some (← parseHexOrDash src))
    match C.run (runUnc v ds (dl.map (·.toUInt64)) (sl.map (·.toUInt64)) src) h0 with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | "ver", [v, sz, wb] => do
    let h0 := junkHeap
    let sz := Int32.ofInt (← parseI64 sz).toInt
    let wb ← if wb == "-" then pure none else do pure (some (Int32.ofInt (← parseI64 wb).toInt))
    match C.run (runVer (if v == "null" then none else some v) sz wb) h0 with
    | .ok (s, _) => return s
    | .error f => return showFault f
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
