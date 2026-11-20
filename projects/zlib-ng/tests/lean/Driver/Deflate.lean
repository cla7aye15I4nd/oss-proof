import ZlibNgF.ZlibNg.«compress.c»
import DiffTest.Common

/-!
Lean side of the differential test for `deflate.c` and the one-shot `compress*` of `compress.c` (format:
`tests/c/deflate.c`). It runs the same call sequence on the translation and prints the same fields.
-/

open DiffTest C

/-- The starting heap: static CRC tables, a garbage oracle with no zero pattern (a read of uninitialised memory
shows up as a difference from the C), and every block at an address that is 16 modulo 64, as glibc's `malloc`
returns for the large deflate block. -/
def junkHeap : Heap :=
  { ZlibNg.Crc32.initStatics Heap.empty with
    garbage := fun a b => (UInt64.ofNat (a * 0x9E3779B97F4A7C15 + b * 0xBF58476D1CE4E5B9 + 0x94D049BB133111EB)) ^^^ 0x5555555555555555
    baseAddr := fun _ => 16 }

/-- A new heap block holding `a` (a `malloc` of the exact size, filled; at least one byte). -/
def mkBlock (a : Array UInt8) : M BPtr := fun h =>
  let b := h.nextBlk
  let a' := if a.size == 0 then #[0] else a
  .ok (.ref (.heap b) 0, { h with bytes := upd h.bytes b (some a'), nextBlk := b + 1, nalloc := h.nalloc + 1 })

def offOf (p : BPtr) : Nat := match p with | .ref _ o => o | .null => 0

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

def readStr (p : BPtr) : M String := do
  if p == .null then return "-"
  let mut a : Array UInt8 := #[]
  for i in [0:256] do
    let b ← index8 p i
    if b == 0 then break
    a := a.push b
  return String.fromUTF8! (ByteArray.mk a)

/-- `gen_data` of `tests/c/deflate.c`: `none` is a NULL pointer. -/
def genData (s : String) : Except String (Option (Array UInt8)) := do
  if s == "-" then return some #[]
  if s == "null" then return none
  if s.startsWith "hex:" then return some (← parseHex (s.drop 4).toString)
  match s.splitOn ":" with
  | ["gen", k, n, seed] =>
    let n ← parseNat n
    let seed ← parseNat seed
    let kind := k.front
    let alpha := "etaoin shrdlu\n".toUTF8
    let mut x : UInt32 := (UInt32.ofNat seed) ||| 1
    let mut out : Array UInt8 := Array.mkEmpty n
    for i in [0:n] do
      x := x ^^^ (x <<< 13)
      x := x ^^^ (x >>> 17)
      x := x ^^^ (x <<< 5)
      let k := if kind == 'm' then "rtpz".toList[(i / 1000) % 4]! else kind
      let v : UInt8 ←
        if k == 'z' then pure 0
        else if k == 'r' then pure (x &&& 0xff).toUInt8
        else if k == 't' then pure alpha[(x % 14).toNat]!
        else if k == 'p' then pure (UInt8.ofNat ((i % (1 + seed % 61)) * 7 + 3))
        else if k == 'b' then pure (x % 4).toUInt8
        else throw "bad kind"
      out := out.push v
    return some out
  | _ => throw s!"bad data {s}"

def parseInt (s : String) : Except String Int :=
  match s.toInt? with
  | some n => pure n
  | none => throw s!"bad number {s}"

def i32 (s : String) : Except String Int32 := do return Int32.ofInt (← parseInt s)

def fieldsOf (s : StreamPtr) : M String := do
  let z ← ldStream s
  return s!":{offOf z.next_in}:{z.avail_in}:{offOf z.next_out}:{z.avail_out}:{z.total_in}:{z.total_out}:{z.adler}:{z.data_type}:{← readStr z.msg}"

/-- The parsed operations of a script. -/
inductive Op where
  | skip
  | i (k : Nat) | o (k : Nat) | f (n : Int32) | L (n : Int32) (ic oc : Nat)
  | P (bits value : Int32) | Q (lv st : Int32) | T (g l n c : Int32)
  | C | D | d | G (n : Nat) | g | p | q | u | B (n : UInt64) | b (n : UInt64) | R | K | H | E

def parseOp (op : String) : Except String Op := do
  let c := op.front
  let a := (op.drop 1).toString
  let nums := fun (k : Nat) => do
    let parts := a.splitOn "/"
    if parts.length != k then throw s!"bad op {op}"
    parts.mapM i32
  match c with
  | '-' => return .skip
  | 'i' => return .i (← parseNat a)
  | 'o' => return .o (← parseNat a)
  | 'f' => return .f (← i32 a)
  | 'L' => match a.splitOn "/" with
    | [n, ic, oc] => return .L (← i32 n) (← parseNat ic) (← parseNat oc)
    | _ => throw s!"bad op {op}"
  | 'P' => do let v ← nums 2; return .P v[0]! v[1]!
  | 'Q' => do let v ← nums 2; return .Q v[0]! v[1]!
  | 'T' => do let v ← nums 4; return .T v[0]! v[1]! v[2]! v[3]!
  | 'C' => return .C
  | 'D' => return .D
  | 'd' => return .d
  | 'G' => return .G (← parseNat a)
  | 'g' => return .g
  | 'p' => return .p
  | 'q' => return .q
  | 'u' => return .u
  | 'B' => return .B (← parseU64 a)
  | 'b' => return .b (← parseU64 a)
  | 'R' => return .R
  | 'K' => return .K
  | 'H' => return .H
  | 'E' => return .E
  | _ => throw s!"bad op {op}"

/-- The header spec: `(text, time, xflags, os, extra, name, comment, hcrc)`. -/
/-- text, time, xflags, os, extra (buffer length or -1), name, comment, hcrc, and the value stored in `extra_len`
(the optional ninth field; `extra` when absent). -/
abbrev HdrSpec := Int32 × Int × Int32 × Int32 × Int × Int × Int × Int32 × Int

def parseHdr (s : String) : Except String (Option HdrSpec) := do
  if s == "-" then return none
  match s.splitOn "/" with
  | [t, tm, xf, os, ex, nm, cm, hc] =>
    let ex ← parseInt ex
    return some (← i32 t, ← parseInt tm, ← i32 xf, ← i32 os, ex, ← parseInt nm, ← parseInt cm, ← i32 hc, ex)
  | [t, tm, xf, os, ex, nm, cm, hc, el] =>
    return some (← i32 t, ← parseInt tm, ← i32 xf, ← i32 os, ← parseInt ex, ← parseInt nm, ← parseInt cm, ← i32 hc,
      ← parseInt el)
  | _ => throw "bad header"

def deflateLoop (s : StreamPtr) (inlen : Nat) (outcap : Nat) (n : Int32)
    (ic oc : Nat) : M String := do
  let mut acc := " L"
  let mut calls := 0
  for _ in [0:200000] do
    let z ← ldStream s
    let inleft := inlen - offOf z.next_in
    let outleft := outcap - offOf z.next_out
    stStream s { z with avail_in := (Nat.min inleft ic).toUInt32, avail_out := (Nat.min outleft oc).toUInt32 }
    let ni := z.next_in
    let no := z.next_out
    let r ← ZlibNg.Deflate.deflate s n
    acc := acc ++ s!" {r}" ++ (← fieldsOf s)
    calls := calls + 1
    if r != 0 then return acc
    let z ← ldStream s
    if z.next_in == ni && z.next_out == no then return acc
  return acc ++ " LIMIT"

def runDef (level method wbits memlevel strategy : Int32) (data dict : Option (Array UInt8)) (hdr : Option HdrSpec)
    (outcap : Nat) (script : List Op) : M String := do
  let inArr := data.getD #[]
  let inB ← mkBlock inArr
  let dictB ← mkBlock (dict.getD #[])
  let outB ← mkBlock (Array.replicate outcap 0)
  let mut hp : HeaderPtr := none
  if let some (t, tm, xf, os, ex, nm, cm, hc, el) := hdr then
    let eb ← if ex < 0 then pure .null else mkBlock (Array.ofFn (n := ex.toNat) fun i => UInt8.ofNat (i.val * 7 + 1))
    let nb ← if nm < 0 then pure .null else
      mkBlock ((Array.ofFn (n := nm.toNat) fun i => UInt8.ofNat (97 + i.val % 26)).push 0)
    let cb ← if cm < 0 then pure .null else
      mkBlock ((Array.ofFn (n := cm.toNat) fun i => UInt8.ofNat (65 + i.val % 26)).push 0)
    let g : GzHeader := { text := t, time := UInt64.ofInt tm, xflags := xf, os := os, extra := eb, extra_len := (if ex < 0 then 0 else UInt32.ofInt el), extra_max := (if ex < 0 then 0 else UInt32.ofInt ex), name := nb, name_max := (if nm < 0 then 0 else UInt32.ofInt (nm + 1)), comment := cb, comm_max := (if cm < 0 then 0 else UInt32.ofInt (cm + 1)), hcrc := hc, done := 0 }
    hp ← newHeader g
  let s1 ← newStream {}
  let s2 ← newStream {}
  let mut s := s1
  let ver ← strLitRef "1.3.2.zlib-ng"
  let r ← ZlibNg.Deflate.deflateInit2_ s level method wbits memlevel strategy ver 112
  let mut acc := s!"init:{r}" ++ (← fieldsOf s)
  let mut live := r == 0
  let z ← ldStream s
  stStream s { z with next_in := if data.isNone then .null else inB, next_out := outB }
  for op in script do
    if !live then break
    match op with
    | .skip => pure ()
    | .i k =>
      let z ← ldStream s
      stStream s { z with avail_in := (Nat.min (inArr.size - offOf z.next_in) k).toUInt32 }
    | .o k =>
      let z ← ldStream s
      stStream s { z with avail_out := (Nat.min (outcap - offOf z.next_out) k).toUInt32 }
    | .f n =>
      let r ← ZlibNg.Deflate.deflate s n
      acc := acc ++ s!" f{r}" ++ (← fieldsOf s)
    | .L n ic oc => acc := acc ++ (← deflateLoop s inArr.size outcap n ic oc)
    | .P bits value => acc := acc ++ s!" P{← ZlibNg.Deflate.deflatePrime s bits value}"
    | .Q lv st =>
      let r ← ZlibNg.Deflate.deflateParams s lv st
      acc := acc ++ s!" Q{r}" ++ (← fieldsOf s)
    | .T g l n c => acc := acc ++ s!" T{← ZlibNg.Deflate.deflateTune s g l n c}"
    | .C =>
      let d := if s == s1 then s2 else s1
      let r ← ZlibNg.Deflate.deflateCopy d s
      acc := acc ++ s!" C{r}"
      if r == 0 then
        acc := acc ++ s!":{← ZlibNg.Deflate.deflateEnd s}"
        s := d
    | .D =>
      let r ← ZlibNg.Deflate.deflateSetDictionary s (if dict.isNone then .null else dictB) (dict.getD #[]).size.toUInt32
      acc := acc ++ s!" D{r}" ++ (← fieldsOf s)
    | .d => acc := acc ++ s!" d{← ZlibNg.Deflate.deflateSetDictionary s .null 0}"
    | .G n =>
      let buf ← if n == 0 then pure .null else mkBlock (Array.replicate n 0)
      let (r, len) ← ZlibNg.Deflate.deflateGetDictionary s buf true
      let len := len.getD 7777
      acc := acc ++ s!" G{r}:{len}:"
      if buf != .null then
        acc := acc ++ hexOf (← blockBytes buf (if r == 0 && len.toNat ≤ n then len.toNat else 0))
      else acc := acc ++ "-"
    | .g =>
      let (r, _) ← ZlibNg.Deflate.deflateGetDictionary s .null false
      acc := acc ++ s!" g{r}"
    | .p =>
      let (r, pe, bi) ← ZlibNg.Deflate.deflatePending s true true
      acc := acc ++ s!" p{r}:{pe.getD 7777}:{bi.getD 7777}"
    | .q =>
      let (r, _, _) ← ZlibNg.Deflate.deflatePending s false false
      acc := acc ++ s!" q{r}"
    | .u =>
      let (r, bi) ← ZlibNg.Deflate.deflateUsed s true
      acc := acc ++ s!" u{r}:{bi.getD 7777}"
    | .B n => acc := acc ++ s!" B{← ZlibNg.Deflate.deflateBound s n}"
    | .b n => acc := acc ++ s!" b{← ZlibNg.Deflate.deflateBound_z s n}"
    | .R =>
      let r ← ZlibNg.Deflate.deflateReset s
      acc := acc ++ s!" R{r}" ++ (← fieldsOf s)
    | .K =>
      let r ← ZlibNg.Deflate.deflateResetKeep s
      acc := acc ++ s!" K{r}" ++ (← fieldsOf s)
    | .H => acc := acc ++ s!" H{← ZlibNg.Deflate.deflateSetHeader s hp}"
    | .E =>
      acc := acc ++ s!" E{← ZlibNg.Deflate.deflateEnd s}"
      live := false
  let z ← ldStream s
  acc := acc ++ s!" out:{hexOf (← blockBytes outB (offOf z.next_out))}"
  if live then acc := acc ++ s!" end:{← ZlibNg.Deflate.deflateEnd s}"
  if hp != none then
    let g ← ldHeader hp
    acc := acc ++ s!" hdr:{g.done}:{g.time}"
  return acc

def runCmp (fn : String) (level : Int32) (data : Option (Array UInt8)) (outcap : Option Nat) (cell : Option UInt64) :
    M String := do
  let inB ← mkBlock (data.getD #[])
  let src := if data.isNone then .null else inB
  let out ← match outcap with
    | some n => mkBlock (Array.replicate n 0)
    | none => pure .null
  let len := (data.getD #[]).size.toUInt64
  let (r, cell') ←
    if fn == "c" then ZlibNg.Compress.compress out cell src len
    else if fn == "c2" then ZlibNg.Compress.compress2 out cell src len level
    else if fn == "cz" then ZlibNg.Compress.compress_z out cell src len
    else ZlibNg.Compress.compress2_z out cell src len level
  let cs := match cell' with | some v => toString v | none => "N"
  let bytes ← if out != .null && r == 0 then do pure (hexOf (← blockBytes out (cell'.getD 0).toNat)) else pure "-"
  return s!"{r}:{cs}:{bytes}"

def showM (m : M String) : String :=
  match C.run m junkHeap with
  | .ok (s, _) => s
  | .error f => showFault f

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "def", [lv, me, wb, ml, st, data, dict, hdr, outcap, script] => do
    let ops ← (script.splitOn ",").mapM parseOp
    return showM (runDef (← i32 lv) (← i32 me) (← i32 wb) (← i32 ml) (← i32 st) (← genData data) (← genData dict)
      (← parseHdr hdr) (← parseNat outcap) ops)
  | "cmp", [f, lv, data, outcap, cell] => do
    if !(f == "c" || f == "c2" || f == "cz" || f == "c2z") then throw "bad fn"
    let oc ← if outcap == "N" then pure none else some <$> parseNat outcap
    let ce ← if cell == "N" then pure none else some <$> parseU64 cell
    return showM (runCmp f (← i32 lv) (← genData data) oc ce)
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
