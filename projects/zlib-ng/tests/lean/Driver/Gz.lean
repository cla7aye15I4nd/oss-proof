import ZlibNgF.ZlibNg.«gzlib.c.gzclose»
import DiffTest.Common

/-!
Lean side of the differential test for `gzlib.c`, `gzread.c` and `gzwrite.c` (format: `tests/c/gz.c`). It runs the
same operations on the translation, in a world (`C.World`) whose file `f` and OS-call schedule are those of the
line, and prints the same fields. The `vsnprintf` oracle is set before each `printf` operation to the output of its
format (`"%s"` of the bytes, `"%d"` of the number, `"%s"` of the empty string). The allocation oracle
(`Heap.allocOk`) fails the library's `malloc` calls the schedule names (`A<k>`); the driver's own buffers are not
`malloc` calls of the library and are not numbered.
-/

open DiffTest C ZlibNg.Gz ZlibNg.Inflate

def junkHeap : Heap :=
  { ZlibNg.Crc32.initStatics Heap.empty with
    garbage := fun a b => (UInt64.ofNat (a * 0x9E3779B97F4A7C15 + b * 0xBF58476D1CE4E5B9 + 0x94D049BB133111EB)) ^^^ 0x5555555555555555
    baseAddr := fun _ => 16 }

/-- A new heap block holding `a` (a driver buffer of the exact size, filled; at least one byte). It is not a `malloc`
call of the library: `nalloc` does not move. -/
def mkBlock (a : Array UInt8) : M BPtr := fun h =>
  let b := h.nextBlk
  let a' := if a.size == 0 then #[0] else a
  .ok (.ref (.heap b) 0, { h with bytes := upd h.bytes b (some a'), nextBlk := b + 1 })

def freeBlock (p : BPtr) : M Unit := freeB p

def hexOf (a : Array UInt8) : String :=
  if a.isEmpty then "-" else
  String.join (a.toList.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

def fnv (a : Array UInt8) : UInt64 := Id.run do
  let mut h : UInt64 := 1469598103934665603
  for b in a do
    h := (h ^^^ b.toUInt64) * 1099511628211
  return h

def hex16 (v : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 v.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- The string at `p` (bytes before the first zero). -/
def cstr (p : BPtr) : M (Array UInt8) := strBytes p

/-- A C string literal argument of the driver, in a fresh block. -/
def mkStr (s : Array UInt8) : M BPtr := mkBlock (s.push 0)

/-- One schedule entry: call number and choice. -/
inductive Ch where
  | F (e : Int32)
  | S (k : Nat)
  | B (bs : Array UInt8)
  | V (v : Int64)
  /-- the library's `malloc` call number `n` returns `NULL` -/
  | A

def parseCh (e : String) : Except String (Nat × Ch) := do
  if e.startsWith "A" then return (← parseNat (e.drop 1).toString, .A)
  match e.splitOn ":" with
  | [n, c] =>
    let n ← parseNat n
    let k := c.take 1 |>.toString
    let rest := (c.drop 1).toString
    if k == "F" then return (n, .F (← parseI64 rest).toInt32)
    else if k == "S" then return (n, .S (← parseNat rest))
    else if k == "B" then return (n, .B (← parseHex rest))
    else if k == "V" then return (n, .V (← parseI64 rest))
    else throw s!"bad choice {c}"
  | _ => throw s!"bad schedule entry {e}"

def mkFs (file : Option (Array UInt8)) (sch : List (Nat × Ch)) : Fs :=
  let find (n : Nat) : Option Ch := ((sch.filter fun e => match e.2 with | .A => false | _ => true).find? (·.1 == n)).map (·.2)
  { names := if file.isSome then #[("f".toUTF8.data, 0)] else #[]
    nodes := match file with | some d => #[d] | none => #[]
    budget := 2 ^ 30
    readChoice := fun n => match find n with
      | some (.F e) => .fail e | some (.S k) => .short k | some (.B bs) => .bytes bs | _ => .regular
    writeChoice := fun n => match find n with
      | some (.F e) => .fail e | some (.S k) => .count k | _ => .regular
    lseekChoice := fun n => match find n with
      | some (.F e) => .fail e | some (.V v) => .value v | _ => .regular
    openFail := fun n => match find n with | some (.F e) => some e | _ => none
    closeFail := fun n => match find n with | some (.F e) => some e | _ => none }

def i32 (s : String) : Except String Int32 := do return (← parseI64 s).toInt32

/-- The fields of an op (`name:a:b:...`). -/
def fieldsOf (op : String) : List String := op.splitOn ":"

/-- Run one op on the handle; returns its output and the new handle. -/
def runOp (file : GzPtr) (op : String) : Except String (G (String × GzPtr)) := do
  match fieldsOf op with
  | ["open", mode] | ["openg", mode] =>
    let g := op.startsWith "openg"
    return do
      let p ← lm (mkStr (if g then "g" else "f").toUTF8.data)
      let m ← lm (mkStr mode.toUTF8.data)
      let f ← gzopen p m
      return (s!"open:{if f.isSome then 1 else 0}:{(← get).fs.lastOflag.toInt}", f)
  | ["dopen", fl, mode] =>
    let fl ← i32 fl
    return do
      let p ← lm (mkStr "f".toUTF8.data)
      let fd ← openG p fl
      let m ← lm (mkStr mode.toUTF8.data)
      let f ← gzdopen fd m
      return (s!"dopen:{fd.toInt}:{if f.isSome then 1 else 0}", f)
  | ["dopenfd", fd, mode] =>
    let fd ← i32 fd
    return do
      let m ← lm (mkStr mode.toUTF8.data)
      let f ← gzdopen fd m
      return (s!"dopenfd:{if f.isSome then 1 else 0}", f)
  | ["buffer", n] =>
    let n ← parseU32 n
    return do return (s!"{(← gzbuffer file n).toInt}", file)
  | ["read", n] =>
    let n ← parseU32 n
    return do
      let b ← lm (mkBlock (Array.replicate (if n.toNat ≤ 2 ^ 20 then n.toNat else 1) 0))
      let r ← gzread file b n
      let bs ← lm (loadBytes b (if r > 0 then r.toInt.toNat else 0))
      lm (freeBlock b)
      return (s!"{r.toInt}:{hexOf bs}", file)
  | ["fread", sz, ni] =>
    let sz ← parseU64 sz
    let ni ← parseU64 ni
    return do
      let cap0 : Nat := if sz != 0 && ni.toNat ≤ (2 ^ 64 - 1) / sz.toNat then sz.toNat * ni.toNat else 1
      let cap := if cap0 > 2 ^ 20 then 1 else cap0
      let b ← lm (mkBlock (Array.replicate cap 0))
      let r ← gzfread b sz ni file
      let bs ← lm (loadBytes b (if r.toNat * sz.toNat ≤ cap then r.toNat * sz.toNat else 0))
      lm (freeBlock b)
      return (s!"{r.toNat}:{hexOf bs}", file)
  | ["getc"] => return do return (s!"{(← gzgetc file).toInt}", file)
  | ["getc_"] => return do return (s!"{(← gzgetc_ file).toInt}", file)
  | ["ungetc", c] =>
    let c ← i32 c
    return do return (s!"{(← gzungetc c file).toInt}", file)
  | ["gets", n] =>
    let n ← i32 n
    return do
      let b ← lm (mkBlock (Array.replicate (if n > 0 then n.toInt.toNat else 1) 0))
      let r ← gzgets file b n
      let s ← if r == .null then pure "null" else do
        let d ← lm (Ptr.diff r b)
        pure s!"{d.toInt}:{hexOf (← lm (cstr r))}"
      lm (freeBlock b)
      return (s, file)
  | ["eof"] => return do return (s!"{(← gzeof file).toInt}", file)
  | ["direct"] => return do return (s!"{(← gzdirect file).toInt}", file)
  | ["error"] => return do
      let (m, en) ← gzerror file true
      if m == .null then return ("err:null", file)
      return (s!"err:{(en.getD 12345).toInt}:{hexOf (← lm (cstr m))}", file)
  | ["clearerr"] => return do gzclearerr file; return ("ok", file)
  | ["tell"] => return do return (s!"{(← gztell64 file).toInt}", file)
  | ["offset"] => return do return (s!"{(← gzoffset64 file).toInt}", file)
  | ["seek", off, wh] =>
    let off ← parseI64 off
    let wh ← i32 wh
    return do return (s!"{(← gzseek64 file off wh).toInt}", file)
  | ["rewind"] => return do return (s!"{(← gzrewind file).toInt}", file)
  | ["write", hx] =>
    let bs ← parseHex (if hx == "-" then "" else hx)
    return do
      let b ← lm (mkBlock bs)
      let r ← gzwrite file b bs.size.toUInt32
      lm (freeBlock b)
      return (s!"{r.toInt}", file)
  | ["writen", n, v] =>
    let n ← parseNat n
    let v ← parseI64 v
    return do
      let bs := Array.ofFn (n := n) fun i =>
        if v < 0 then UInt8.ofNat ((i.val * 7 + i.val / 3) % 256) else UInt8.ofNat v.toInt.toNat
      let b ← lm (mkBlock bs)
      let r ← gzwrite file b n.toUInt32
      lm (freeBlock b)
      return (s!"{r.toInt}", file)
  | ["fwrite", sz, ni, hx] =>
    let sz ← parseU64 sz
    let ni ← parseU64 ni
    let bs ← parseHex (if hx == "-" then "" else hx)
    return do
      let b ← lm (mkBlock bs)
      let r ← gzfwrite b sz ni file
      lm (freeBlock b)
      return (s!"{r.toNat}", file)
  | ["putc", c] =>
    let c ← i32 c
    return do return (s!"{(← gzputc file c).toInt}", file)
  | ["puts", hx] =>
    let bs ← parseHex (if hx == "-" then "" else hx)
    return do
      let b ← lm (mkStr bs)
      let r ← gzputs file b
      lm (freeBlock b)
      return (s!"{r.toInt}", file)
  | "printf" :: k :: rest =>
    let out ← if k == "s" then (match rest with | [hx] => parseHex (if hx == "-" then "" else hx) | _ => throw "printf s")
      else if k == "d" then (match rest with | [d] => do pure (toString (← i32 d).toInt).toUTF8.data | _ => throw "printf d")
      else if k == "e" then pure #[]
      else throw "bad printf kind"
    return do
      let fmt ← lm (mkStr "%s".toUTF8.data)
      let w ← get
      let n := w.nprintf
      set { w with printfRet := fun i => if i == n then Int32.ofNat out.size else w.printfRet i,
                   printfOut := fun i => if i == n then out else w.printfOut i }
      let r ← gzprintf file fmt
      lm (freeBlock fmt)
      return (s!"{r.toInt}", file)
  | ["flush", f] =>
    let f ← i32 f
    return do return (s!"{(← gzflush file f).toInt}", file)
  | ["params", l, s] =>
    let l ← i32 l
    let s ← i32 s
    return do return (s!"{(← gzsetparams file l s).toInt}", file)
  | ["close"] => return do
      let r ← gzclose file
      return (s!"{r.toInt}", if r == Z_STREAM_ERROR then file else none)
  | ["closer"] => return do
      let r ← gzclose_r file
      return (s!"{r.toInt}", if r == Z_STREAM_ERROR then file else none)
  | ["closew"] => return do
      let r ← gzclose_w file
      return (s!"{r.toInt}", if r == Z_STREAM_ERROR then file else none)
  | ["null"] => return do
      let z : GzPtr := none
      let b ← lm (mkBlock (Array.replicate 4 0))
      let a ← lm (mkStr "a".toUTF8.data)
      let fmt ← lm (mkStr "%d".toUTF8.data)
      let v1 ← gzbuffer z 64
      let v2 ← gzread z b 1
      let v3 ← gzfread b 1 1 z
      let v4 ← gzwrite z b 1
      let v5 ← gzfwrite b 1 1 z
      let v6 ← gzputc z 1
      let v7 ← gzputs z a
      let v8 ← gzprintf z fmt
      let v9 ← gzgetc z
      let v10 ← gzungetc 1 z
      let v11 ← gzgets z b 4
      let v12 ← gzflush z 0
      let v13 ← gzsetparams z 1 0
      let v14 ← gzrewind z
      let v15 ← gzeof z
      let v16 ← gzseek64 z 0 0
      let v17 ← gztell64 z
      let v18 ← gzoffset64 z
      let (v19, _) ← gzerror z true
      let v20 ← gzdirect z
      let v21 ← gzclose z
      let v22 ← gzclose_r z
      let v23 ← gzclose_w z
      gzclearerr z
      lm (freeBlock b); lm (freeBlock a); lm (freeBlock fmt)
      let bi : Bool → Nat := fun x => if x then 1 else 0
      return (s!"null:{v1.toInt}:{v2.toInt}:{v3.toNat}:{v4.toInt}:{v5.toNat}:{v6.toInt}:{v7.toInt}:{v8.toInt}:{v9.toInt}:{v10.toInt}:{bi (v11 == .null)}:{v12.toInt}:{v13.toInt}:{v14.toInt}:{v15.toInt}:{v16.toInt}:{v17.toInt}:{v18.toInt}:{bi (v19 == .null)}:{v20.toInt}:{v21.toInt}:{v22.toInt}:{v23.toInt}", file)
  | _ => throw s!"bad op {op}"

def fileOut (w : World) (name : String) : Option String :=
  match w.fs.lookup name.toUTF8.data with
  | some n => let d := w.fs.nodes[n]?.getD #[]; some s!"{d.size}:{hex16 (fnv d)}"
  | none => none

def runLine (file : Option (Array UInt8)) (sch : List (Nat × Ch)) (ops : List String) : Except String String := do
  let acts ← ops.mapM fun op => do return (← runOp none op, op)
  -- re-parse per op at run time with the current handle
  let _ := acts
  let w0 : World := { fs := mkFs file sch }
  let prog : G (List String) := do
    let mut f : GzPtr := none
    let mut outs : List String := []
    for op in ops do
      match runOp f op with
      | .ok m =>
        let (s, f') ← m
        outs := outs ++ [s]
        f := f'
      | .error e => gub s!"bad op {e}"
    if f.isSome then
      let r ← gzclose f
      outs := outs ++ [s!"autoclose:{r.toInt}"]
    let w ← get
    outs := outs ++ [match fileOut w "f" with | some s => s!"F:{s}" | none => "F:none"]
    if let some s := fileOut w "g" then outs := outs ++ [s!"G:{s}"]
    let nopen := (w.fs.fds.filter (·.isSome)).size
    outs := outs ++ [s!"fds:{nopen}"]
    return outs
  let fails := (sch.filter fun e => match e.2 with | .A => true | _ => false).map (·.1)
  match C.run (prog.run w0) { junkHeap with allocOk := fun n => !fails.contains n } with
  | .ok ((outs, _), _) => return " ".intercalate outs
  | .error f => return showFault f

def handle (fn : String) (args : List String) : Except String String :=
  match fn, args with
  | "gz", fhex :: sc :: ops => do
    let file ← if fhex == "none" then pure none else some <$> parseHex (if fhex == "-" then "" else fhex)
    let sch ← if sc == "-" then pure [] else (sc.splitOn ",").mapM parseCh
    runLine file sch ops
  | _, _ => throw s!"unknown function or wrong arity: {fn}"

def main : IO UInt32 := mainLoop handle
