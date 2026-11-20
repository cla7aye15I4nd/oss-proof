import MozjpegF.Runtime.Libc

/-!
# Shared helpers for `mozjpeg` Lean differential-test drivers
-/

namespace DiffTest

def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"bad unsigned number {s}"

def parseU32 (s : String) : Except String UInt32 := do
  let n ← parseNat s
  if n < 2 ^ 32 then pure (UInt32.ofNat n) else throw s!"out of range for uint32: {s}"

def parseI32 (s : String) : Except String Int32 :=
  match s.toInt? with
  | some n =>
    if -(2 ^ 31 : Int) ≤ n ∧ n < 2 ^ 31 then pure (Int32.ofInt n)
    else throw s!"out of range for int32: {s}"
  | none => throw s!"bad signed number {s}"

def parseI64 (s : String) : Except String Int64 :=
  match s.toInt? with
  | some n =>
    if -(2 ^ 63 : Int) ≤ n ∧ n < 2 ^ 63 then pure (Int64.ofInt n)
    else throw s!"out of range for int64: {s}"
  | none => throw s!"bad signed number {s}"

def showFault : C.Fault → String
  | .ub w => s!"FAULT ub {w}"
  | .outOfFuel => "FAULT outOfFuel"

def hexByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toUTF8
  String.fromUTF8! (ByteArray.mk #[digits[(b / 16).toNat]!, digits[(b % 16).toNat]!])

def showBytes (arr : Array UInt8) : String :=
  String.join (arr.toList.map hexByte)

end DiffTest
