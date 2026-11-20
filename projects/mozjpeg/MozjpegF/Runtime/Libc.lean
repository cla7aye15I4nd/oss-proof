import MozjpegF.Runtime.Ptr

/-!
# Strict ISO C17 memory, allocation, string-literal, and checked-arithmetic primitives (`MozjpegF`)

Under ISO C17 §7.24.1p2, pointer arguments to `memcpy` and `memset` must point into live objects even
when the byte count `n` is `0`.
Under ISO C17 §6.5p5 and §6.5.5, signed integer overflow, division/modulo by zero, and `INT_MIN / -1`
raise `Fault.ub`.
-/

set_option autoImplicit false

namespace C

def load8 (p : BPtr) : M UInt8 := Ptr.load p
def index8 (p : BPtr) (i : Int) : M UInt8 := Ptr.index p i
def store8 (p : BPtr) (v : UInt8) : M Unit := Ptr.store p v

/-- Checked 32-bit signed range check (`INT32_MIN .. INT32_MAX`). -/
def checkI32 (x : Int) (what : String) : M Int32 :=
  if -(2 ^ 31 : Int) ≤ x ∧ x < 2 ^ 31 then pure (Int32.ofInt x)
  else ub what

/-- Checked 64-bit signed range check (`INT64_MIN .. INT64_MAX`, LP64 `long`). -/
def checkI64 (x : Int) (what : String) : M Int64 :=
  if -(2 ^ 63 : Int) ≤ x ∧ x < 2 ^ 63 then pure (Int64.ofInt x)
  else ub what

/-- Signed 32-bit `a + b` under ISO C17 §6.5p5. -/
def i32Add (a b : Int32) : M Int32 := checkI32 (a.toInt + b.toInt) "signed int32 addition overflow"

/-- Signed 32-bit `a - b` under ISO C17 §6.5p5. -/
def i32Sub (a b : Int32) : M Int32 := checkI32 (a.toInt - b.toInt) "signed int32 subtraction overflow"

/-- Signed 32-bit `a * b` under ISO C17 §6.5p5. -/
def i32Mul (a b : Int32) : M Int32 := checkI32 (a.toInt * b.toInt) "signed int32 multiplication overflow"

/-- Signed 32-bit `a / b` (truncating toward zero) under ISO C17 §6.5.5p6. -/
def i32Div (a b : Int32) : M Int32 :=
  if b == 0 then ub "int32 division by zero"
  else if a.toInt == -(2 ^ 31 : Int) ∧ b.toInt == -1 then ub "int32 INT_MIN / -1 overflow"
  else checkI32 (Int.tdiv a.toInt b.toInt) "signed int32 division overflow"

/-- Signed 32-bit `a % b` under ISO C17 §6.5.5p6. -/
def i32Mod (a b : Int32) : M Int32 :=
  if b == 0 then ub "int32 modulo by zero"
  else if a.toInt == -(2 ^ 31 : Int) ∧ b.toInt == -1 then ub "int32 INT_MIN % -1 overflow"
  else checkI32 (Int.tmod a.toInt b.toInt) "signed int32 modulo overflow"

/-- Signed 64-bit `a + b` (LP64 `long`) under ISO C17 §6.5p5. -/
def i64Add (a b : Int64) : M Int64 := checkI64 (a.toInt + b.toInt) "signed int64 addition overflow"

/-- Signed 64-bit `a - b` (LP64 `long`) under ISO C17 §6.5p5. -/
def i64Sub (a b : Int64) : M Int64 := checkI64 (a.toInt - b.toInt) "signed int64 subtraction overflow"

/-- Signed 64-bit `a * b` (LP64 `long`) under ISO C17 §6.5p5. -/
def i64Mul (a b : Int64) : M Int64 := checkI64 (a.toInt * b.toInt) "signed int64 multiplication overflow"

/-- Signed 64-bit `a / b` (LP64 `long`, truncating toward zero) under ISO C17 §6.5.5p6. -/
def i64Div (a b : Int64) : M Int64 :=
  if b == 0 then ub "int64 division by zero"
  else if a.toInt == -(2 ^ 63 : Int) ∧ b.toInt == -1 then ub "int64 LONG_MIN / -1 overflow"
  else checkI64 (Int.tdiv a.toInt b.toInt) "signed int64 division overflow"

/-- Signed 64-bit `a % b` (LP64 `long`) under ISO C17 §6.5.5p6. -/
def i64Mod (a b : Int64) : M Int64 :=
  if b == 0 then ub "int64 modulo by zero"
  else if a.toInt == -(2 ^ 63 : Int) ∧ b.toInt == -1 then ub "int64 LONG_MIN % -1 overflow"
  else checkI64 (Int.tmod a.toInt b.toInt) "signed int64 modulo overflow"

/-- Look up a source string literal in `strTable` and return its static read-only `BPtr`. -/
def strLitRef (s : String) : M BPtr := fun h =>
  match strTable.findIdx? (· == s) with
  | some i => .ok (.ref (.str i) 0, h)
  | none => .error (.ub "unknown string literal")

/-- `malloc(n)` on LP64: consults `h.allocOk h.nalloc`, returning `.null` on OOM or a fresh block filled from `h.garbage`. -/
def allocB (n : Nat) : M BPtr := fun h =>
  if h.allocOk h.nalloc then
    let b := h.nextBlk
    let arr := Array.ofFn (n := n) (fun i => Junk.of (h.garbage h.nalloc i.val))
    let h' : Heap := {
      h with
      bytes := upd h.bytes b (some arr)
      nextBlk := b + 1
      nalloc := h.nalloc + 1
    }
    .ok (.ref (.heap b) 0, h')
  else
    .ok (.null, { h with nalloc := h.nalloc + 1 })

/-- `free(p)` under ISO C17 §7.22.3.3. -/
def freeB (p : BPtr) : M Unit := fun h =>
  match p with
  | .null => .ok ((), h)
  | .ref (.heap b) 0 =>
    match h.bytes b with
    | some _ => .ok ((), { h with bytes := upd h.bytes b none })
    | none => .error (.ub "double or dangling free")
  | _ => .error (.ub "free of non-heap or interior pointer")

/-- `memset(dst, byte, n)` under strict ISO C17 §7.24.1p2 and §7.24.6.1.
Both null and dangling `dst` fault even when `n = 0`. -/
def Ptr.memset {R : Type} [Space Heap R UInt8] (dst : Ptr R) (byte : UInt8) (n : Nat) : M Unit := fun h =>
  match dst with
  | .null => .error (.ub "memset on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset on a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "memset into a read-only object")
      else if off + n ≤ a.size then
        let fillSlice := Id.run do
          let mut out := a
          for i in [0:n] do
            out := out.set! (off + i) byte
          return out
        .ok ((), Space.modify h r (fun _ => fillSlice))
      else .error (.ub "memset outside its object")

/-- Zero an entire live writable `JpegErrorMgr` object (`memset(err, 0, sizeof(struct jpeg_error_mgr))`). -/
def memsetZeroErrMgr (dst : ErrPtr) : M Unit := fun h =>
  match dst with
  | .null => .error (.ub "memset on a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset on a dangling pointer")
    | some a =>
      if Space.ro h r then .error (.ub "memset into a read-only object")
      else if off < a.size then
        .ok ((), Space.modify h r (fun arr => arr.set! off { msgParmI := Array.replicate 8 0 }))
      else .error (.ub "memset outside its object")

theorem toInt_ofInt64 {x : Int} (hlo : -(2 ^ 63 : Int) ≤ x) (hhi : x < 2 ^ 63) :
    (Int64.ofInt x).toInt = x := by
  rw [Int64.toInt_ofInt, Int.bmod]
  have hs : (Int64.size : Int) = 2 ^ 64 := rfl
  rw [hs]
  by_cases hx : 0 ≤ x
  · have hm : x % (2 ^ 64 : Int) = x := Int.emod_eq_of_lt hx (by omega)
    rw [hm]
    split <;> omega
  · have hm : x % (2 ^ 64 : Int) = x + 2 ^ 64 := by
      conv => lhs; rw [show x = (x + 2 ^ 64) + (2 ^ 64 : Int) * (-1) by omega]
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hm]
    split <;> omega

theorem toInt_ofInt32 {x : Int} (hlo : -(2 ^ 31 : Int) ≤ x) (hhi : x < 2 ^ 31) :
    (Int32.ofInt x).toInt = x := by
  rw [Int32.toInt_ofInt, Int.bmod]
  have hs : (Int32.size : Int) = 2 ^ 32 := rfl
  rw [hs]
  by_cases hx : 0 ≤ x
  · have hm : x % (2 ^ 32 : Int) = x := Int.emod_eq_of_lt hx (by omega)
    rw [hm]
    split <;> omega
  · have hm : x % (2 ^ 32 : Int) = x + 2 ^ 32 := by
      conv => lhs; rw [show x = (x + 2 ^ 32) + (2 ^ 32 : Int) * (-1) by omega]
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hm]
    split <;> omega

theorem i64Add_eq (a b : Int64) (hlo : -(2 ^ 63 : Int) ≤ a.toInt + b.toInt)
    (hhi : a.toInt + b.toInt < 2 ^ 63) :
    i64Add a b = pure (Int64.ofInt (a.toInt + b.toInt)) := by
  simp only [i64Add, checkI64, hlo, hhi, and_self, ↓reduceIte]

theorem i64Sub_eq (a b : Int64) (hlo : -(2 ^ 63 : Int) ≤ a.toInt - b.toInt)
    (hhi : a.toInt - b.toInt < 2 ^ 63) :
    i64Sub a b = pure (Int64.ofInt (a.toInt - b.toInt)) := by
  simp only [i64Sub, checkI64, hlo, hhi, and_self, ↓reduceIte]

theorem i64Mul_eq (a b : Int64) (hlo : -(2 ^ 63 : Int) ≤ a.toInt * b.toInt)
    (hhi : a.toInt * b.toInt < 2 ^ 63) :
    i64Mul a b = pure (Int64.ofInt (a.toInt * b.toInt)) := by
  simp only [i64Mul, checkI64, hlo, hhi, and_self, ↓reduceIte]

theorem i64Div_nonneg_eq (a b : Int64) (ha : 0 ≤ a.toInt) (hb : 0 < b.toInt) :
    i64Div a b = pure (Int64.ofInt (Int.tdiv a.toInt b.toInt)) := by
  have hb0 : (b == (0 : Int64)) = false := beq_false_of_ne (fun h => by subst h; simp at hb)
  have hle : Int.tdiv a.toInt b.toInt ≤ a.toInt := Int.tdiv_le_self b.toInt ha
  have hge : 0 ≤ Int.tdiv a.toInt b.toInt := Int.tdiv_nonneg ha (by omega)
  have halt := Int64.toInt_lt a
  have h1 : -(2 ^ 63 : Int) ≤ Int.tdiv a.toInt b.toInt := by omega
  have h2 : Int.tdiv a.toInt b.toInt < 2 ^ 63 := by omega
  have hne : (b.toInt == -1) = false := beq_false_of_ne (by omega)
  simp only [i64Div, checkI64, hb0, Bool.false_eq_true, ↓reduceIte, hne, and_false, h1, h2, and_self]

theorem i64Mod_nonneg_eq (a b : Int64) (ha : 0 ≤ a.toInt) (hb : 0 < b.toInt) :
    i64Mod a b = pure (Int64.ofInt (Int.tmod a.toInt b.toInt)) := by
  have hb0 : (b == (0 : Int64)) = false := beq_false_of_ne (fun h => by subst h; simp at hb)
  have hge : 0 ≤ Int.tmod a.toInt b.toInt := Int.tmod_nonneg b.toInt ha
  have hle : Int.tmod a.toInt b.toInt < b.toInt := by
    rw [Int.tmod_eq_emod_of_nonneg ha]
    exact Int.emod_lt_of_pos a.toInt hb
  have hblt := Int64.toInt_lt b
  have h1 : -(2 ^ 63 : Int) ≤ Int.tmod a.toInt b.toInt := by omega
  have h2 : Int.tmod a.toInt b.toInt < 2 ^ 63 := by omega
  have hne : (b.toInt == -1) = false := beq_false_of_ne (by omega)
  simp only [i64Mod, checkI64, hb0, Bool.false_eq_true, ↓reduceIte, hne, and_false, h1, h2, and_self]

theorem i32Mul_eq (a b : Int32) (hlo : -(2 ^ 31 : Int) ≤ a.toInt * b.toInt)
    (hhi : a.toInt * b.toInt < 2 ^ 31) :
    i32Mul a b = pure (Int32.ofInt (a.toInt * b.toInt)) := by
  simp only [i32Mul, checkI32, hlo, hhi, and_self, ↓reduceIte]

theorem i32Mod_nonneg_eq (a b : Int32) (ha : 0 ≤ a.toInt) (hb : 0 < b.toInt) :
    i32Mod a b = pure (Int32.ofInt (Int.tmod a.toInt b.toInt)) := by
  have hb0 : (b == (0 : Int32)) = false := beq_false_of_ne (fun h => by subst h; simp at hb)
  have hge : 0 ≤ Int.tmod a.toInt b.toInt := Int.tmod_nonneg b.toInt ha
  have hle : Int.tmod a.toInt b.toInt < b.toInt := by
    rw [Int.tmod_eq_emod_of_nonneg ha]
    exact Int.emod_lt_of_pos a.toInt hb
  have hblt := Int32.toInt_lt b
  have h1 : -(2 ^ 31 : Int) ≤ Int.tmod a.toInt b.toInt := by omega
  have h2 : Int.tmod a.toInt b.toInt < 2 ^ 31 := by omega
  have hne : (b.toInt == -1) = false := beq_false_of_ne (by omega)
  simp only [i32Mod, checkI32, hb0, Bool.false_eq_true, ↓reduceIte, hne, and_false, h1, h2, and_self]

end C
