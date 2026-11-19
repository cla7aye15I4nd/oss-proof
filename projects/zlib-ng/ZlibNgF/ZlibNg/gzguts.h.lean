import ZlibNgF.Runtime.Gz
import ZlibNgF.ZlibNg.«deflate.c»

/-!
# `gzguts.h` — constants of the gz* files (`ZlibNgF`)

Source: `zlib-ng/gzguts.h` with patch 0004 (`GZ_OFF_MAX`); x86_64 Linux LP64 (`z_off64_t` is `long`, so `GT_OFF(x)`
is false). The `gz_state` structure is `C.GzState` (`Runtime/Gz.lean`).

Control flow of the translations: a loop is `gwhile` / `gdoWhile` over a record of its locals; a `break` or a
`return` inside the loop sets the field `ctl` (`Ctl.brk`, `Ctl.ret`), which ends the loop without evaluating the
condition again, and the code after the loop returns when `ctl = Ctl.ret`. A `continue` ends the body (the
condition is evaluated). A condition `a && b` or `a || b` whose second operand can fault or has an effect is
written as nested `if`s, so that the operand is evaluated only when the C evaluates it; reads of fields of the live
`gz_state` and of its embedded `z_stream`, which cannot fault and have no effect, are hoisted out of conditions.
-/

set_option autoImplicit false

namespace ZlibNg.Gz
open C

/-- `GZBUFSIZE` -/
def GZBUFSIZE : UInt32 := 131072
/-- `GZBUFSIZE_MAX` (`1u << 30`) -/
def GZBUFSIZE_MAX : UInt32 := (1 : UInt32) <<< 30

/-- gzip modes -/
def GZ_NONE : Int32 := 0
def GZ_READ : Int32 := 7247
def GZ_WRITE : Int32 := 31153
def GZ_APPEND : Int32 := 1

/-- values of `how` -/
def LOOK : Int32 := 0
def COPY : Int32 := 1
def GZIP : Int32 := 2

/-- `GT_OFF(x)`: `sizeof(int) == sizeof(z_off64_t) && (x) > INT_MAX`, false on LP64. -/
def GT_OFF (_x : UInt32) : Bool := false

/-- `GZ_OFF_MAX` (patch 0004; patch 0016 defines it in `gzread.c` too, when `gzguts.h` does not): `(z_off64_t)((~(uint64_t)0) >> (65 - sizeof(z_off64_t) * 8))` = `2^63 - 1`. -/
def GZ_OFF_MAX : Int64 := Int64.ofInt (2 ^ 63 - 1)

/-- `Z_ERRNO` -/
def Z_ERRNO : Int32 := -1

/-- `ZLIB_VERSION` (`zlib.h`), passed by the `inflateInit2` / `deflateInit2` macros. -/
def ZLIB_VERSION : String := "1.3.2.zlib-ng"

/-- How a loop body ended: normally (or by `continue`), by `break`, or by `return`. -/
inductive Ctl where
  | go
  | brk
  | ret
  deriving DecidableEq, Inhabited

end ZlibNg.Gz
