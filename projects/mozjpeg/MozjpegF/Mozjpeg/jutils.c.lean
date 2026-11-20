import MozjpegF.Mozjpeg.«jpeglib.h»

/-!
# `jutils.c` — faithful statement-by-statement translation (`MozjpegF`)

Source: `mozjpeg/jutils.c`, LP64 Linux build (`BITS_IN_JSAMPLE == 8`, `WITH_JPEG8 == 1`).
-/

set_option autoImplicit false

namespace Mozjpeg.Jutils
open C Mozjpeg.JpeglibH

/-- `const int jpeg_natural_order[DCTSIZE2 + 16]` (`jutils.c:59-70`). -/
def jpeg_natural_order : Array Int32 := #[
   0,  1,  8, 16,  9,  2,  3, 10,
  17, 24, 32, 25, 18, 11,  4,  5,
  12, 19, 26, 33, 40, 48, 41, 34,
  27, 20, 13,  6,  7, 14, 21, 28,
  35, 42, 49, 56, 57, 50, 43, 36,
  29, 22, 15, 23, 30, 37, 44, 51,
  58, 59, 52, 45, 38, 31, 39, 46,
  53, 60, 61, 54, 47, 55, 62, 63,
  63, 63, 63, 63, 63, 63, 63, 63,
  63, 63, 63, 63, 63, 63, 63, 63
]

/-- `long jdiv_round_up(long a, long b)` (`jutils.c:77-83`).
Computes `ceil(a/b)` via `(a + b - 1L) / b`; raises `Fault.ub` on signed overflow or `b == 0`. -/
def jdiv_round_up (a b : Int64) : M Int64 := do
  let ab ← i64Add a b
  let num ← i64Sub ab 1
  i64Div num b

/-- `long jround_up(long a, long b)` (`jutils.c:86-93`).
Computes `ceil(a/b)*b` via `a += b - 1L; return a - (a % b);`; raises `Fault.ub` on signed overflow or `b == 0`. -/
def jround_up (a b : Int64) : M Int64 := do
  let bm1 ← i64Sub b 1
  let a1 ← i64Add a bm1
  let rem ← i64Mod a1 b
  i64Sub a1 rem

/-- `void jzero_far(void *target, size_t bytestozero)` (`jutils.c:140-146`).
Calls `memset(target, 0, bytestozero)`, faulting under strict ISO C17 on NULL or dangling `target`
even when `bytestozero == 0`. -/
def jzero_far (target : BPtr) (bytestozero : UInt64) : M Unit :=
  Ptr.memset target 0 bytestozero.toNat

end Mozjpeg.Jutils
