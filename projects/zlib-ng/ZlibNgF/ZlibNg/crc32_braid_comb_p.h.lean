import ZlibNgF.Runtime.Libc
import ZlibNgF.ZlibNg.«crc32_braid_tbl.h»

/-!
# `crc32_braid_comb_p.h` — GF(2) CRC-32 polynomial helpers (`ZlibNgF`)

Source: `zlib-ng/crc32_braid_comb_p.h` and `zlib-ng/crc32_braid_p.h` (`POLY = 0xedb88320`).
-/

set_option autoImplicit false

namespace ZlibNg.Crc32CombP
open C

/-- `#define POLY 0xedb88320` (`crc32_braid_p.h:38`). -/
def POLY : UInt32 := 0xedb88320

/-- Read `x2n_table[i]` from static read-only `st_x2n_table`. -/
def x2nTab (i : UInt32) : M UInt32 :=
  Ptr.index (Ptr.ref URef.st_x2n_table 0) (Int.ofNat i.toNat)

/-- `static uint32_t multmodp(uint32_t a, uint32_t b)` (`crc32_braid_comb_p.h:8-23`). -/
def multmodp (a b : UInt32) : M UInt32 := do
  let (_, p, _, _) ← cwhile
    (fun ((m, p, b, brk) : UInt32 × UInt32 × UInt32 × Bool) => pure (!brk, (m, p, b, brk)))
    (fun ((m, p, b, brk) : UInt32 × UInt32 × UInt32 × Bool) => do
      let mut p := p
      if a &&& m != 0 then
        p := p ^^^ b
        if a &&& (m - 1) == 0 then
          return (m, p, b, true)
      let m := m >>> 1
      let b := if b &&& 1 != 0 then (b >>> 1) ^^^ POLY else b >>> 1
      pure (m, p, b, brk))
    (((1 : UInt32) <<< 31, (0 : UInt32), b, false))
  return p

/-- `static uint32_t x2nmodp(z_off64_t n, unsigned k)` (`crc32_braid_comb_p.h:29-40`). -/
def x2nmodp (n : Int64) (k : UInt32) : M UInt32 := do
  let (p, _, _) ← cwhile
    (fun ((p, n, k) : UInt32 × Int64 × UInt32) => pure (n != 0, (p, n, k)))
    (fun ((p, n, k) : UInt32 × Int64 × UInt32) => do
      let mut p := p
      if n &&& 1 != 0 then
        let t ← x2nTab (k &&& 31)
        p ← multmodp t p
      pure (p, n >>> 1, k + 1))
    (((1 : UInt32) <<< 31, n, k))
  return p

end ZlibNg.Crc32CombP
