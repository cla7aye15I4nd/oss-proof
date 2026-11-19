import ZlibNgF.ZlibNg.«insert_string_p.h»

/-!
# `arch/generic/compare256_c.c` and `match_tpl.h` — match length and longest match (`ZlibNgF`)

Source: `zlib-ng/arch/generic/compare256_c.c` (`COMPARE256_FALLBACK` defined: no SIMD in the verified build;
`OPTIMAL_CMP == 64` on x86_64, so `COMPARE256` is `compare256_64_static`) with its three inclusions of
`zlib-ng/match_tpl.h`:
* `LONGEST_MATCH = longest_match_c` (neither flag),
* `LONGEST_MATCH = longest_match_slow_knuth_c` (`LONGEST_MATCH_SLOW`),
* `LONGEST_MATCH = longest_match_slow_roll_c` (`LONGEST_MATCH_SLOW` and `LONGEST_MATCH_SLOW_ROLL`).
The template is one function `LONGEST_MATCH slow roll` whose two flags select the preprocessor branches; the
three C functions are thin wrappers. No `ZLIB_DEBUG`: `Assert` is empty. Little-endian: `Z_U32_FROM_LE` is the
identity.

## Control flow of `LONGEST_MATCH`
The mutable locals are the record `LMVars`; the locals that do not change after the prologue are `LMEnv`. The
outer `for (;;)` (`match_tpl.h:138-295`) is a `cwhile` whose body (`LM.loop_body`) ends with one of
* `LMExit.cont`: the next trip (`continue` of `GOTO_NEXT_CHAIN` at `:294` or of the offset search at `:289`);
* `LMExit.brk`: `break` at `:140`, after which the function returns `best_len` (`:296`);
* `LMExit.ret v`: a `return v` inside the loop.
Inside a trip the candidate filter (`:150-195`) ends with `LMSel.compare` (fall through to `COMPARE256`, `:197`),
`LMSel.accept len` (`goto short_match_accept`) or `LMSel.ret v` (a `return`). The block at the label
`short_match_accept` is `LM.short_match_accept`; `GOTO_NEXT_CHAIN` at `:294` is `LM.goto_next_chain`. The inner
`for (;;)` loops at `:169` and `:187` are `cwhile`s; the `continue` of `GOTO_NEXT_CHAIN` at `:193` continues the inner
loop at `:187`.

## Pointers
Every pointer the C computes is computed with `Ptr.add` at the same point: `mbase_start -= match_offset` (`:133`),
`mbase_end -= match_offset` (`:134`) and `mbase_start = window - match_offset` (`:287`) form pointers before
`window`, which fault when they fall before the start of the block of `alloc_deflate` (ISO C17 §6.5.6p8).
`mbase_start+cur_match+2`, `scan + len - k` are two pointer additions each, evaluated left to right as in C.
`zng_memcmp_8(p, &scan_end)` compares the 8 bytes at `p` with the 8 bytes of the local `uint64_t`
(`zng_memcmp_8_local`).
-/

set_option autoImplicit false

namespace ZlibNg.Compare256
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.InsertStringP

/-! ## `compare256_c.c` -/

/-- `Z_FORCEINLINE static uint32_t compare256_8_static(const uint8_t *src0, const uint8_t *src1)`
(`compare256_c.c:16-40`). Loop state `(src0, src1, len, r)`; `r = some v` is `return v` inside the body. -/
def compare256_8_static (src0 src1 : BPtr) : M UInt32 := do
  let (_, _, _, r) ← cdoWhile
    (fun ((src0, src1, len, _) : BPtr × BPtr × UInt32 × Option UInt32) => do
      if (← index8 src0 0) != (← index8 src1 0) then return (src0, src1, len, some len)
      if (← index8 src0 1) != (← index8 src1 1) then return (src0, src1, len, some (len + 1))
      if (← index8 src0 2) != (← index8 src1 2) then return (src0, src1, len, some (len + 2))
      if (← index8 src0 3) != (← index8 src1 3) then return (src0, src1, len, some (len + 3))
      if (← index8 src0 4) != (← index8 src1 4) then return (src0, src1, len, some (len + 4))
      if (← index8 src0 5) != (← index8 src1 5) then return (src0, src1, len, some (len + 5))
      if (← index8 src0 6) != (← index8 src1 6) then return (src0, src1, len, some (len + 6))
      if (← index8 src0 7) != (← index8 src1 7) then return (src0, src1, len, some (len + 7))
      let src0 ← src0.add 8
      let src1 ← src1.add 8
      return (src0, src1, len + 8, none))
    (fun ((src0, src1, len, r) : BPtr × BPtr × UInt32 × Option UInt32) =>
      pure (r.isNone && len < 256, (src0, src1, len, r)))
    (src0, src1, (0 : UInt32), none)
  match r with
  | some v => return v
  | none => return 256

/-- `Z_FORCEINLINE static uint32_t compare256_64_static(const uint8_t *src0, const uint8_t *src1)`
(`compare256_c.c:43-63`). Loop state `(src0, src1, len, r)`; `r = some v` is `return v` inside the body. -/
def compare256_64_static (src0 src1 : BPtr) : M UInt32 := do
  let (_, _, _, r) ← cdoWhile
    (fun ((src0, src1, len, _) : BPtr × BPtr × UInt32 × Option UInt32) => do
      let sv ← memread8 src0
      let mv ← memread8 src1
      let diff := sv ^^^ mv
      if diff != 0 then return (src0, src1, len, some (len + (← zng_first_diff_byte64 diff)))
      let src0 ← src0.add 8
      let src1 ← src1.add 8
      let len := len + 8
      let sv ← memread8 src0
      let mv ← memread8 src1
      let diff := sv ^^^ mv
      if diff != 0 then return (src0, src1, len, some (len + (← zng_first_diff_byte64 diff)))
      let src0 ← src0.add 8
      let src1 ← src1.add 8
      return (src0, src1, len + 8, none))
    (fun ((src0, src1, len, r) : BPtr × BPtr × UInt32 × Option UInt32) =>
      pure (r.isNone && len < 256, (src0, src1, len, r)))
    (src0, src1, (0 : UInt32), none)
  match r with
  | some v => return v
  | none => return 256

/-- `Z_INTERNAL uint32_t compare256_8(const uint8_t *src0, const uint8_t *src1)` (`compare256_c.c:71-73`). -/
def compare256_8 (src0 src1 : BPtr) : M UInt32 := compare256_8_static src0 src1

/-- `Z_INTERNAL uint32_t compare256_64(const uint8_t *src0, const uint8_t *src1)` (`compare256_c.c:75-77`). -/
def compare256_64 (src0 src1 : BPtr) : M UInt32 := compare256_64_static src0 src1

/-- `Z_INTERNAL uint32_t compare256_c(const uint8_t *src0, const uint8_t *src1)` (`compare256_c.c:79-81`):
`COMPARE256` is `compare256_64_static` (`OPTIMAL_CMP == 64`). -/
def compare256_c (src0 src1 : BPtr) : M UInt32 := compare256_64_static src0 src1

/-- `Z_FORCEINLINE static int32_t zng_memcmp_8(const void *src0, const void *src1)` (`zmemory.h:91-97`, the
`HAVE_MAY_ALIAS` branch: `zng_memread_8(src0) != zng_memread_8(src1)`) with `src1 = &v` the address of a local
`uint64_t`: reading its 8 bytes gives `v`. -/
def zng_memcmp_8_local (src0 : BPtr) (v : UInt64) : M Int32 := do
  let a ← memread8 src0
  return if a != v then 1 else 0

/-! ## `match_tpl.h` -/

/-- The locals of `LONGEST_MATCH` that do not change after the prologue. `head` is read only with
`LONGEST_MATCH_SLOW` (`.null` otherwise, never used); `limit_base` and `offset_search` exist only with
`LONGEST_MATCH_SLOW`. -/
structure LMEnv where
  slow : Bool
  roll : Bool
  st : StatePtr
  wmask : UInt32
  strstart : UInt32
  window : BPtr
  prev : BPtr
  head : BPtr
  scan : BPtr
  limit_base : UInt32
  nice_match : UInt32
  lookahead : UInt32
  scan_start : UInt64
  offset_search : Bool

/-- The mutable locals of `LONGEST_MATCH`. -/
structure LMVars where
  chain_length : UInt32
  best_len : UInt32
  offset : UInt32
  cur_match : UInt32
  match_offset : UInt32
  scan_end : UInt64
  mbase_start : BPtr
  mbase_end : BPtr
  limit : UInt32

/-- How a trip of the outer `for (;;)` of `LONGEST_MATCH` ends. -/
inductive LMExit where
  | cont
  | brk
  | ret (v : UInt32)

/-- How the candidate filter of a trip (`match_tpl.h:150-195`) ends. -/
inductive LMSel where
  | compare
  | accept (len : UInt32)
  | ret (v : UInt32)

/-- `LMExit.cont`: the outer loop runs another trip. -/
def LMExit.isCont : LMExit → Bool
  | .cont => true
  | _ => false

namespace LM

/-- `GOTO_NEXT_CHAIN` (`match_tpl.h:13-16`):
`if (--chain_length && (cur_match = prev[cur_match & wmask]) > limit) continue; return best_len;`.
`none` is `continue` (of the innermost loop), `some v` is `return v`. -/
def GOTO_NEXT_CHAIN (e : LMEnv) (v : LMVars) : M (Option UInt32 × LMVars) := do
  let v := { v with chain_length := v.chain_length - 1 }
  if v.chain_length != 0 then
    let v := { v with cur_match := (← posLoad e.prev (v.cur_match &&& e.wmask).toNat).toUInt32 }
    if v.cur_match > v.limit then return (none, v)
    return (some v.best_len, v)
  return (some v.best_len, v)

/-- `GOTO_NEXT_CHAIN` at `match_tpl.h:294`, whose `continue` is that of the outer `for (;;)`. -/
def goto_next_chain_outer (e : LMEnv) (v : LMVars) : M (LMExit × LMVars) := do
  let (r, v) ← GOTO_NEXT_CHAIN e v
  match r with
  | none => return (.cont, v)
  | some x => return (.ret x, v)

/-- The inner `for (;;)` of `match_tpl.h:169-180` (candidates after the first two, while `best_len < 8`). Loop
state `(v, cand_start, r)`; `r = some x` ends the loop: `goto short_match_accept` (`.accept`), `return` (`.ret`)
or `break` (`.compare`). -/
def short_walk (e : LMEnv) (first_mask : UInt64) (v : LMVars) (cand_start : UInt64) : M (LMSel × LMVars) := do
  let (v, _, r) ← cwhile
    (fun ((v, c, r) : LMVars × UInt64 × Option LMSel) => pure (r.isNone, (v, c, r)))
    (fun ((v, cand_start, _) : LMVars × UInt64 × Option LMSel) => do
      let diff := e.scan_start ^^^ cand_start
      if diff &&& first_mask == 0 then
        let len ← zng_first_diff_byte64 diff
        return (v, cand_start, some (.accept len))
      let v := { v with chain_length := v.chain_length - 1 }
      if v.chain_length == 0 then return (v, cand_start, some (.ret v.best_len))
      let v := { v with cur_match := (← posLoad e.prev (v.cur_match &&& e.wmask).toNat).toUInt32 }
      if v.cur_match <= v.limit then return (v, cand_start, some (.ret v.best_len))
      let cand_start ← memread8 (← v.mbase_start.add v.cur_match.toNat)
      if e.scan_start == cand_start then return (v, cand_start, some .compare)
      return (v, cand_start, none))
    (v, cand_start, none)
  return (r.getD .compare, v)

/-- The candidate filter for `best_len < sizeof(uint64_t)` (`match_tpl.h:150-183`). -/
def short_filter (e : LMEnv) (v : LMVars) : M (LMSel × LMVars) := do
  let cand_start ← memread8 (← v.mbase_start.add v.cur_match.toNat)
  if e.scan_start != cand_start then
    let first_mask ← zng_first_bytes_mask64 (v.best_len + 1)
    let diff := e.scan_start ^^^ cand_start
    if diff &&& first_mask == 0 then
      let len ← zng_first_diff_byte64 diff
      return (.accept len, v)
    let v := { v with chain_length := v.chain_length - 1 }
    if v.chain_length == 0 then return (.ret v.best_len, v)
    let v := { v with cur_match := (← posLoad e.prev (v.cur_match &&& e.wmask).toNat).toUInt32 }
    if v.cur_match <= v.limit then return (.ret v.best_len, v)
    let cand_start ← memread8 (← v.mbase_start.add v.cur_match.toNat)
    if e.scan_start != cand_start then
      return ← short_walk e first_mask v cand_start
    return (.compare, v)
  return (.compare, v)

/-- The candidate filter for `best_len >= sizeof(uint64_t)`: the `for (;;)` of `match_tpl.h:187-194`. Loop state
`(v, r)`; `r = some x` ends the loop (`break` is `.compare`, `return` is `.ret`). The `&&` evaluates its second
operand only when the first is true. -/
def long_filter (e : LMEnv) (v : LMVars) : M (LMSel × LMVars) := do
  let (v, r) ← cwhile
    (fun ((v, r) : LMVars × Option LMSel) => pure (r.isNone, (v, r)))
    (fun ((v, _) : LMVars × Option LMSel) => do
      if (← zng_memcmp_8_local (← v.mbase_end.add v.cur_match.toNat) v.scan_end) == 0 then
        if (← zng_memcmp_8_local (← v.mbase_start.add v.cur_match.toNat) e.scan_start) == 0 then
          return (v, some .compare)
      let (x, v) ← GOTO_NEXT_CHAIN e v
      match x with
      | none => return (v, none)
      | some b => return (v, some (.ret b)))
    (v, none)
  return (r.getD .compare, v)

/-- The look for a better string offset of `LONGEST_MATCH_SLOW` (`match_tpl.h:222-290`), entered when
`offset_search && len > STD_MIN_MATCH && match_start + len < strstart`; it ends with `continue` of the outer loop or
a `return`. The `for` over `i` has loop state `(i, next_pos, match_offset, r)`; `r = some x` is `return x`. -/
def offset_search_block (e : LMEnv) (v : LMVars) (len : UInt32) : M (LMExit × LMVars) := do
  let mut v := v
  v := { v with cur_match := v.cur_match - v.match_offset }
  v := { v with match_offset := 0 }
  let next_pos := v.cur_match
  let bound := if e.roll then len - STD_MIN_MATCH else len - WANT_MIN_MATCH
  let cur_match := v.cur_match
  let best_len := v.best_len
  let (_, next_pos, match_offset, r) ← cwhile
    (fun ((i, np, mo, r) : UInt32 × UInt32 × UInt32 × Option UInt32) =>
      pure (r.isNone && i <= bound, (i, np, mo, r)))
    (fun ((i, next_pos, match_offset, _) : UInt32 × UInt32 × UInt32 × Option UInt32) => do
      let pos := (← posLoad e.prev ((cur_match + i) &&& e.wmask).toNat).toUInt32
      if pos < next_pos then
        if pos <= e.limit_base + i then return (i, next_pos, match_offset, some best_len)
        return (i + 1, pos, i, none)
      return (i + 1, next_pos, match_offset, none))
    ((0 : UInt32), next_pos, v.match_offset, none)
  v := { v with match_offset := match_offset }
  if let some x := r then return (.ret x, v)
  v := { v with cur_match := next_pos }
  if e.roll then
    let scan_endstr ← (← e.scan.add len.toNat).add (-((STD_MIN_MATCH - 1).toNat : Int))
    let hash := update_hash_roll 0 (← index8 scan_endstr 0).toUInt32
    let hash := update_hash_roll hash (← index8 scan_endstr 1).toUInt32
    let hash := update_hash_roll hash (← index8 scan_endstr 2).toUInt32
    let pos := (← posLoad e.head hash.toNat).toUInt32
    if pos < v.cur_match then
      v := { v with match_offset := len - (STD_MIN_MATCH - 1) }
      if pos <= e.limit_base + v.match_offset then return (.ret v.best_len, v)
      v := { v with cur_match := pos }
  else
    let scan_endstr ← (← e.scan.add len.toNat).add (-(WANT_MIN_MATCH.toNat : Int))
    let val ← memread4 scan_endstr
    let hash := UPDATE_HASH_KNUTH val
    let pos := (← posLoad e.head hash.toNat).toUInt32
    if pos < v.cur_match then
      v := { v with match_offset := len - WANT_MIN_MATCH }
      if pos <= e.limit_base + v.match_offset then return (.ret v.best_len, v)
      v := { v with cur_match := pos }
  v := { v with limit := e.limit_base + v.match_offset }
  v := { v with mbase_start := ← e.window.add (-(v.match_offset.toNat : Int)) }
  v := { v with mbase_end := ← v.mbase_start.add v.offset.toNat }
  return (.cont, v)

/-- The block at the label `short_match_accept` (`match_tpl.h:201-293`), followed by `GOTO_NEXT_CHAIN` at `:294`. -/
def short_match_accept (e : LMEnv) (v : LMVars) (len : UInt32) : M (LMExit × LMVars) := do
  let match_start := v.cur_match - v.match_offset
  wrD e.st fun s => { s with match_start := match_start }
  if len >= e.lookahead then return (.ret e.lookahead, v)
  if len >= e.nice_match then return (.ret len, v)
  let v := { v with best_len := len }
  let v := { v with offset := if v.best_len >= 8 then v.best_len - 7 else 0 }
  let v := { v with scan_end := ← memread8 (← e.scan.add v.offset.toNat) }
  if e.slow then
    if e.offset_search && len > STD_MIN_MATCH && match_start + len < e.strstart then
      return ← offset_search_block e v len
  let v := { v with mbase_end := ← v.mbase_start.add v.offset.toNat }
  goto_next_chain_outer e v

/-- One trip of the outer `for (;;)` of `LONGEST_MATCH` (`match_tpl.h:139-294`). -/
def loop_body (e : LMEnv) (v : LMVars) : M (LMExit × LMVars) := do
  if v.cur_match >= e.strstart then return (.brk, v)
  let (sel, v) ← if v.best_len < 8 then short_filter e v else long_filter e v
  match sel with
  | .ret x => return (.ret x, v)
  | .accept len => short_match_accept e v len
  | .compare =>
    let a ← e.scan.add 2
    let b ← (← v.mbase_start.add v.cur_match.toNat).add 2
    let len := (← compare256_64_static a b) + 2
    if len > v.best_len then short_match_accept e v len
    else goto_next_chain_outer e v

end LM

/-- `Z_INTERNAL uint32_t LONGEST_MATCH(deflate_state *const s, uint32_t cur_match)` (`match_tpl.h:26-297`), with
`slow` = `LONGEST_MATCH_SLOW` and `roll` = `LONGEST_MATCH_SLOW_ROLL` (meaningful only with `slow`). The fields of
`*s` are read from one load of the record: no store to `*s` precedes them. The two prologue loops of
`LONGEST_MATCH_SLOW` have loop state `(i, hash, match_offset, cur_match)` / `(i, match_offset, cur_match)`. -/
def LONGEST_MATCH (slow roll : Bool) (st : StatePtr) (cur_match : UInt32) : M UInt32 := do
  let s ← ldDState st
  let wmask := W_MASK s
  let strstart := s.strstart
  let window ← s.window.get
  let prev ← s.prev.get
  let head ← if slow then s.head.get else pure .null
  let mut mbase_start := window
  let chain_length := s.max_chain_length
  let nice_match := s.nice_match.toUInt32
  let lookahead := s.lookahead
  let mut match_offset : UInt32 := 0
  let mut cur_match := cur_match
  let best_len : UInt32 :=
    if slow then (if s.prev_length != 0 then s.prev_length else STD_MIN_MATCH - 1) else STD_MIN_MATCH - 1
  if slow then
    if best_len >= lookahead then return lookahead
  let offset_search : Bool := slow && (roll || best_len >= STD_MIN_MATCH)
  let offset : UInt32 := if best_len >= 8 then best_len - 7 else 0
  let scan ← window.add strstart.toNat
  let scan_start ← memread8 scan
  let scan_end ← memread8 (← scan.add offset.toNat)
  let mut mbase_end ← mbase_start.add offset.toNat
  let chain_length := if best_len >= s.good_match then chain_length >>> 2 else chain_length
  let mut limit : UInt32 := if strstart > MAX_DIST s then strstart - MAX_DIST s else 0
  let limit_base := limit
  if slow then
    if best_len >= STD_MIN_MATCH then
      if roll then
        let hash := update_hash_roll 0 (← index8 scan 1).toUInt32
        let hash := update_hash_roll hash (← index8 scan 2).toUInt32
        let (_, _, mo, cm) ← cwhile
          (fun ((i, hash, mo, cm) : UInt32 × UInt32 × UInt32 × UInt32) => pure (i <= best_len, (i, hash, mo, cm)))
          (fun ((i, hash, mo, cm) : UInt32 × UInt32 × UInt32 × UInt32) => do
            let hash := update_hash_roll hash (← index8 scan i.toNat).toUInt32
            let pos := (← posLoad head hash.toNat).toUInt32
            if pos < cm then return (i + 1, hash, i - 2, pos)
            return (i + 1, hash, mo, cm))
          ((3 : UInt32), hash, match_offset, cur_match)
        match_offset := mo
        cur_match := cm
      else
        let (_, mo, cm) ← cwhile
          (fun ((i, mo, cm) : UInt32 × UInt32 × UInt32) => pure (i + (WANT_MIN_MATCH - 1) <= best_len, (i, mo, cm)))
          (fun ((i, mo, cm) : UInt32 × UInt32 × UInt32) => do
            let val ← memread4 (← scan.add i.toNat)
            let hash := UPDATE_HASH_KNUTH val
            let pos := (← posLoad head hash.toNat).toUInt32
            if pos < cm then return (i + 1, i, pos)
            return (i + 1, mo, cm))
          ((1 : UInt32), match_offset, cur_match)
        match_offset := mo
        cur_match := cm
      limit := limit_base + match_offset
      if cur_match <= limit then return best_len
      mbase_start ← mbase_start.add (-(match_offset.toNat : Int))
      mbase_end ← mbase_end.add (-(match_offset.toNat : Int))
  let e : LMEnv := {
    slow, roll, st, wmask, strstart, window, prev, head, scan, limit_base, nice_match, lookahead, scan_start,
    offset_search }
  let v : LMVars := {
    chain_length, best_len, offset, cur_match, match_offset, scan_end, mbase_start, mbase_end, limit }
  let (x, v) ← cwhile
    (fun ((x, v) : LMExit × LMVars) => pure (x.isCont, (x, v)))
    (fun ((_, v) : LMExit × LMVars) => LM.loop_body e v)
    (LMExit.cont, v)
  match x with
  | .ret r => return r
  | _ => return v.best_len

/-- `Z_INTERNAL uint32_t longest_match_c(deflate_state *const s, uint32_t cur_match)` (`compare256_c.c:83-84`,
`match_tpl.h` without `LONGEST_MATCH_SLOW`). -/
def longest_match_c (st : StatePtr) (cur_match : UInt32) : M UInt32 :=
  LONGEST_MATCH false false st cur_match

/-- `Z_INTERNAL uint32_t longest_match_slow_knuth_c(deflate_state *const s, uint32_t cur_match)`
(`compare256_c.c:86-88`, `match_tpl.h` with `LONGEST_MATCH_SLOW`). -/
def longest_match_slow_knuth_c (st : StatePtr) (cur_match : UInt32) : M UInt32 :=
  LONGEST_MATCH true false st cur_match

/-- `Z_INTERNAL uint32_t longest_match_slow_roll_c(deflate_state *const s, uint32_t cur_match)`
(`compare256_c.c:90-93`, `match_tpl.h` with `LONGEST_MATCH_SLOW` and `LONGEST_MATCH_SLOW_ROLL`). -/
def longest_match_slow_roll_c (st : StatePtr) (cur_match : UInt32) : M UInt32 :=
  LONGEST_MATCH true true st cur_match

/-- `longest_match(s, cur_match)` with `longest_match_func longest_match = s->longest_match` (`deflate.h:155`): a call
through the function pointer, to the function the value designates (`lm_set_level` stores
`FUNCTABLE_FPTR(longest_match_slow_roll)` = `longest_match_slow_roll_c` or `FUNCTABLE_FPTR(longest_match_slow_knuth)`
= `longest_match_slow_knuth_c`). -/
def call_longest_match (f : LongestMatchFn) (st : StatePtr) (cur_match : UInt32) : M UInt32 :=
  match f with
  | .longest_match_slow_knuth_c => longest_match_slow_knuth_c st cur_match
  | .longest_match_slow_roll_c => longest_match_slow_roll_c st cur_match

end ZlibNg.Compare256

