import ZlibNgF.ZlibNg.«deflate.c.fill_window»

/-!
# `deflate_medium_tpl.h` — the medium strategy of deflate, template (`ZlibNgF`)

Source: `zlib-ng/deflate_medium_tpl.h`, included twice by `zlib-ng/deflate_medium.c` (`NO_MEDIUM_STRATEGY` is
undefined in the verified build): once with `SUFFIX(name) = name` and `USE_FIZZLE` undefined, once with
`SUFFIX(name) = name ## _fizzle` and `USE_FIZZLE` defined. No `ZLIB_DEBUG`, so `check_match` is empty; `LIKELY` /
`UNLIKELY` are branch hints; `ALIGNED_(16)` does not change the semantics. `FUNCTABLE_CALL(longest_match)` =
`longest_match_c`; `PREFIX(fill_window)` = `fill_window`.

## One Lean function per template function
`insert_match` and `find_best_match` do not test `USE_FIZZLE`: `SUFFIX(insert_match)` / `insert_match_fizzle` and
`SUFFIX(find_best_match)` / `find_best_match_fizzle` have the same body and are one Lean function each.
`fizzle_matches` exists only with `USE_FIZZLE`. `SUFFIX(deflate_medium)` is `deflate_medium_tpl fizzle`, where the
flag `fizzle` selects the branches of `#ifdef USE_FIZZLE`. `struct match` of `deflate_medium.c:12-17` is `Match`,
defined here because the template uses it.

## Control flow
The outer `for (;;)` (`deflate_medium_tpl.h:179-324`) is a `cwhile` whose body (`deflate_medium_trip`) is one trip
and ends with a `Ctl`: `cont` (next trip, also the `continue` at `:248`), `brk` (`break` at `:194`) or `ret r`
(`return need_more` at `:191`, or the `return` inside `FLUSH_BLOCK`). The inner `for (;;)` of max-length
continuations (`:285-319`) is a `cwhile` whose body is `deflate_medium_cont_trip`. `current_match` and `next_match`
are function-scope locals threaded through the outer loop (without `USE_FIZZLE` the model still carries
`next_match`, which no statement then reads or writes); `bflush` and `curr_match_len` are locals of one trip.

## Pointers
In `fizzle_matches`, `window + next->match_start + 1 - current->match_length` is the three pointer additions
`((window + next->match_start) + 1) - current->match_length`, each a `Ptr.add`, in C's left-to-right order; the same
for `orig` and for the two pointers of the extra-byte test. Each faults (ISO C17 §6.5.6p8) if it leaves
`[0, size]` of the block of `alloc_deflate`, whether or not it is dereferenced.

## Uninitialised locals and the `fizzle_matches` out-parameters
`struct match m;` of `find_best_match` and `struct match cont_match;` of the continuation loop are uninitialised;
every member is written before it is read, so the model's starting value (`default`, all zero) is not observable.
`uint32_t curr_match_len;` is written on every path before its first read; the model starts it at `0`.
`fizzle_matches` takes `struct match *current` and `*next`, two locals of `deflate_medium`; they are passed by value
and returned (normalisation 1).
-/

set_option autoImplicit false

namespace ZlibNg.DeflateMedium
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.InsertStringP ZlibNg.InsertString ZlibNg.Compare256

/-- `struct match { uint32_t match_start; uint32_t match_length; uint32_t strstart; uint32_t orgstart; };`
(`deflate_medium.c:12-17`). -/
structure Match where
  match_start : UInt32
  match_length : UInt32
  strstart : UInt32
  orgstart : UInt32
  deriving DecidableEq, Repr, Inhabited

/-- How one trip of a `for (;;)` loop ends: the next trip, `break`/`continue` as named, or `return r`. -/
inductive Ctl where
  | cont
  | brk
  | ret (r : BlockState)
  deriving DecidableEq, Repr, Inhabited

/-- `int memcmp(const void *s1, const void *s2, size_t n)` (ISO C17 §7.24.4.1; §7.1.4p1, §7.24.1p2): both arguments
must point to live objects with `n` accessible bytes (checked by forming `s1 + n` and `s2 + n`, which also faults on
`NULL`, even for `n = 0`); the result is the difference of the first differing pair of bytes (as `unsigned char`), or
`0`. Not in the runtime (`Runtime/Libc.lean`, `Runtime/CExpr.lean`); its only caller is `fizzle_matches`. -/
def memcmp (s1 s2 : BPtr) (n : Nat) : M Int32 := do
  let _ ← s1.add n
  let _ ← s2.add n
  let (r, _) ← cwhile
    (fun ((r, i) : Option Int32 × Nat) => pure (r.isNone && i < n, (r, i)))
    (fun ((_, i) : Option Int32 × Nat) => do
      let a ← index8 s1 i
      let b ← index8 s2 i
      if a != b then return (some (Int32.ofNat a.toNat - Int32.ofNat b.toNat), i)
      return (none, i + 1))
    (none, 0)
  return r.getD 0

/-- `Z_FORCEINLINE static void SUFFIX(insert_match)(deflate_state *s, unsigned char *Z_RESTRICT window,
struct match match, uint32_t max_insert_count)` (`deflate_medium_tpl.h:16-41`). `insert_knuth_batch` and
`insert_knuth_stepped` are the external functions of `insert_string.c`. -/
def insert_match (st : StatePtr) (window : BPtr) (match_ : Match) (max_insert_count : UInt32) : M Unit := do
  let mut strstart : UInt32 := match_.strstart + 1
  let mut match_len : UInt32 := match_.match_length - 1
  let max_len : UInt32 := 2 * max_insert_count
  if strstart < match_.orgstart then
    let end_ : UInt32 := strstart + match_len
    strstart := match_.orgstart
    match_len := end_ - strstart
    if match_len == 0 then
      let _ ← insert_knuth st window (end_ - 1)
      return
  if match_len ≤ max_len then
    insert_knuth_batch st window strstart match_len
    return
  insert_knuth_stepped st window strstart match_len max_insert_count

/-- `Z_FORCEINLINE static struct match SUFFIX(find_best_match)(deflate_state *s, uint32_t hash_head,
int32_t max_dist)` (`deflate_medium_tpl.h:43-82`). `(int32_t)s->strstart - (int32_t)hash_head` converts both with
GCC's modulo and subtracts in `int` (checked). -/
def find_best_match (st : StatePtr) (hash_head : UInt32) (max_dist : Int32) : M Match := do
  let mut m : Match := default
  m := { m with match_start := 0 }
  m := { m with match_length := 1 }
  m := { m with strstart := (← rdD st (·.strstart)) }
  m := { m with orgstart := m.strstart }
  let dist ← chkI32 ((← rdD st (·.strstart)).toInt32.toInt - hash_head.toInt32.toInt)
  if dist ≤ max_dist && dist > 0 && hash_head != 0 then
    let match_len ← longest_match_c st hash_head
    m := { m with match_start := (← rdD st (·.match_start)) }
    if match_len < WANT_MIN_MATCH then
      return m
    if m.match_start ≥ m.strstart then
      return m
    m := { m with match_length := match_len }
    let match_dist : UInt32 := m.strstart - m.match_start
    if match_dist < match_len then
      m := { m with orgstart := m.orgstart + (match_len - match_dist) }
  return m

/-- `static void fizzle_matches(unsigned char *Z_RESTRICT window, struct match *Z_RESTRICT current,
struct match *Z_RESTRICT next, int32_t max_dist)` (`deflate_medium_tpl.h:100-167`, `USE_FIZZLE` only). `*current`
and `*next` are passed by value and returned (normalisation 1). `STD_MAX_MATCH` is the `int` constant `258`; the
`int32_t` subtractions are checked (`chkI32`); `(int32_t)` of a `uint32_t` takes GCC's modulo result.
`MIN(a, b)` is `((a) > (b) ? (b) : (a))`. `need <= sizeof(uint64_t)` compares as `size_t`. -/
def fizzle_matches (window : BPtr) (current next : Match) (max_dist : Int32) : M (Match × Match) := do
  let mut current := current
  let mut next := next
  -- unsigned char *match = window + next->match_start + 1 - current->match_length;
  let match_ ← (← (← window.add next.match_start.toNat).add 1).add (-(current.match_length.toNat : Int))
  -- unsigned char *orig  = window + next->strstart + 1 - current->match_length;
  let orig ← (← (← window.add next.strstart.toNat).add 1).add (-(current.match_length.toNat : Int))
  if (← load8 match_) != (← load8 orig) then
    return (current, next)
  let limit : Int32 ←
    if next.strstart.toInt32 > max_dist then chkI32 (next.strstart.toInt32.toInt - max_dist.toInt) else pure 0
  let need : UInt32 := current.match_length - 1
  let max_steps_to_limit ← chkI32 (next.strstart.toInt32.toInt - limit.toInt)
  let max_growth_allowed ← chkI32 ((STD_MAX_MATCH.toNat : Int) - next.match_length.toInt32.toInt)
  let max_steps_to_history ← chkI32 (next.match_start.toInt32.toInt - 1)
  let steps1 : Int32 :=
    if current.match_length.toInt32 > max_steps_to_limit then max_steps_to_limit else current.match_length.toInt32
  let steps2 : Int32 :=
    if max_growth_allowed > max_steps_to_history then max_steps_to_history else max_growth_allowed
  let steps : Int32 := if steps1 > steps2 then steps2 else steps1
  if steps < need.toInt32 then
    return (current, next)
  if need.toNat ≤ 8 then
    let diff : UInt64 := (← memread8 match_) ^^^ (← memread8 orig)
    if diff &&& (← zng_first_bytes_mask64 need) != 0 then
      return (current, next)
  else if (← memcmp match_ orig need.toNat) != 0 then
    return (current, next)
  let extra_byte_ok : Bool := steps == current.match_length.toInt32
  next := { next with match_start := next.match_start - need }
  next := { next with strstart := next.strstart - need }
  next := { next with match_length := next.match_length + need }
  next := { next with orgstart := next.orgstart + 1 }
  current := { current with match_length := 1 }
  if extra_byte_ok then
    -- match = window + next->match_start - 1;  orig = window + next->strstart - 1;
    let match_ ← (← window.add next.match_start.toNat).add (-1)
    let orig ← (← window.add next.strstart.toNat).add (-1)
    if (← load8 match_) == (← load8 orig) then
      next := { next with match_start := next.match_start - 1 }
      next := { next with strstart := next.strstart - 1 }
      next := { next with match_length := next.match_length + 1 }
      current := { current with match_length := 0 }
  return (current, next)

/-- One trip of the inner `for (;;)` of `SUFFIX(deflate_medium)` (`deflate_medium_tpl.h:285-319`): the continuation
of a max-length match at the distance `cont_dist`. Returns how the trip ends and the new `bflush`. -/
def deflate_medium_cont_trip (st : StatePtr) (window : BPtr) (max_insert_count cont_dist : UInt32)
    (bflush : Bool) : M (Ctl × Bool) := do
  let mut bflush := bflush
  let mut cont_match : Match := default
  let cont_len ← max_match_continues window (← rdD st (·.strstart)) cont_dist
  if cont_len < 8 then
    return (.brk, bflush)
  cont_match := { cont_match with match_start := (← rdD st (·.strstart)) - cont_dist }
  cont_match := { cont_match with match_length := cont_len }
  cont_match := { cont_match with strstart := (← rdD st (·.strstart)) }
  cont_match := { cont_match with
    orgstart := if cont_dist < cont_len then cont_match.strstart + cont_len - cont_dist else cont_match.strstart }
  let _ ← insert_knuth st window (← rdD st (·.strstart))
  insert_match st window cont_match max_insert_count
  wrD st fun s => { s with lookahead := s.lookahead - cont_len }
  let b ← zng_tr_tally_dist st cont_dist (cont_len - STD_MIN_MATCH)
  bflush := bflush || b
  wrD st fun s => { s with strstart := s.strstart + cont_len }
  if bflush then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return (.ret r, bflush)
    | none => pure ()
    bflush := false
  if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
    return (.brk, bflush)
  return (.cont, bflush)

/-- One trip of the outer `for (;;)` of `SUFFIX(deflate_medium)` (`deflate_medium_tpl.h:179-324`); `fizzle` is
`USE_FIZZLE`. The loop state is `(current_match, next_match)`. -/
def deflate_medium_trip (fizzle : Bool) (st : StatePtr) (flush : Int32) (window : BPtr)
    (max_insert_count : UInt32) (max_dist : Int32) (current_match next_match : Match) :
    M (Ctl × Match × Match) := do
  let mut current_match := current_match
  let mut next_match := next_match
  let mut bflush : Bool := false
  let mut curr_match_len : UInt32 := 0
  if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
    ZlibNg.Deflate.fill_window st
    if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD && flush == Z_NO_FLUSH then
      return (.ret .need_more, current_match, next_match)
    if (← rdD st (·.lookahead)) == 0 then
      return (.brk, current_match, next_match)
    if fizzle then
      next_match := { next_match with match_length := 0 }
  if fizzle then
    -- #ifdef USE_FIZZLE (`:204-252`)
    if next_match.match_length > 0 then
      current_match := next_match
      next_match := { next_match with match_length := 0 }
    else
      let mut hash_head : UInt32 := 0
      if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
        hash_head ← insert_knuth st window (← rdD st (·.strstart))
      current_match ← find_best_match st hash_head max_dist
    curr_match_len := current_match.match_length
    if curr_match_len ≥ WANT_MIN_MATCH then
      if (← rdD st (·.lookahead)) > curr_match_len + WANT_MIN_MATCH then
        insert_match st window current_match max_insert_count
    if curr_match_len == STD_MAX_MATCH then
      next_match := { next_match with match_length := 0 }
    else
      -- `(s->lookahead > MIN_LOOKAHEAD) & ((current_match.strstart + curr_match_len) < s->fill_end)`: both operands
      -- are evaluated.
      let c1 : Bool := (← rdD st (·.lookahead)) > MIN_LOOKAHEAD
      let c2 : Bool := current_match.strstart + curr_match_len < (← rdD st (·.fill_end))
      if c1 && c2 then
        wrD st fun s => { s with strstart := current_match.strstart + curr_match_len }
        let hash_head ← insert_knuth st window (← rdD st (·.strstart))
        next_match ← find_best_match st hash_head max_dist
        let tmp_cmatch_len_sub : UInt32 := curr_match_len - 1
        if tmp_cmatch_len_sub != 0 && next_match.match_length ≥ WANT_MIN_MATCH &&
            tmp_cmatch_len_sub ≤ next_match.match_start then
          let (c, n) ← fizzle_matches window current_match next_match max_dist
          current_match := c
          next_match := n
          curr_match_len := current_match.match_length
        wrD st fun s => { s with strstart := current_match.strstart }
        if curr_match_len == 0 then
          return (.cont, current_match, next_match)
      else
        next_match := { next_match with match_length := 0 }
  else
    -- #else (`:253-265`)
    let mut hash_head : UInt32 := 0
    if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
      hash_head ← insert_knuth st window (← rdD st (·.strstart))
    current_match ← find_best_match st hash_head max_dist
    curr_match_len := current_match.match_length
    if curr_match_len ≥ WANT_MIN_MATCH then
      if (← rdD st (·.lookahead)) > curr_match_len + WANT_MIN_MATCH then
        insert_match st window current_match max_insert_count
  -- now emit the current match
  wrD st fun s => { s with lookahead := s.lookahead - curr_match_len }
  if curr_match_len == 1 then
    bflush ← zng_tr_tally_lit st (← index8 window current_match.strstart.toNat)
  else
    bflush ← zng_tr_tally_dist st (current_match.strstart - current_match.match_start)
      (curr_match_len - STD_MIN_MATCH)
  wrD st fun s => { s with strstart := s.strstart + curr_match_len }
  if curr_match_len == STD_MAX_MATCH then
    if (← rdD st (·.lookahead)) ≥ MIN_LOOKAHEAD then
      let cont_dist : UInt32 := current_match.strstart - current_match.match_start
      let (c, bf) ← cwhile
        (fun (x : Ctl × Bool) => pure (x.1 matches .cont, x))
        (fun (x : Ctl × Bool) => deflate_medium_cont_trip st window max_insert_count cont_dist x.2)
        (Ctl.cont, bflush)
      bflush := bf
      if let .ret r := c then
        return (.ret r, current_match, next_match)
  if bflush then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return (.ret r, current_match, next_match)
    | none => pure ()
  return (.cont, current_match, next_match)

/-- `Z_INTERNAL block_state SUFFIX(deflate_medium)(deflate_state *s, int flush)` (`deflate_medium_tpl.h:170-335`);
`fizzle` is `USE_FIZZLE`. `int32_t max_dist = MAX_DIST(s);` converts the `unsigned int` with GCC's modulo. -/
def deflate_medium_tpl (fizzle : Bool) (st : StatePtr) (flush : Int32) : M BlockState := do
  let current_match : Match := { match_start := 0, match_length := 0, strstart := 0, orgstart := 0 }
  let next_match : Match := { match_start := 0, match_length := 0, strstart := 0, orgstart := 0 }
  let window ← (← rdD st (·.window)).get
  -- uint32_t max_insert_count = MIN(MAX(2, s->max_insert_count), STD_MAX_MATCH);   (patch 0013; max_insert_count
  -- is max_lazy_match)
  let mic ← rdD st (·.max_lazy_match)
  let mic2 : UInt32 := if 2 < mic then mic else 2
  let max_insert_count : UInt32 := if mic2 > STD_MAX_MATCH then STD_MAX_MATCH else mic2
  let max_dist : Int32 := (MAX_DIST (← ldDState st)).toInt32
  let (c, _, _) ← cwhile
    (fun (x : Ctl × Match × Match) => pure (x.1 matches .cont, x))
    (fun (x : Ctl × Match × Match) =>
      deflate_medium_trip fizzle st flush window max_insert_count max_dist x.2.1 x.2.2)
    (Ctl.cont, current_match, next_match)
  if let .ret r := c then
    return r
  wrD st fun s => { s with insert := if s.strstart < STD_MIN_MATCH - 1 then s.strstart else STD_MIN_MATCH - 1 }
  if flush == Z_FINISH then
    match ← FLUSH_BLOCK st window 1 with
    | some r => return r
    | none => pure ()
    return .finish_done
  if (← rdD st (·.sym_next)) != 0 then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return r
    | none => pure ()
  return .block_done

end ZlibNg.DeflateMedium
