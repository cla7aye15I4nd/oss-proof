import ZlibNgF.Proof.«deflate_slow.c.frame»

/-!
# One trip of `deflate_slow`, in three parts (`ZlibNgF`)

The trip of the `for (;;)` of `deflate_slow` (`deflate_slow_trip`) is split at its two join points into the part after
the refill (`slowA`: the hash insertion), the part after the insertion (`slowB`: the lazy match search, from
`hash_head`) and the part after the search (`slowC`: the emission, from `match_len`). Each part is the translation's
text from that point on; `trip_eq` states that the trip is the refill followed by `slowA` (definitional unfolding).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.SlowStep
open C ZlibNg.Inflate ZlibNg.Deflate ZlibNg.DeflateP ZlibNg.InsertStringP ZlibNg.InsertString ZlibNg.Compare256
open ZlibNg.DeflateSlow

/-- The end of the emission of a match (`deflate_slow.c:121-126`): `prev_length` and `match_available` cleared,
`strstart` past the match, and `FLUSH_BLOCK` when the symbol buffer is full. -/
def slowDist3 (st : StatePtr) (window : BPtr) (mov_fwd : UInt32) (bflush : Bool) : M Ctl := do
  wrD st fun s => { s with prev_length := 0 }
  wrD st fun s => { s with match_available := 0 }
  wrD st fun s => { s with strstart := s.strstart + (mov_fwd + 1) }
  if bflush then
    match ← FLUSH_BLOCK st window 0 with
    | some r => return .ret r
    | none => pure ()
  return .cont

/-- The insertion of the positions inside a match (`deflate_slow.c:107-120`), then `slowDist3`. -/
def slowIns (st : StatePtr) (window : BPtr) (insert_batch : InsertBatchFn) (level : Int32)
    (max_insert mov_fwd : UInt32) (bflush : Bool) : M Ctl := do
  let mut insert_cnt : UInt32 := mov_fwd
  if insert_cnt > max_insert - (← rdD st (·.strstart)) then
    insert_cnt := max_insert - (← rdD st (·.strstart))
  let s ← ldDState st
  let match_dist : UInt32 := s.strstart - 1 - s.prev_match
  -- uint32_t tail_cnt = MAX(match_dist + 2, 64);
  let tail_cnt : UInt32 := if match_dist + 2 < 64 then 64 else match_dist + 2
  if tail_cnt ≥ insert_cnt then
    call_insert_batch insert_batch st window ((← rdD st (·.strstart)) + 1) insert_cnt
  else if level ≥ MIN_ROLL_LEVEL then
    insert_roll_batch_tail_static st window ((← rdD st (·.strstart)) + 1) insert_cnt tail_cnt
  else
    insert_knuth_batch_tail_static st window ((← rdD st (·.strstart)) + 1) insert_cnt tail_cnt
  slowDist3 st window mov_fwd bflush

/-- The emission of a match after its tally (`deflate_slow.c:101-126`). -/
def slowDist2 (st : StatePtr) (window : BPtr) (insert_batch : InsertBatchFn) (level : Int32) (max_insert : UInt32)
    (bflush : Bool) : M Ctl := do
  wrD st fun s => { s with prev_length := s.prev_length - 1 }
  wrD st fun s => { s with lookahead := s.lookahead - s.prev_length }
  let mov_fwd : UInt32 := (← rdD st (·.prev_length)) - 1
  if max_insert > (← rdD st (·.strstart)) then
    slowIns st window insert_batch level max_insert mov_fwd bflush
  else
    slowDist3 st window mov_fwd bflush

/-- The emission of the pending match (`deflate_slow.c:94-126`), from the state `s` read before it. -/
def slowDist (st : StatePtr) (window : BPtr) (insert_batch : InsertBatchFn) (level : Int32) (s : DeflateState) :
    M Ctl := do
  -- unsigned int max_insert = s->strstart + s->lookahead - STD_MIN_MATCH;
  let max_insert : UInt32 := s.strstart + s.lookahead - STD_MIN_MATCH
  let bflush ← zng_tr_tally_dist st (s.strstart - 1 - s.prev_match) (s.prev_length - STD_MIN_MATCH)
  slowDist2 st window insert_batch level max_insert bflush

/-- The end of the emission of the pending literal (`deflate_slow.c:135-141`). -/
def slowLit2 (st : StatePtr) (match_len : UInt32) : M Ctl := do
  wrD st fun s => { s with prev_length := match_len }
  wrD st fun s => { s with strstart := s.strstart + 1 }
  wrD st fun s => { s with lookahead := s.lookahead - 1 }
  let strm ← (← rdD st (·.strm)).get
  if (← rdZ strm (·.avail_out)) == 0 then
    return .ret .need_more
  return .cont

/-- The emission of the pending literal (`deflate_slow.c:127-141`). -/
def slowLit (st : StatePtr) (window : BPtr) (match_len : UInt32) : M Ctl := do
  -- bflush = zng_tr_tally_lit(s, window[s->strstart-1]);
  let bflush ← zng_tr_tally_lit st (← index8 window ((← rdD st (·.strstart)) - 1).toNat)
  if bflush then
    FLUSH_BLOCK_ONLY st (pure window) 0
  slowLit2 st match_len

/-- No pending literal (`deflate_slow.c:142-149`): the byte at `strstart` waits. -/
def slowElse (st : StatePtr) (match_len : UInt32) : M Ctl := do
  wrD st fun s => { s with prev_length := match_len }
  wrD st fun s => { s with match_available := 1 }
  wrD st fun s => { s with strstart := s.strstart + 1 }
  wrD st fun s => { s with lookahead := s.lookahead - 1 }
  return .cont

/-- The trip after the match search (`deflate_slow.c:93-150`), from the kept `match_len`. -/
def slowC (st : StatePtr) (window : BPtr) (insert_batch : InsertBatchFn) (level : Int32) (match_len : UInt32) :
    M Ctl := do
  let s ← ldDState st
  if s.prev_length ≥ STD_MIN_MATCH && match_len ≤ s.prev_length then
    slowDist st window insert_batch level s
  else if s.match_available != 0 then
    slowLit st window match_len
  else
    slowElse st match_len

/-- The trip after the hash insertion (`deflate_slow.c:55-92`), from `hash_head`. -/
def slowB (st : StatePtr) (window : BPtr) (longest_match : LongestMatchFn) (insert_batch : InsertBatchFn)
    (level : Int32) (match_discard match_floor : UInt32) (hash_head : UInt32) : M Ctl := do
  -- s->prev_match = s->match_start;
  wrD st fun s => { s with prev_match := s.match_start }
  let prev_length ← rdD st (·.prev_length)
  let mut match_len : UInt32 := STD_MIN_MATCH - 1
  let dist : Int := ((← rdD st (·.strstart)).toNat : Int) - (hash_head.toNat : Int)
  let s ← ldDState st
  if dist ≤ ((MAX_DIST s).toNat : Int) && dist > 0 && prev_length < s.max_lazy_match && hash_head != 0 then
    -- s->prev_length = MAX(prev_length, match_floor);
    wrD st fun s => { s with prev_length := if prev_length < match_floor then match_floor else prev_length }
    match_len ← call_longest_match longest_match st hash_head
    wrD st fun s => { s with prev_length := prev_length }
    -- if (match_len <= match_discard || s->match_start >= s->strstart)  (patch 0019; `||` short-circuits)
    if match_len ≤ match_discard then
      match_len := STD_MIN_MATCH - 1
    else
      let s ← ldDState st
      if s.match_start ≥ s.strstart then
        match_len := STD_MIN_MATCH - 1
  slowC st window insert_batch level match_len

/-- The trip after the refill (`deflate_slow.c:45-54`): the hash insertion. -/
def slowA (st : StatePtr) (window : BPtr) (longest_match : LongestMatchFn) (insert_batch : InsertBatchFn)
    (level : Int32) (match_discard match_floor : UInt32) : M Ctl := do
  let mut hash_head : UInt32 := 0
  if (← rdD st (·.lookahead)) ≥ WANT_MIN_MATCH then
    if level ≥ MIN_ROLL_LEVEL then
      hash_head ← insert_roll st window (← rdD st (·.strstart))
    else
      hash_head ← insert_knuth st window (← rdD st (·.strstart))
  slowB st window longest_match insert_batch level match_discard match_floor hash_head

/-- The trip is the refill followed by `slowA`. -/
theorem trip_eq (st : StatePtr) (flush : Int32) (longest_match : LongestMatchFn) (insert_batch : InsertBatchFn)
    (window : BPtr) (level : Int32) (match_discard match_floor : UInt32) :
    deflate_slow_trip st flush longest_match insert_batch window level match_discard match_floor = (do
      if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD then
        ZlibNg.Deflate.fill_window st
        if (← rdD st (·.lookahead)) < MIN_LOOKAHEAD && flush == Z_NO_FLUSH then
          return .ret .need_more
        if (← rdD st (·.lookahead)) == 0 then
          return .brk
      slowA st window longest_match insert_batch level match_discard match_floor) := rfl

/-! ## The loop invariant -/

open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.DeflateInit

/-- The facts of the entry heap `h` that hold along the call: the window at offset `wo` of the block, the levels of
`deflate_slow` with a `last_flush` that is a flush value, and the level `level` read at entry. -/
structure Env (h : Heap) (b wo : Nat) (level : Int32) : Prop where
  win : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo)
  tab : ∀ st0, h.dstate b = some st0 → TableAt 7 9 st0 ∧ 0 ≤ st0.last_flush
  lv : ∀ st0, h.dstate b = some st0 → st0.level = level

/-- The hash chains and the lazy-match fields of the state of `H`. -/
def SI (b : Nat) (H : Heap) : Prop :=
  ∀ st d, H.dstate b = some st → H.bytes b = some d → ChainOk b d st ∧ LazyOk st

/-- The loop invariant, by the way the trip ended. -/
def RI (h : Heap) (i b : Nat) (flush : Int32) (c : Ctl) (H : Heap) : Prop :=
  match c with
  | .cont => SLC h i b H ∧ SI b H
  | .brk => SLC h i b H ∧ SI b H ∧ ∀ st, H.dstate b = some st → st.lookahead = 0
  | .ret r => StratPost h (some i) flush r H ∧ ∀ st d, H.dstate b = some st → H.bytes b = some d → ChainOk b d st

/-- The lookahead of the state of `H`. -/
def laOf (H : Heap) (b : Nat) : Nat :=
  match H.dstate b with
  | some st => st.lookahead.toNat
  | none => 0

/-- The loop measure. -/
def RM (i b : Nat) (c : Ctl) (H : Heap) : Nat :=
  match c with
  | .cont => avIn H i + laOf H b + 1
  | _ => 0

theorem laOf_SH (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    laOf (SH H0 i z b st d) b = st.lookahead.toNat := by
  simp [laOf]

/-- The facts of `Env` on the state of an `SLF` heap. -/
theorem env_st {h H0 : Heap} {i b wo : Nat} {z : ZStream} {st : DeflateState} {d : Array UInt8} {level : Int32}
    (E : Env h b wo level) (F : SLF h i b (SH H0 i z b st d)) :
    st.window = .val (.ref (.heap b) wo) ∧ TableAt 7 9 st ∧ 0 ≤ st.last_flush ∧ st.level = level := by
  obtain ⟨st0, h0, hw⟩ := F.win
  obtain ⟨st1, h1, hk⟩ := F.keeps
  obtain rfl := Option.some.inj (h0.symm.trans h1)
  have K := hk st (SH_dstate _ _ _ _ _ _)
  obtain ⟨t1, t2⟩ := ZlibNgF.Proof.SlowFrame.slf_table F (fun st2 h2 => ⟨(E.tab st2 h2).1, (E.tab st2 h2).2⟩) st
    (SH_dstate _ _ _ _ _ _)
  exact ⟨(hw st (SH_dstate _ _ _ _ _ _)).trans (E.win st0 h0), t1, t2, K.2.2.2.2.1.trans (E.lv st0 h0)⟩

end ZlibNgF.Proof.SlowStep
