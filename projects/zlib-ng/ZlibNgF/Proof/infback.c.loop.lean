import ZlibNgF.Proof.«infback.c.room»
import ZlibNgF.Proof.«inftrees.c.prefix»

/-!
# The loop of `inflateBack()` (`ZlibNgF`)

`BEnv`: what one `inflateBack` call fixes (the stream `i`, the state block `b`, the caller's window `[woff, woff + n)`
of heap block `wb`, the call-backs, their descriptors and the caller's invariant `I`). `BShape E H z S`: the shape of
the call-back stream that every step keeps (the stream's state block, its allocation record for `inflateBackEnd`,
the window and its size, `wnext == 0`, the array sizes of the state). `BL E l H t z S`: the invariant at the head of
`for (;;)`: the shape, the input (`InB`: `next` with `have` bytes is the tail of the chunk `in()` handed out last,
`t` bytes are still to come, fewer than `2^48` in all), the output (`put = window + (wsize - left)`), `whave` is `0` or
`wsize`, fewer than 8 bits held outside `BAD`, and the mode clauses `BModeOK` (the decoding tables in `LEN` and
`MATCH`, a non-zero distance in `MATCH`).

The decoding tables are `RTab`: `TabAt` (what `inflate`'s decoders read) and `Rep`, the prefix property of each table
level: the code bits of an entry that does not lead to `BAD` are at most the level's index bits and are shared by
every index with the same low code-bits bits. `Rep` keeps fewer than 8 bits held after a symbol is decoded: when the decoder had to pull a byte, the code it
finds is longer than the bits held before that byte. `inflate_fast_safe_c`, which `LEN` calls, needs fewer than 8
bits held on entry.

Termination: `μ = 32 * (8 * (have + t) + bits) + rank mode`. `out()` resets `left`, so output is not in the measure.
A trip of the loop (`dispatch`) leaves (`inf_leave`) or lowers `μ`: it consumes a bit (`TYPE`, `STORED`, `TABLE`,
`LEN`: every code has at least one bit, and `inflate_fast` consumes at least one), or moves to a mode of lower `rank`
without consuming (`MATCH → LEN`, `TYPE → DONE`, any mode `→ BAD`). `TripOK E` is that statement for every state with
the invariant; `loop_ok` turns it into the run of the whole loop.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateTab (TabAt CodeTable linkTest)

/-! ## The decoding tables -/

/-- The table at `p` with `n` root bits, as the decoders of `inflateBack` read it: in the state's `codes`, or a fixed
table; a decoding table (`CodeTable`) and a prefix code (`Rep`). -/
def RTab (b : Nat) (codes : Array Code) (p : Ival CodePtr) (n : UInt32) (m : Nat) (dist : Bool) : Prop :=
  (∃ o e, p = .val (.ref (.codes b) o) ∧ CodeTable codes o e n.toNat m dist ∧ Rep codes o n.toNat dist) ∨
  (p = .val (.ref .lenfix 0) ∧ (∃ e, CodeTable lenfix 0 e n.toNat m dist) ∧ Rep lenfix 0 n.toNat dist) ∨
  (p = .val (.ref .distfix 0) ∧ (∃ e, CodeTable distfix 0 e n.toNat m dist) ∧ Rep distfix 0 n.toNat dist)

theorem RTab.tabAt {b : Nat} {codes : Array Code} {p : Ival CodePtr} {n : UInt32} {m : Nat} {dist : Bool}
    (t : RTab b codes p n m dist) : TabAt b codes p n m dist := by
  rcases t with ⟨o, e, hp, t, -⟩ | ⟨hp, t, -⟩ | ⟨hp, t, -⟩
  · exact Or.inl ⟨o, e, hp, t⟩
  · exact Or.inr (Or.inl ⟨hp, t⟩)
  · exact Or.inr (Or.inr ⟨hp, t⟩)

/-! ## The call -/

/-- What one `inflateBack` call fixes. -/
structure BEnv where
  i : Nat
  b : Nat
  wb : Nat
  woff : Nat
  n : Nat
  inCb : InCb
  inDesc : BPtr
  outCb : OutCb
  outDesc : BPtr
  I : Heap → BPtr → Nat → Nat → Prop

/-- The caller's window. -/
def BEnv.w (E : BEnv) : BPtr := .ref (.heap E.wb) E.woff

/-- The context of the modes. -/
def BEnv.c (E : BEnv) : BCtx := ⟨some E.i, some E.b, E.inCb, E.inDesc, E.outCb, E.outDesc⟩

/-- The call-backs are well behaved for `I`. -/
def BEnv.CB (E : BEnv) : Prop := BackCallbacks E.i E.b E.w E.n E.inCb E.inDesc E.outCb E.outDesc E.I

/-- The shape of a call-back stream with stream record `z` and state `S` (see the module comment). -/
structure BShape (E : BEnv) (H : Heap) (z : ZStream) (S : InflateState) : Prop where
  hz : H.streams E.i = some z
  zs : z.state = some E.b
  zfree : z.zfree = .zcfree
  hd : ∃ d, H.bytes E.b = some d
  hs : H.istates E.b = some S
  al : ∃ al, H.iallocs E.b = some al ∧ al.zfree = .val .zcfree ∧ al.buf_start = .val (.ref (.heap E.b) 0)
  ab : S.alloc_bufs = .val (some E.b)
  win : S.window = .val E.w
  wbb : E.wb ≠ E.b
  wd : ∃ wd, H.bytes E.wb = some wd ∧ E.woff + E.n ≤ wd.size
  ws : S.wsize.toNat = E.n
  n_pos : 1 ≤ E.n
  n_le : E.n ≤ 32768
  wnext : S.wnext = 0
  lens : S.lens.size = 320
  work : S.work.size = 288
  codes : S.codes.size = ENOUGH

theorem BShape.istate {E : BEnv} {H : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S) :
    H.istate E.b = some S := by
  obtain ⟨d, hd⟩ := sh.hd
  simp [Heap.istate, hd, sh.hs]

/-- A call-back keeps the shape. -/
theorem BShape.keep {E : BEnv} {H H' : Heap} {z : ZStream} {S : InflateState} (sh : BShape E H z S)
    (k : BackKeep H H' E.i E.b E.w) : BShape E H' z S := by
  obtain ⟨ks, kb, ki, ka, kw, -, -⟩ := k
  obtain ⟨wd, hwd, hws⟩ := sh.wd
  obtain ⟨wd', hwd', hws'⟩ := kw E.wb E.woff wd rfl hwd
  exact { sh with
    hz := by rw [ks]; exact sh.hz
    hd := by rw [kb]; exact sh.hd
    hs := by rw [ki]; exact sh.hs
    al := by rw [ka]; exact sh.al
    wd := ⟨wd', hwd', by omega⟩ }

/-- The mode clauses. -/
structure BModeOK (b : Nat) (S : InflateState) : Prop where
  dec : S.mode = LEN ∨ S.mode = MATCH → RTab b S.codes S.lencode S.lenbits 28 false ∧
    RTab b S.codes S.distcode S.distbits 28 true
  off : S.mode = MATCH → 1 ≤ S.offset.toNat

/-- The invariant inside a mode: the shape, the input, the output and `whave`. -/
structure BM (E : BEnv) (l : IL) (H : Heap) (t : Nat) (z : ZStream) (S : InflateState) : Prop where
  sh : BShape E H z S
  inB : InB E.I H l t
  tot : l.have_.toNat + t < 2 ^ 48
  put : l.put = .ref (.heap E.wb) (E.woff + (E.n - l.left.toNat))
  left : l.left.toNat ≤ E.n
  whave : S.whave = 0 ∨ S.whave = S.wsize

/-- The invariant at the head of the loop (see the module comment). -/
structure BL (E : BEnv) (l : IL) (H : Heap) (t : Nat) (z : ZStream) (S : InflateState) : Prop
    extends BM E l H t z S where
  bits : S.mode = BAD ∨ l.bits.toNat < 8
  modes : BModeOK E.b S

/-- What holds when the loop leaves (`inf_leave`): the shape, the input and the output. -/
def BLv (E : BEnv) (l : IL) (H : Heap) : Prop :=
  ∃ t z S, BShape E H z S ∧ InB E.I H l t ∧ l.put = .ref (.heap E.wb) (E.woff + (E.n - l.left.toNat)) ∧
    l.left.toNat ≤ E.n

theorem BM.leave {E : BEnv} {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState} (bm : BM E l H t z S) :
    BLv E l H := ⟨t, z, S, bm.sh, bm.inB, bm.put, bm.left⟩

/-! ## The measure -/

/-- How far a mode is from leaving without consuming anything. -/
def rank (m : UInt32) : Nat :=
  if m = LEN then 1 else if m = MATCH then 2 else if m = TYPE then 3 else if m = STORED then 4
  else if m = TABLE then 5 else 0

theorem rank_lt (m : UInt32) : rank m < 32 := by
  unfold rank; repeat' (first | decide | split)

/-- The measure of the loop. -/
def μ (l : IL) (t : Nat) (S : InflateState) : Nat :=
  32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + rank S.mode

theorem μ_lt_fuel {l : IL} {t : Nat} (S : InflateState) (ht : l.have_.toNat + t < 2 ^ 48) : μ l t S + 2 < fuel := by
  have h2 := l.bits.toNat_lt
  have h4 := rank_lt S.mode
  unfold μ fuel
  have : (2 : Nat) ^ 64 = 2 ^ 48 * 2 ^ 16 := by rw [← Nat.pow_add]
  omega

/-- The outcome of one trip of the loop started below the measure `m`. -/
def Post (E : BEnv) (m : Nat) : Except Ex Unit → IL → Heap → Prop
  | .ok (), l, H => ∃ t z S, BL E l H t z S ∧ μ l t S < m
  | .error .leave, l, H => BLv E l H
  | .error (.ret _), _, _ => False

theorem Post.mono {E : BEnv} {m m' : Nat} (hm : m ≤ m') {r : Except Ex Unit} {l : IL} {H : Heap}
    (p : Post E m r l H) : Post E m' r l H := by
  match r, p with
  | .ok (), ⟨t, z, S, bl, hlt⟩ => exact ⟨t, z, S, bl, by omega⟩
  | .error .leave, p => exact p

/-- One trip of the loop from every state with the invariant. -/
def TripOK (E : BEnv) : Prop :=
  ∀ l H t z S, BL E l H t z S → SatX H l (dispatch E.c) (Post E (μ l t S))

/-! ## The loop rule -/

/-- A least element of a non-empty set of numbers. -/
theorem exists_least (p : Nat → Prop) (h : ∃ k, p k) : ∃ k, p k ∧ ∀ j, p j → k ≤ j := by
  obtain ⟨k, hk⟩ := h
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hm : ∃ j, j < k ∧ p j
    · obtain ⟨j, hj, pj⟩ := hm
      exact ih j hj pj
    · exact ⟨k, hk, fun j pj => Nat.le_of_not_lt fun hj => hm ⟨j, hj, pj⟩⟩

/-- The least measure of a loop state with the invariant (`0` if there is none). -/
noncomputable def rk (E : BEnv) (l : IL) (H : Heap) : Nat :=
  open Classical in
  if h : ∃ k t z S, BL E l H t z S ∧ μ l t S = k then
    Classical.choose (exists_least _ h)
  else 0

theorem rk_spec {E : BEnv} {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState} (bl : BL E l H t z S) :
    (∃ t' z' S', BL E l H t' z' S' ∧ μ l t' S' = rk E l H) ∧ rk E l H ≤ μ l t S := by
  have h : ∃ k t z S, BL E l H t z S ∧ μ l t S = k := ⟨_, t, z, S, bl, rfl⟩
  unfold rk
  rw [dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hp, hmin⟩ := Classical.choose_spec (exists_least _ h)
  exact ⟨hp, hmin _ ⟨t, z, S, bl, rfl⟩⟩

/-- The whole `for (;;)` loop: it ends only by `inf_leave`. -/
theorem loop_ok {E : BEnv} (T : TripOK E) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bl : BL E l H t z S) :
    SatX H l (xloopBrk (do dispatch E.c; return false)) (fun r l' H' => match r with
      | .ok () => False
      | .error .leave => BLv E l' H'
      | .error (.ret _) => False) := by
  unfold xloopBrk
  refine xwhileBrk_rank (fun l H => ∃ t z S, BL E l H t z S) (rk E) _ ?_ ⟨t, z, S, bl⟩ ?_
  · rintro l' H' ⟨t', z', S', bl'⟩
    obtain ⟨⟨t1, z1, S1, bl1, e1⟩, -⟩ := rk_spec bl'
    refine SatX.pure ?_
    dsimp only
    refine SatX.bind (SatX.mono (T l' H' t1 z1 S1 bl1) ?_)
    rintro r l2 H2 p
    match r, p with
    | .ok (), ⟨t2, z2, S2, bl2, hlt⟩ =>
      refine SatX.pure ⟨⟨t2, z2, S2, bl2⟩, ?_⟩
      have := (rk_spec bl2).2
      omega
    | .error .leave, p => exact p
  · obtain ⟨⟨t1, z1, S1, bl1, e1⟩, -⟩ := rk_spec bl
    rw [← e1]
    exact μ_lt_fuel S1 bl1.tot

end ZlibNgF.Proof.InfbackLoop
