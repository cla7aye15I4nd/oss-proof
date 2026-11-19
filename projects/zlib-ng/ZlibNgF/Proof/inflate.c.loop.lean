import ZlibNgF.Proof.«inflate.c.xrun»
import ZlibNgF.Proof.«inflate.c.facts»

/-!
# The loop of `inflate()` (`ZlibNgF`)

`Env`: what one `inflate(strm, flush)` call fixes at entry (the heap `H0`, the stream `i` and state block `b`, the
input `[inp, inp + A0)`, the output buffer `[oo, oo + O0)` of heap block `bo`, the registered header, and the frame
lists of `Goal.inflate_safety`). `LI E l H z S`: the loop invariant at the head of `for (;;)`: the structural
invariant of the stream, the frame from `H0`, and the locals consistent with the call: `next` is the input advanced
by what was consumed with `have` bytes left (`InAt`), `put` is `out - left` bytes after the start of the output
written since the last `out = left` (`OutAt`), at most 39 bits held.

Termination: `μ = 32 * (8 * have + bits + left) + rank mode`. A trip of the loop (`dispatch`) either leaves
(`inf_leave` or `return`) or lowers `μ`: it consumes a bit, produces a byte, or moves to a mode of lower `rank`
(`rank` orders the modes against the transitions that consume nothing: `MATCH → LEN` with `length == 0`,
`COPY → TYPE`, `TYPE → CHECK`, header modes `→ TYPE`, ...). `TripOK E` is that statement for every mode; `loop_ok`
turns it into the run of the whole loop.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateLoop
open C ZlibNgF.Spec ZlibNg.Inflate
open ZlibNgF.Proof.InflateInv (Inv)
open ZlibNgF.Proof.InflateX

/-- What one call of `inflate` fixes at entry. -/
structure Env where
  H0 : Heap
  i : Nat
  b : Nat
  flush : Int32
  inp : BPtr
  A0 : UInt32
  bo : Nat
  oo : Nat
  O0 : UInt32
  hp : HeaderPtr
  G : List Nat
  W : List (BPtr × Nat)

/-- The context of the modes. -/
def Env.c (E : Env) : Ctx := ⟨some E.i, some E.b, E.flush⟩

/-- `next` is the input advanced by the `A0 - have` bytes consumed. -/
def InAt (inp : BPtr) (A0 : UInt32) (next : BPtr) (have_ : UInt32) : Prop :=
  have_ ≤ A0 ∧ match inp with
    | .null => next = .null ∧ have_ = 0
    | .ref r o => next = .ref r (o + (A0 - have_).toNat)

/-- `put` is `out - left` bytes after a position of the output buffer `[oo, oo + O0)` of block `bo` with `out` bytes
of the buffer from there on. -/
def OutAt (bo oo : Nat) (O0 : UInt32) (put : BPtr) (out left : UInt32) : Prop :=
  left ≤ out ∧ ∃ ob, oo ≤ ob ∧ ob + out.toNat ≤ oo + O0.toNat ∧ put = .ref (.heap bo) (ob + (out - left).toNat)

/-- A registered header keeps its buffer sizes; `inflate` may only null its buffer pointers. -/
def HdrOK (H0 H : Heap) (hp : HeaderPtr) : Prop :=
  match hp with
  | none => True
  | some k => ∃ g0 g, H0.gzheaders k = some g0 ∧ H.gzheaders k = some g ∧
      (g.extra = g0.extra ∨ g.extra = .null) ∧ g.extra_max = g0.extra_max ∧
      (g.name = g0.name ∨ g.name = .null) ∧ g.name_max = g0.name_max ∧
      (g.comment = g0.comment ∨ g.comment = .null) ∧ g.comm_max = g0.comm_max

/-- Every byte block but `b` keeps its size from `H0` (so the caller's buffers stay readable and writable), and the
static bytes stay. -/
def SizeKeep (H0 H : Heap) (b : Nat) : Prop :=
  (∀ c, c ≠ b → ∀ d, H0.bytes c = some d → ∃ d', H.bytes c = some d' ∧ d'.size = d.size) ∧ H.consts = H0.consts

theorem SizeKeep.refl (H : Heap) (b : Nat) : SizeKeep H H b :=
  ⟨fun _ _ d hd => ⟨d, hd, rfl⟩, rfl⟩

theorem SizeKeep.trans {H0 H1 H2 : Heap} {b : Nat} (s1 : SizeKeep H0 H1 b) (s2 : SizeKeep H1 H2 b) :
    SizeKeep H0 H2 b := by
  refine ⟨fun c hc d hd => ?_, s2.2.trans s1.2⟩
  obtain ⟨d1, e1, z1⟩ := s1.1 c hc d hd
  obtain ⟨d2, e2, z2⟩ := s2.1 c hc d1 e1
  exact ⟨d2, e2, z2.trans z1⟩

/-- The loop invariant: heap `H` with stream record `z` and state `S`, locals `l`. -/
structure LI (E : Env) (l : IL) (H : Heap) (z : ZStream) (S : InflateState) : Prop where
  inv : Inv H (some E.i)
  frame : Frame E.H0 H [E.i] [E.b] E.G E.W
  sz : SizeKeep E.H0 H E.b
  hz : H.streams E.i = some z
  hb : z.state = some E.b
  hs : H.istate E.b = some S
  head : S.head = .val E.hp
  hdr : HdrOK E.H0 H E.hp
  inAt : InAt E.inp E.A0 l.next l.have_
  outAt : OutAt E.bo E.oo E.O0 l.put l.out l.left
  bits : l.bits ≤ 39

/-- The loop invariant for some stream record and state. -/
def LIx (E : Env) (l : IL) (H : Heap) : Prop := ∃ z S, LI E l H z S

/-- How far a mode is from leaving without consuming anything (see the module comment). -/
def rank (m : UInt32) : Nat := min 31 <|
  if m = LENGTH then 1 else if m = CHECK then 2 else if m = LEN then 3 else if m = LEN_ then 4
  else if m = LIT then 5 else if m = MATCH then 6 else if m = DISTEXT then 7 else if m = DIST then 8
  else if m = LENEXT then 9 else if m = TYPEDO then 10 else if m = TYPE then 11 else if m = COPY then 12
  else if m = COPY_ then 13 else if m = STORED then 14 else if m = TABLE then 15 else if m = LENLENS then 16
  else if m = CODELENS then 17 else if m = HCRC then 18 else if m = COMMENT then 19 else if m = NAME then 20
  else if m = EXTRA then 21 else if m = EXLEN then 22 else if m = OS then 23 else if m = TIME then 24
  else if m = FLAGS then 25 else if m = DICT then 26 else if m = DICTID then 27 else if m = HEAD then 28
  else 0

theorem rank_lt (m : UInt32) : rank m < 32 := by
  unfold rank; exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by decide)

/-- The measure of the loop. -/
def μ (l : IL) (S : InflateState) : Nat :=
  32 * (8 * l.have_.toNat + l.bits.toNat + l.left.toNat) + rank S.mode

theorem μ_lt_fuel (l : IL) (S : InflateState) : μ l S + 2 < fuel := by
  have h1 := l.have_.toNat_lt
  have h2 := l.bits.toNat_lt
  have h3 := l.left.toNat_lt
  have h4 := rank_lt S.mode
  unfold μ fuel
  omega

/-- What the call returns with: the invariant and the frame. -/
def Fin (E : Env) (H : Heap) : Prop := Inv H (some E.i) ∧ Frame E.H0 H [E.i] [E.b] E.G E.W

/-- The outcome of one trip of the loop started below the measure `m`. -/
def Post (E : Env) (m : Nat) : Except Ex Unit → IL → Heap → Prop
  | .ok (), l, H => ∃ z S, LI E l H z S ∧ μ l S < m
  | .error .leave, l, H => LIx E l H
  | .error (.ret _), _, H => Fin E H

theorem Post.mono {E : Env} {m m' : Nat} (hm : m ≤ m') {r : Except Ex Unit} {l : IL} {H : Heap}
    (p : Post E m r l H) : Post E m' r l H := by
  match r, p with
  | .ok (), ⟨z, S, li, hlt⟩ => exact ⟨z, S, li, by omega⟩
  | .error .leave, p => exact p
  | .error (.ret _), p => exact p

/-- One trip of the loop from every state with the invariant. -/
def TripOK (E : Env) : Prop :=
  ∀ l H z S, LI E l H z S → SatX H l (dispatch E.c) (Post E (μ l S))

/-- The whole `for (;;)` loop: it ends only by `inf_leave` (with the invariant) or `return` (with the final
invariant and frame). -/
theorem loop_ok {E : Env} (T : TripOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) :
    SatX H l (xloopBrk (do dispatch E.c; return false)) (fun r l' H' => match r with
      | .ok () => False
      | .error .leave => LIx E l' H'
      | .error (.ret _) => Fin E H') := by
  unfold xloopBrk
  refine xwhileBrk_rank (fun l H => LIx E l H) (fun l H => ?_) _ ?_ ⟨z, S, li⟩ ?_
  · exact match H.istate E.b with | some S => μ l S | none => 0
  · rintro l' H' ⟨z', S', li'⟩
    refine SatX.pure ?_
    dsimp only
    refine SatX.bind (SatX.mono (T l' H' z' S' li') ?_)
    rintro r l2 H2 p
    match r, p with
    | .ok (), ⟨z2, S2, li2, hlt⟩ =>
      refine SatX.pure ⟨⟨z2, S2, li2⟩, ?_⟩
      show (match H2.istate E.b with | some S => μ l2 S | none => 0) <
        (match H'.istate E.b with | some S => μ l' S | none => 0)
      rw [li2.hs, li'.hs]
      exact hlt
    | .error .leave, p => exact p
    | .error (.ret _), p => exact p
  · show (match H.istate E.b with | some S => μ l S | none => 0) + 2 < fuel
    rw [li.hs]
    exact μ_lt_fuel l S

end ZlibNgF.Proof.InflateLoop
