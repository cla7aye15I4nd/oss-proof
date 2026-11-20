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

/-- `put` is `out - left` bytes after a position `ob` of the output buffer `[oo, oo + O0)` of block `bo` with exactly
the `out` bytes of the buffer from there on (`ob + out = oo + O0`). -/
def OutAt (bo oo : Nat) (O0 : UInt32) (put : BPtr) (out left : UInt32) : Prop :=
  left ≤ out ∧ ∃ ob, oo ≤ ob ∧ ob + out.toNat = oo + O0.toNat ∧ put = .ref (.heap bo) (ob + (out - left).toNat)

/-- The values `ret` takes at the head of a trip: `Z_OK`, `Z_STREAM_END` or `Z_DATA_ERROR`. -/
abbrev RetOK (v : Int32) : Prop := v = Z_OK ∨ v = Z_STREAM_END ∨ v = Z_DATA_ERROR

theorem RetOK.ne_buf {v : Int32} (h : RetOK v) : v ≠ Z_BUF_ERROR := by
  rcases h with rfl | rfl | rfl <;> decide

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

/-- How far a mode is from leaving without consuming anything (see the module comment). -/
def rank (m : UInt32) : Nat := min 31 <|
  if m = LENGTH then 1 else if m = CHECK then 2 else if m = LEN then 3 else if m = LEN_ then 4
  else if m = LIT then 5 else if m = MATCH then 6 else if m = DISTEXT then 7 else if m = DIST then 8
  else if m = LENEXT then 9 else if m = TYPEDO then 10 else if m = TYPE then 11 else if m = COPY then 12
  else if m = COPY_ then 13 else if m = STORED then 14 else if m = TABLE then 15 else if m = LENLENS then 17
  else if m = CODELENS then 16 else if m = HCRC then 18 else if m = COMMENT then 19 else if m = NAME then 20
  else if m = EXTRA then 21 else if m = EXLEN then 22 else if m = OS then 23 else if m = TIME then 24
  else if m = FLAGS then 25 else if m = DICT then 26 else if m = DICTID then 27 else if m = HEAD then 28
  else 0

theorem rank_lt (m : UInt32) : rank m < 32 := by
  unfold rank; exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by decide)

/-- A stream record with the exact accounting of the call: `next_in` advanced by `A0 - avail_in` bytes (`InAt`), and
`next_out` advanced by `O0 - avail_out` bytes from the start `oo` of the output buffer. -/
def SAcc (E : Env) (z : ZStream) : Prop :=
  InAt E.inp E.A0 z.next_in z.avail_in ∧ z.avail_out ≤ E.O0 ∧
    z.next_out = .ref (.heap E.bo) (E.oo + (E.O0 - z.avail_out).toNat)

/-- A stream record that holds the locals (after `RESTORE()`) has the exact accounting. -/
theorem SAcc.of_locals {E : Env} {l : IL} {z : ZStream} (hi : InAt E.inp E.A0 l.next l.have_)
    (ho : OutAt E.bo E.oo E.O0 l.put l.out l.left)
    (hn : z.next_in = l.next) (ha : z.avail_in = l.have_) (hpo : z.next_out = l.put) (hao : z.avail_out = l.left) :
    SAcc E z := by
  obtain ⟨hlo, ob, hob1, hob2, hput⟩ := ho
  have hlo' : l.left.toNat ≤ l.out.toNat := hlo
  have hsub : (l.out - l.left).toNat = l.out.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ hlo
  have hle : l.left.toNat ≤ E.O0.toNat := by omega
  have hsub2 : (E.O0 - l.left).toNat = E.O0.toNat - l.left.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)
  refine ⟨by rw [hn, ha]; exact hi, by rw [hao]; exact UInt32.le_iff_toNat_le.mpr hle, ?_⟩
  rw [hpo, hput, hao, hsub, hsub2]
  congr 1; omega

/-- `msg` of a stream record: the one at entry (in `E.H0`) or a string literal of the program. -/
def MsgK (E : Env) (z : ZStream) : Prop :=
  ∀ z0, E.H0.streams E.i = some z0 → z.msg = z0.msg ∨ ∃ k, z.msg = .ref (.str k) 0 ∧ k < strTable.size

/-- The call starts from a just reset state: mode `HEAD` (or `TYPEDO`), no bits held, not the last block. -/
def Fresh (E : Env) : Prop :=
  ∀ S0, E.H0.istate E.b = some S0 → (S0.mode = HEAD ∨ S0.mode = TYPEDO) ∧ S0.bits = 0 ∧ S0.last = 0

/-- What a trip holds while it has read nothing of the input of a fresh call: no bits held, not the last block, the
mode `HEAD`, `TYPEDO` or `BAD`, and `ret` not `Z_STREAM_END`. -/
def FrS (l : IL) (S : InflateState) : Prop :=
  l.bits = 0 ∧ S.last = 0 ∧ (S.mode = HEAD ∨ S.mode = TYPEDO ∨ S.mode = BAD) ∧ l.ret ≠ Z_STREAM_END

/-- A fresh call that has consumed no input holds `FrS`. -/
def Fr (E : Env) (l : IL) (S : InflateState) : Prop := Fresh E → l.have_ = E.A0 → FrS l S

theorem Fr.mono {E : Env} {l l' : IL} {S S' : InflateState} (h : Fr E l S) (hh : l'.have_ = l.have_)
    (k : FrS l S → FrS l' S') : Fr E l' S' :=
  fun hf ha => k (h hf (hh ▸ ha))

theorem Fr.ofLt {E : Env} {l : IL} {S : InflateState} (h : l.have_ < E.A0) : Fr E l S :=
  fun _ ha => absurd ha (UInt32.ne_of_lt h)

theorem Fr.ofFreshLt {E : Env} {l : IL} {S : InflateState} (h : Fresh E → l.have_ < E.A0) : Fr E l S :=
  fun hf ha => absurd ha (UInt32.ne_of_lt (h hf))

/-- A fresh call in a state without `FrS` has consumed input. -/
theorem Fr.lt {E : Env} {l : IL} {S : InflateState} (h : Fr E l S) (hle : l.have_ ≤ E.A0) (hn : ¬ FrS l S)
    (hf : Fresh E) : l.have_ < E.A0 :=
  UInt32.lt_of_le_of_ne hle (fun e => hn (h hf e))

theorem FrS.no_mode {l : IL} {S : InflateState} {P : Prop} (h : S.mode ≠ HEAD ∧ S.mode ≠ TYPEDO ∧ S.mode ≠ BAD) :
    FrS l S → P := fun ⟨_, _, hm, _⟩ => by
  rcases hm with e | e | e
  · exact absurd e h.1
  · exact absurd e h.2.1
  · exact absurd e h.2.2

theorem FrS.no_bits {l : IL} {S : InflateState} {P : Prop} (h : 0 < l.bits.toNat) : FrS l S → P :=
  fun ⟨hb, _⟩ => absurd h (by rw [hb]; decide)

/-- A step that only lowers the bits (`DROPBITS`, `INITBITS`, `BYTEBITS`), keeps `last`, keeps the mode or goes to
`TYPEDO` or `BAD`, and keeps `ret` or sets another code than `Z_STREAM_END`, keeps `FrS`. -/
theorem FrS.keep {l l' : IL} {S S' : InflateState} (hb : l'.bits.toNat ≤ l.bits.toNat) (hl : S'.last = S.last)
    (hm : S'.mode = S.mode ∨ S'.mode = TYPEDO ∨ S'.mode = BAD) (hr : l'.ret = l.ret ∨ l'.ret ≠ Z_STREAM_END) :
    FrS l S → FrS l' S' := fun ⟨a, b, c, d⟩ => by
  refine ⟨UInt8.toNat_inj.mp ?_, hl ▸ b, ?_, ?_⟩
  · have : l.bits.toNat = 0 := by rw [a]; rfl
    show l'.bits.toNat = 0
    omega
  · rcases hm with e | e | e
    · rw [e]; exact c
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · rcases hr with e | e
    · rw [e]; exact d
    · exact e

theorem FrS.dec {l l' : IL} {S : InflateState} (h : l'.bits.toNat ≤ l.bits.toNat) (hr : l'.ret = l.ret) :
    FrS l S → FrS l' S := FrS.keep h rfl (Or.inl rfl) (Or.inl hr)

syntax "fr_bits" : tactic
macro_rules
  | `(tactic| fr_bits) => `(tactic| first
      | exact Nat.le_refl _
      | exact Nat.zero_le _
      | omega
      | (simp only []; omega))
syntax "fr_mode" : tactic
macro_rules
  | `(tactic| fr_mode) => `(tactic| first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr rfl))
syntax "fr_ret" : tactic
macro_rules
  | `(tactic| fr_ret) => `(tactic| first
      | exact Or.inl rfl
      | (apply Or.inr; decide)
      | (apply Or.inr; simp only []; decide)
      | (apply Or.inr; simp only [*]; decide))
syntax "fr_no" : tactic
macro_rules
  | `(tactic| fr_no) => `(tactic| first
      | decide
      | (simp only []; decide)
      | (simp only [*]; decide))
/-- Discharges `FrS l S → FrS l' S'` at a step of a trip: the step keeps the fields of `FrS` (`FrS.keep`), or starts
from a state without `FrS` (a mode other than `HEAD`, `TYPEDO`, `BAD`, or bits held). -/
syntax "fr_tac" : tactic
macro_rules
  | `(tactic| fr_tac) => `(tactic| first
      | exact id
      | (refine FrS.keep ?_ rfl ?_ ?_
         · fr_bits
         · fr_mode
         · fr_ret)
      | (refine FrS.no_bits ?_
         first
         | omega
         | (simp only []; omega))
      | (refine FrS.no_mode ?_; fr_no))

/-- Discharges `Fr E l S → Fr E l' S'` at a step that keeps `have`, by `fr_tac`. -/
syntax "frt" : tactic
macro_rules
  | `(tactic| frt) => `(tactic| first
      | exact id
      | (intro h
         refine Fr.mono h ?_ ?_
         · first
           | rfl
           | simp only []
         · fr_tac))

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
  /-- `in`, the input count at entry, is set once before the loop -/
  inn : l.in_ = E.A0
  /-- `out` is the output count at entry until `CHECK` sets it to `left` (and then the mode stays in
  `CHECK`, `LENGTH`, `DONE`, `BAD`, the modes of rank at most 2) -/
  outO : l.out = E.O0 ∨ rank S.mode ≤ 2
  /-- `ret` is `Z_OK`, `Z_STREAM_END` or `Z_DATA_ERROR` inside the loop, never `Z_BUF_ERROR` -/
  retB : RetOK l.ret
  /-- the stream record has the exact accounting: it holds the entry values or those of the last `RESTORE()` or
  `inflate_fast` -/
  sacc : SAcc E z
  /-- `msg` is the one at entry or a string literal (only `SET_BAD` stores it) -/
  msgK : MsgK E z
  /-- a fresh call that has consumed no input has not left `HEAD` / `TYPEDO` (or `BAD`), holds no bits, is not in the
  last block, and has not set `ret` to `Z_STREAM_END` -/
  fr : Fr E l S

/-- The loop invariant for some stream record and state. -/
def LIx (E : Env) (l : IL) (H : Heap) : Prop := ∃ z S, LI E l H z S

/-- The state between two trips: the loop invariant, or the mode `BAD` with `ret` holding a code of `inflate_table`
(`ret = zng_inflate_table(...); if (ret) { SET_BAD(...); break; }`), which the next trip (`BAD`) overwrites. -/
def LIh (E : Env) (l : IL) (H : Heap) (z : ZStream) (S : InflateState) : Prop :=
  LI E l H z S ∨ (S.mode = BAD ∧ ∃ v, LI E { l with ret := v } H z S)

theorem LIh.hs {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (h : LIh E l H z S) :
    H.istate E.b = some S := by
  rcases h with li | ⟨-, v, li⟩
  · exact li.hs
  · exact li.hs

/-- The stream record in `H` with the exact accounting of the call: `next_in` advanced by `A0 - avail_in` bytes
(`InAt`), and `next_out` advanced by `O0 - avail_out` bytes from the start `oo` of the output buffer. -/
def IoAcc (E : Env) (H : Heap) : Prop := ∃ z, H.streams E.i = some z ∧ SAcc E z ∧ MsgK E z

theorem LI.ioAcc {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (li : LI E l H z S) : IoAcc E H :=
  ⟨z, li.hz, li.sacc, li.msgK⟩

theorem LIh.ioAcc {E : Env} {l : IL} {H : Heap} {z : ZStream} {S : InflateState} (h : LIh E l H z S) : IoAcc E H := by
  rcases h with li | ⟨-, v, li⟩
  · exact li.ioAcc
  · exact li.ioAcc

/-- Why a trip went to `inf_leave`: `ret` was set, the input ran out or was read from, the output ran out (with `out`
still the output count at entry), or `flush` asked to stop at a block boundary. -/
def Why (E : Env) (l : IL) : Prop :=
  l.ret ≠ Z_OK ∨ l.have_ = 0 ∨ l.have_ < E.A0 ∨ (l.left = 0 ∧ l.out = E.O0) ∨ E.flush = Z_BLOCK ∨
    E.flush = Z_TREES

theorem Why.ret {E : Env} {l : IL} (h : l.ret ≠ Z_OK) : Why E l := Or.inl h
theorem Why.have0 {E : Env} {l : IL} (h : l.have_ = 0) : Why E l := Or.inr (Or.inl h)
theorem Why.read {E : Env} {l : IL} (h : l.have_ < E.A0) : Why E l := Or.inr (Or.inr (Or.inl h))
theorem Why.full {E : Env} {l : IL} (h : l.left = 0) (h' : l.out = E.O0) : Why E l :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h'⟩)))
theorem Why.block {E : Env} {l : IL} (h : E.flush = Z_BLOCK) : Why E l := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem Why.trees {E : Env} {l : IL} (h : E.flush = Z_TREES) : Why E l := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

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

/-- What the call returns with: the invariant, the frame, and the stream's state block `b` with the registered
header kept. -/
def Fin (E : Env) (H : Heap) : Prop := Inv H (some E.i) ∧ Frame E.H0 H [E.i] [E.b] E.G E.W ∧
  ∃ z S, H.streams E.i = some z ∧ z.state = some E.b ∧ H.istate E.b = some S ∧ S.head = .val E.hp

/-- The outcome of one trip of the loop started below the measure `m`. -/
def Post (E : Env) (m : Nat) : Except Ex Unit → IL → Heap → Prop
  | .ok (), l, H => ∃ z S, LIh E l H z S ∧ μ l S < m
  | .error .leave, l, H => LIx E l H ∧ Why E l
  | .error (.ret v), _, H => Fin E H ∧ IoAcc E H ∧ (v = Z_NEED_DICT ∨ v = Z_STREAM_ERROR)

theorem Post.mono {E : Env} {m m' : Nat} (hm : m ≤ m') {r : Except Ex Unit} {l : IL} {H : Heap}
    (p : Post E m r l H) : Post E m' r l H := by
  match r, p with
  | .ok (), ⟨z, S, li, hlt⟩ => exact ⟨z, S, li, by omega⟩
  | .error .leave, p => exact p
  | .error (.ret _), p => exact p

/-- One trip of the loop from every state between two trips. -/
def TripOK (E : Env) : Prop :=
  ∀ l H z S, LIh E l H z S → SatX H l (dispatch E.c) (Post E (μ l S))

/-- The whole `for (;;)` loop: it ends only by `inf_leave` (with the invariant) or `return` (with the final
invariant and frame). -/
theorem loop_ok {E : Env} (T : TripOK E) {l : IL} {H : Heap} {z : ZStream} {S : InflateState}
    (li : LI E l H z S) :
    SatX H l (xloopBrk (do dispatch E.c; return false)) (fun r l' H' => match r with
      | .ok () => False
      | .error .leave => LIx E l' H' ∧ Why E l'
      | .error (.ret v) => Fin E H' ∧ IoAcc E H' ∧ (v = Z_NEED_DICT ∨ v = Z_STREAM_ERROR)) := by
  unfold xloopBrk
  refine xwhileBrk_rank (fun l H => ∃ z S, LIh E l H z S) (fun l H => ?_) _ ?_ ⟨z, S, Or.inl li⟩ ?_
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
      rw [LIh.hs li2, LIh.hs li']
      exact hlt
    | .error .leave, p => exact p
    | .error (.ret _), p => exact p
  · show (match H.istate E.b with | some S => μ l S | none => 0) + 2 < fuel
    rw [li.hs]
    exact μ_lt_fuel l S

end ZlibNgF.Proof.InflateLoop
