import ZlibNgF.Proof.«inffast.base»

/-!
# `inflate_fast`: the decoding state and the steps without copies (`ZlibNgF`)

`FE` names the objects `INFLATE_FAST` works on (output block, input object, window, state, tables), `EnvOK` the
facts the entry code establishes about the copied values `FC`. A trip of the main loop runs `stepTop` and then the
label loop over `dolen` / `common` / `dodist`; `PI` is the invariant of the label loop, with a ghost rank that falls
at every label change (a root entry may link to a second-level entry, which is never a link).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InffastInv
open C ZlibNg.Inffast ZlibNg.InflateP ZlibNg.Chunkset
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono sat_cwhile)
open ZlibNgF.Proof.ChunkMem
open ZlibNgF.Proof.ChunkCopy (B)
open ZlibNgF.Proof.InffastBase

/-- The objects of one call of `INFLATE_FAST`. -/
structure FE where
  /-- output block, its size, offsets of `strm->next_out` at entry, of `safe` and of `beg` -/
  ob : Nat
  N : Nat
  o0 : Nat
  s : Nat
  begO : Nat
  /-- input object, offset of `next_in` at entry, end of the input (`next_in + avail_in`), `bits` at entry -/
  rin : BRef
  in0 : Nat
  E : Nat
  bits0 : Nat
  /-- window block and offset -/
  wb : Nat
  woff : Nat
  /-- stream, state block, their records at entry -/
  i : Nat
  b : Nat
  st : InflateState
  z : ZStream
  /-- tables -/
  rl : CodeRef
  ol : Nat
  Tl : Array Code
  lb : Nat
  rd : CodeRef
  od : Nat
  Td : Array Code
  db : Nat

/-- The facts about the values that `INFLATE_FAST` copies at entry. -/
structure EnvOK (H0 : Heap) (c : FC) (e : FE) : Prop where
  strm : c.strm = some e.i
  stp : c.st = some e.b
  hz : H0.streams e.i = some e.z
  hst : H0.istate e.b = some e.st
  bob : e.b ≠ e.ob
  outN : ∃ a, H0.bytes e.ob = some a ∧ a.size = e.N
  N63 : e.N < 2 ^ 63
  beg : c.beg = B e.ob e.begO
  safe : c.safe = B e.ob e.s
  begle : e.begO ≤ e.o0
  o0s : e.o0 ≤ e.s
  sN : e.s ≤ e.N
  span : e.s - e.begO < 2 ^ 32
  endp : c.end_ = B e.ob (if c.safeMode then e.s - 2 else e.s - 259)
  room : (if c.safeMode then 3 else 260) ≤ e.s
  last : c.last = .ref e.rin (e.E - 14)
  inA : ∃ A, Space.get H0 e.rin = some A ∧ e.E ≤ A.size
  inE : e.in0 + 15 ≤ e.E
  bits0 : e.bits0 < 8
  win : c.window = B e.wb e.woff
  wdata : ∃ wd, H0.bytes e.wb = some wd ∧ e.woff + c.wsize.toNat ≤ wd.size
  wbob : e.wb ≠ e.ob
  whave : c.whave ≤ c.wsize
  wnext : c.wnext ≤ c.whave
  lcode : c.lcode = .ref e.rl e.ol
  lget : Space.get H0 e.rl = some e.Tl
  ltab : Tab e.Tl e.ol e.lb LenEnt LenLink
  lmask : ∀ x : UInt64, (x &&& c.lmask.toUInt64).toNat < 2 ^ e.lb
  lnot : ∀ b', e.rl = .codes b' → b' ≠ e.ob
  dcode : c.dcode = .ref e.rd e.od
  dget : Space.get H0 e.rd = some e.Td
  dtab : Tab e.Td e.od e.db DistEnt DistLink
  dmask : ∀ x : UInt64, (x &&& c.dmask.toUInt64).toNat < 2 ^ e.db
  dnot : ∀ b', e.rd = .codes b' → b' ≠ e.ob

/-! ## Heaps during the loop -/

/-- The running heap: only output bytes in `[next_out, safe)` changed. -/
abbrev RH (H0 : Heap) (e : FE) (G : Heap) : Prop := ORun H0 G e.ob e.N e.o0 e.s

theorem code_get {H0 G : Heap} {e : FE} (r : RH H0 e G) {rr : CodeRef} (hr : ∀ b', rr = .codes b' → b' ≠ e.ob) :
    Space.get G rr = Space.get H0 rr := by
  have eq := r.eq
  cases rr with
  | codes b' =>
    have hb := hr b' rfl
    show (G.istate b').map (·.codes) = (H0.istate b').map (·.codes)
    rw [eq]; simp only [Heap.istate, upd_ne _ _ _ _ hb]
  | lenfix => rfl
  | distfix => rfl

theorem istate_get {H0 G : Heap} {e : FE} (r : RH H0 e G) {b' : Nat} (hb : b' ≠ e.ob) :
    G.istate b' = H0.istate b' := by
  rw [r.eq]; simp only [Heap.istate, upd_ne _ _ _ _ hb]

theorem streams_get {H0 G : Heap} {e : FE} (r : RH H0 e G) : G.streams = H0.streams := by
  rw [r.eq]

theorem in_get {H0 G : Heap} {e : FE} (r : RH H0 e G) {A : Array UInt8} (hA : Space.get H0 e.rin = some A) :
    ∃ A', Space.get G e.rin = some A' ∧ A'.size = A.size := by
  by_cases h : e.rin = BRef.heap e.ob
  · obtain ⟨a0, a, e0, e1, s0, s1, _⟩ := r.blk
    rw [h] at hA ⊢
    have : a0 = A := by
      have := hA; simp only [space_heap] at this; rw [e0] at this; exact Option.some.inj this
    subst this
    exact ⟨a, e1, by omega⟩
  · exact ⟨A, (r.get_ne h).trans hA, rfl⟩

/-! ## Invariants of a trip -/

/-- `in` at offset `p` of the input object, with `k` more readable bytes, and the bit accounting. -/
def InOK (e : FE) (l : FL) (k : Nat) : Prop :=
  ∃ p, l.in_ = .ref e.rin p ∧ e.in0 ≤ p ∧ p + k ≤ e.E ∧ l.bits.toNat < 64 ∧
    l.bits.toNat ≤ 8 * (p - e.in0) + e.bits0

/-- At least one bit consumed since entry: `in` at offset `p`, `bits + 1 ≤ 8 * (p - in0) + bits0`. -/
def InS (e : FE) (l : FL) : Prop :=
  ∃ p, l.in_ = .ref e.rin p ∧ l.bits.toNat + 1 ≤ 8 * (p - e.in0) + e.bits0

/-- `out` is `w` bytes past `ot`, the value of `out` at the start of the trip, which had room for a whole trip. -/
def OutOK (e : FE) (sm : Bool) (ot : Nat) (l : FL) (w : Nat) : Prop :=
  l.out = B e.ob (ot + w) ∧ e.o0 ≤ ot ∧ (if sm then ot + 3 else ot + 260) ≤ e.s

def RootL (e : FE) (h : Code) : Prop := ∃ k, k < 2 ^ e.lb ∧ h = e.Tl[e.ol + k]!
def SubL (h : Code) : Prop := ∃ pre, LenEnt pre h ∧ ¬ LenLink h
def RootD (e : FE) (h : Code) : Prop := ∃ k, k < 2 ^ e.db ∧ h = e.Td[e.od + k]!
def SubD (h : Code) : Prop := ∃ pre, DistEnt pre h ∧ ¬ DistLink h

/-- The state after a `break`: the output run, then the stores of `state->mode` (and `strm->msg`). -/
def BrkHeap (H0 : Heap) (e : FE) (G : Heap) : Prop :=
  ∃ G1 st' z', RH H0 e G1 ∧
    G = { G1 with istates := upd G1.istates e.b (some st'), streams := upd G1.streams e.i (some z') } ∧
    (st' = { e.st with mode := BAD } ∨ st' = { e.st with mode := TYPE } ∨
      ∃ len dist, st' = { e.st with mode := MATCH, length := len, was := len, offset := dist }) ∧
    (z' = e.z ∨ ∃ p, z' = { e.z with msg := p })

/-- The invariant of the label loop, with ghost rank `n`. -/
def PI (H0 : Heap) (c : FC) (e : FE) (ot : Nat) (n : Nat) (x : FL × Lbl) (G : Heap) : Prop :=
  match x.2 with
  | .dolen => ∃ w, w ≤ 2 ∧ OutOK e c.safeMode ot x.1 w ∧ InOK e x.1 8 ∧ InS e x.1 ∧ RH H0 e G ∧
      ((n = 6 ∧ RootL e x.1.here ∧ 20 ≤ x.1.bits.toNat) ∨
       (n = 4 ∧ SubL x.1.here ∧ x.1.here.bits.toNat ≤ x.1.bits.toNat))
  | .common => ∃ w, w ≤ 2 ∧ OutOK e c.safeMode ot x.1 w ∧ InOK e x.1 8 ∧ InS e x.1 ∧ RH H0 e G ∧ x.1.here.op ≠ 0 ∧
      ((n = 5 ∧ RootL e x.1.here ∧ 20 ≤ x.1.bits.toNat + x.1.here.bits.toNat) ∨ (n = 3 ∧ SubL x.1.here))
  | .dodist => ∃ w, w ≤ 2 ∧ OutOK e c.safeMode ot x.1 w ∧ InOK e x.1 0 ∧ InS e x.1 ∧ RH H0 e G ∧
      1 ≤ x.1.len.toNat ∧ x.1.len.toNat ≤ 258 ∧
      ((n = 2 ∧ RootD e x.1.here ∧ 28 ≤ x.1.bits.toNat) ∨
       (n = 1 ∧ SubD x.1.here ∧ x.1.here.bits.toNat ≤ x.1.bits.toNat))
  | .cont => ∃ po, x.1.out = B e.ob po ∧ ot < po ∧ po ≤ e.s ∧ InOK e x.1 0 ∧ RH H0 e G
  | .brk => ∃ po, x.1.out = B e.ob po ∧ ot ≤ po ∧ po ≤ e.s ∧ InOK e x.1 0 ∧ InS e x.1 ∧ BrkHeap H0 e G

/-! ## Root and second-level entries -/

theorem RootL.ent {e : FE} {h : Code} (E : Tab e.Tl e.ol e.lb LenEnt LenLink) (hr : RootL e h) : LenEnt 0 h := by
  obtain ⟨k, hk, rfl⟩ := hr; exact (E.2 k hk).1

theorem RootD.ent {e : FE} {h : Code} (E : Tab e.Td e.od e.db DistEnt DistLink) (hr : RootD e h) :
    DistEnt 0 h := by
  obtain ⟨k, hk, rfl⟩ := hr; exact (E.2 k hk).1

theorem LenEnt.bits_le {pre : Nat} {h : Code} (E : LenEnt pre h) : pre + h.bits.toNat ≤ 20 := by
  by_cases h0 : h.op = 0
  · have := E.1 h0; omega
  · exact E.2.1 h0

/-! ## Small steps -/

theorem InOK.mono {e : FE} {l l' : FL} {k k' : Nat} (h : InOK e l k) (hin : l'.in_ = l.in_)
    (hb : l'.bits.toNat ≤ l.bits.toNat) (hk : k' ≤ k) : InOK e l' k' := by
  obtain ⟨p, h1, h2, h3, h4, h5⟩ := h
  exact ⟨p, hin.trans h1, h2, by omega, by omega, by omega⟩

theorem InS.mono {e : FE} {l l' : FL} (h : InS e l) (hin : l'.in_ = l.in_)
    (hb : l'.bits.toNat ≤ l.bits.toNat) : InS e l' := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p, hin.trans h1, by omega⟩

theorem drop_toNat (x y : UInt8) (h : y.toNat ≤ x.toNat) : (x - y.toUInt32.toUInt8).toNat = x.toNat - y.toNat := by
  have e : y.toUInt32.toUInt8 = y := by
    apply UInt8.toNat_inj.mp; simp
  rw [e, UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le]; exact h)]

theorem sat_putLit {H0 G : Heap} {c : FC} {e : FE} {ot w : Nat} (r : RH H0 e G) (l : FL)
    (ho : OutOK e c.safeMode ot l w) (hw : w ≤ 2) (hsN : e.s ≤ e.N) :
    Sat G (putLit l) (fun l' G' => l' = { l with out := B e.ob (ot + w + 1) } ∧ RH H0 e G') := by
  obtain ⟨hout, ho0, hroom⟩ := ho
  have hs : ot + 3 ≤ e.s := by split at hroom <;> omega
  unfold putLit
  rw [hout]
  refine Sat.bind (Sat.mono (r.sat_store _ (k := ot + w) (by omega) (by omega) (by omega)) ?_)
  intro _ G1 r1
  obtain ⟨a1, ha1, ha1N⟩ := r1.cur
  refine Sat.bind (Sat.mono (sat_add (space_heap G1 e.ob ▸ ha1) (by omega) 1 (ot + w + 1) (by omega)
    (by omega)) ?_)
  rintro p G2 ⟨rfl, rfl⟩
  exact Sat.pure ⟨rfl, r1⟩

theorem sat_lookupLen {H0 G : Heap} {c : FC} {e : FE} (EV : EnvOK H0 c e) (r : RH H0 e G) (l : FL) :
    Sat G (lookupLen c l) (fun l' G' => G' = G ∧ RootL e l'.here ∧ l' = { l with here := l'.here }) := by
  have hg : Space.get G e.rl = some e.Tl := (code_get r EV.lnot).trans EV.lget
  have hk := EV.lmask l.hold
  unfold lookupLen
  rw [EV.lcode]
  refine Sat.bind (Sat.mono (sat_index_code hg _ (by have := EV.ltab.1; omega)) ?_)
  rintro h G1 ⟨rfl, rfl⟩
  exact Sat.pure ⟨rfl, ⟨_, hk, rfl⟩, rfl⟩

/-- `old = hold; DROPBITS(here.bits);` -/
theorem sat_oldDrop {G : Heap} (l : FL) (hb : l.here.bits.toNat ≤ l.bits.toNat) (h20 : l.here.bits.toNat < 64) :
    Sat G (DROPBITS { l with old := l.hold } { l with old := l.hold }.here.bits.toUInt32) (fun l' G' => G' = G ∧
      l'.in_ = l.in_ ∧ l'.out = l.out ∧ l'.here = l.here ∧ l'.len = l.len ∧
      l'.bits.toNat = l.bits.toNat - l.here.bits.toNat) := by
  refine Sat.mono (sat_DROPBITS _ _ (by simpa using h20)) ?_
  rintro l' G' ⟨rfl, hold, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, drop_toNat _ _ hb⟩

end ZlibNgF.Proof.InffastInv
