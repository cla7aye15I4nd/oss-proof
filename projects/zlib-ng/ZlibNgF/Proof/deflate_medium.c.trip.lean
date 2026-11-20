import ZlibNgF.Proof.«deflate_medium.c.cont»

/-!
# One trip of the loop of `deflate_medium` (`ZlibNgF`)

The loop state is `OI`: between trips `MG` (the frame with no pending bytes and room for a symbol, and the hash
chains), `w_size` fixed (so `max_dist = MAX_DIST(s)` of the entry state), and the carried `next_match` of
`deflate_medium_fizzle` (`NI`): used only with at least `MIN_LOOKAHEAD` bytes of lookahead (else `fill_window` runs and
clears it), it starts at `strstart`, has length 1, or 4..258 at a distance 1..32768, and `orgstart` at most its end.
The measure `OM` is `260 * (2 * avail_in + lookahead)` plus a term that drops when the fizzle `continue` lengthens the
carried match (`nm`). `fill_window` does not raise `2 * avail_in + lookahead` and lowers it when the lookahead
changes; an emission lowers the lookahead by its length.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateMedium

/-- A match that starts at `ss`: length 1, or 4..258 at a distance 1..32768; `orgstart` at most its end. -/
def NxtOk (ss : Nat) (m : Match) : Prop :=
  m.strstart.toNat = ss ∧ m.orgstart.toNat ≤ ss + m.match_length.toNat ∧ m.match_length.toNat ≤ 258 ∧
    (m.match_length = 1 ∨
      (4 ≤ m.match_length.toNat ∧ m.match_start.toNat < ss ∧ ss ≤ m.match_start.toNat + 32768))

/-- The carried `next_match`, when it is used. -/
def NI (b : Nat) (n : Match) (H : Heap) : Prop :=
  ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat → 0 < n.match_length.toNat → NxtOk st.strstart.toNat n

/-- `w_size` of block `b`'s state. -/
def WS (b : Nat) (W : UInt32) (H : Heap) : Prop := ∀ st, H.dstate b = some st → st.w_size = W

/-- The state of the outer loop. -/
def OI (h : Heap) (i b : Nat) (W : UInt32) (flush : Int32) (fz : Bool) (v : Ctl × Match × Match) (H : Heap) :
    Prop :=
  match v.1 with
  | .cont => MG h i b H ∧ WS b W H ∧ NI b v.2.2 H ∧ (fz = false → v.2.2.match_length = 0)
  | .brk => MG h i b H ∧ ∀ st, H.dstate b = some st → st.lookahead = 0
  | .ret r => StratPost h (some i) flush r H ∧ ChainAll b H

/-- The part of the measure from the carried match. -/
def nm (m : Match) : Nat := if 0 < m.match_length.toNat then 258 - m.match_length.toNat else 259

theorem nm_le (m : Match) : nm m ≤ 259 := by unfold nm; split <;> omega

/-- The measure of the outer loop. -/
def OM (i b : Nat) (v : Ctl × Match × Match) (H : Heap) : Nat :=
  match v.1 with
  | .cont => 260 * (2 * avIn H i + laOf b H) + nm v.2.2
  | _ => 0

/-- An insertion that keeps the state and grows the chains below `strstart + lookahead` keeps `MG`. -/
theorem mg_ins {h H0 : Heap} {i b : Nat} {z : ZStream} {st : DeflateState} {d d' : Array UInt8}
    (G : MG h i b (SH H0 i z b st d)) (hl : MedLv h b) (F' : SLF h i b (SH H0 i z b st d'))
    {S : Nat → Prop} (g : ZlibNgF.Proof.InsertLoop.GrowSt b st d d' S)
    (hS : ∀ q, S q → q ≠ 0 → q < st.strstart.toNat + st.lookahead.toNat) : MG h i b (SH H0 i z b st d') :=
  mg_of_pf (pe_ins (pe_of_mg G (SH_dstate _ _ _ _ _ _)) hl F' g hS).1

end ZlibNgF.Proof.MediumLoop
