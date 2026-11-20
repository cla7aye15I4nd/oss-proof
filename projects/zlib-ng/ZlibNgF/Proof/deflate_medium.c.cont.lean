import ZlibNgF.Proof.«deflate_medium.c.emit»

/-!
# The continuation loop of `deflate_medium` (`ZlibNgF`)

After a match of length `STD_MAX_MATCH` at distance `dist`, with at least `MIN_LOOKAHEAD` bytes of lookahead,
`deflate_medium` extends it by runs of at least 8 bytes at the same distance (`deflate_medium_tpl.h:283-319`):
each trip reads at most 258 bytes (`max_match_continues`), inserts `strstart` and the match, tallies it (the first
trip may tally into a full symbol buffer, `PE true`), advances `strstart`, and flushes when `bflush`. The loop stops
when the run is shorter than 8 or the lookahead drops below `MIN_LOOKAHEAD`; its measure is the lookahead.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.MediumLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.Strategy ZlibNgF.Proof.StrategyChain
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNg.DeflateP ZlibNg.DeflateMedium

/-- The lookahead of block `b`'s state. -/
def laOf (b : Nat) (H : Heap) : Nat :=
  match H.dstate b with
  | some st => st.lookahead.toNat
  | none => 0

theorem laOf_SH (H0 : Heap) (i : Nat) (z : ZStream) (b : Nat) (st : DeflateState) (d : Array UInt8) :
    laOf b (SH H0 i z b st d) = st.lookahead.toNat := by
  simp only [laOf, SH_dstate]

/-- The state of the continuation loop. -/
def CI (h : Heap) (i b A : Nat) (flush : Int32) (dist : UInt32) (x : Ctl × Bool) (H : Heap) : Prop :=
  match x.1 with
  | .cont => PE h i b A x.2 H ∧
      ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat ∧ dist.toNat ≤ st.strstart.toNat
  | .brk => PE h i b A x.2 H
  | .ret r => StratPost h (some i) flush r H ∧ ChainAll b H

/-- The measure of the continuation loop. -/
def CM (b : Nat) (x : Ctl × Bool) (H : Heap) : Nat :=
  match x.1 with
  | .cont => laOf b H + 1
  | _ => 0

theorem u32_add_toNat (x y : UInt32) (h : x.toNat + y.toNat < 2 ^ 32) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt h

theorem u32_sub_toNat (x y : UInt32) (h : y.toNat ≤ x.toNat) : (x - y).toNat = x.toNat - y.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr h)

/-- One trip of the continuation loop. -/
theorem cont_trip_ok (T : TreesFacts) {h H : Heap} {i b A wo : Nat} (flush : Int32) (mic dist : UInt32)
    (bf : Bool) (hl : MedLv h b) (hm2 : 2 ≤ mic.toNat) (hm3 : mic.toNat ≤ 258) (hd1 : 1 ≤ dist.toNat)
    (hd2 : dist.toNat ≤ 32768)
    (hw0 : ∀ st0, h.dstate b = some st0 → st0.window = .val (.ref (.heap b) wo))
    (hn : ∀ st0, h.dstate b = some st0 → st0.strategy ≠ Z_FIXED)
    (P : PE h i b A bf H)
    (hc : ∀ st, H.dstate b = some st → 262 ≤ st.lookahead.toNat ∧ dist.toNat ≤ st.strstart.toNat) :
    Sat H (deflate_medium_cont_trip (some b) (.ref (.heap b) wo) mic dist bf) (fun x H2 =>
      CI h i b A flush dist x H2 ∧ CM b x H2 < laOf b H + 1) := by
  have P0 := P
  obtain ⟨⟨H0, z, st, d, rfl, -⟩, -⟩ := P0
  obtain ⟨hla, hds⟩ := hc st (SH_dstate _ _ _ _ _ _)
  obtain ⟨F, hp, hle, Ch, hs, hA⟩ := pe_st P
  obtain ⟨wo', po, ho, Ly, -, w1, w2, hlook, h65, hwp, hbig, -, -⟩ := slf_lay F
  have hwin : st.window = .val (.ref (.heap b) wo) := by
    obtain ⟨st0, h0, hw⟩ := F.win
    exact (hw _ (SH_dstate _ _ _ _ _ _)).trans (hw0 st0 h0)
  obtain rfl : wo' = wo := by have := Ly.win; rw [hwin] at this; injection this with e; injection e
  rw [laOf_SH]
  unfold deflate_medium_cont_trip
  refine Sat.bind (Sat.of_eq (rdD_SH _) ?_)
  refine Sat.bind (Sat.mono (ZlibNgF.Proof.MediumFizzle.max_match_continues_ok (r := .heap b) (a := d)
    (by rw [ZlibNgF.Proof.InflateAlloc.space_get_heap]; exact SH_bytes _ _ _ _ _ _) st.strstart dist hds
    (by omega)) ?_)
  rintro cl _ ⟨rfl, hcl⟩
  by_cases h8 : cl < 8
  · rw [if_pos h8]
    exact Sat.pure ⟨P, by simp [CM]⟩
  rw [if_neg h8]
  have h8' : 8 ≤ cl.toNat := by have := UInt32.not_lt.mp h8; exact UInt32.le_iff_toNat_le.mp this
  sorry

end ZlibNgF.Proof.MediumLoop
