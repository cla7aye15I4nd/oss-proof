import ZlibNgF.Proof.«deflate_strategy.common»
import ZlibNgF.ZlibNg.«deflate_quick.c»

/-!
# `deflate_quick` with tallied symbols (`ZlibNgF`)

The pieces of `deflate_quick` on its tallying path (`static_emit == 0`, a strategy other than `Z_FIXED`), on the
common loop invariant of `Proof/deflate_strategy.common.lean`: `FLUSH_BLOCK_ONLY` with the window read inside the
macro (`slf_flush_only`) and `quick_end_block` (`qeb_tally`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.Strategy
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInit
open ZlibNgF.Proof.DeflateInv ZlibNgF.Proof.DeflateFacts ZlibNgF.Proof.DeflateFlush
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)
open ZlibNgF.Proof.FlushBlock (dframe_trans dframe_wmono dframe_nil FBPost FBKeeps flush_block_only_ok)
open ZlibNg.DeflateP

/-- `FLUSH_BLOCK_ONLY(s, window, last)` from `SLF` with no pending bytes, the window expression evaluating to the
state's window: `SLF` after, no symbols, `lookahead`, `strstart` and `window` kept, the input kept, and no pending bytes
when the output has room. -/
theorem slf_flush_only (T : TreesFacts) {h H : Heap} {i b wo : Nat} (window : M BPtr) (last : Int32) (hl0 : 0 ≤ last)
    (hl1 : last ≤ 1) (F : SLF h i b H) (hp : ∀ st, H.dstate b = some st → st.pending = 0 ∧ st.window = .val (.ref (.heap b) wo))
    (hwm : window H = .ok (.ref (.heap b) wo, H)) (hsy0 : last = 0 → ∀ st, H.dstate b = some st → st.sym_next ≠ 0) :
    Sat H (FLUSH_BLOCK_ONLY (some b) window last) (fun _ H2 => avIn H2 i = avIn H i ∧
      SLFe (lastSlack last) h i b H2 ∧
      (∀ st2, H2.dstate b = some st2 → st2.sym_next = 0 ∧ st2.sym_next < st2.sym_end ∧
        ∃ st, H.dstate b = some st ∧ st2.lookahead = st.lookahead ∧ st2.strstart = st.strstart ∧
          st2.window = st.window) ∧
      (∀ z2 st2, H2.streams i = some z2 → H2.dstate b = some st2 → z2.avail_out ≠ 0 → st2.pending = 0)) := by
  obtain ⟨z, st, al, hz, hb, hst, hal, c⟩ := F.live
  obtain ⟨hp0, hwin⟩ := hp st hst
  obtain ⟨hlv, -, -, h8⟩ := F.st st hst
  obtain ⟨h', e, P⟩ := flush_block_only_ok T window last hl0 hl1 F.inv F.io F.set hz hb hst hp0 hlv h8 hwin hwm
  obtain ⟨z', st', -, hz', hst', -, -, -, -, hpz', -, -⟩ := P.out
  refine ⟨(), h', e, ?_⟩
  obtain ⟨z2, st2, L, hz2, hst2, hLo, hav, hze, hadv, hpz, hsym, st1, hK1, hst2e⟩ := P.out
  obtain rfl : z' = z2 := Option.some.inj (hz'.symm.trans hz2)
  obtain rfl : st' = st2 := Option.some.inj (hst'.symm.trans hst2)
  have hzs : z'.state = some b := by rw [hze]; exact hb
  have hss := (strstart_toInt32 c).1
  simp only [dview] at hss
  obtain ⟨-, -, -, hl2, -, -, hse⟩ := c.sizes
  simp only [dview] at hse hl2
  have hk : st'.lookahead = st.lookahead ∧ st'.strstart = st.strstart ∧ st'.window = st.window ∧
      st'.level = st.level ∧ st'.status = st.status ∧ st'.block_start = st.strstart.toInt32 ∧
      st'.sym_end = st.sym_end := by
    rw [hst2e, hK1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ := hk
  have hK : StratKeeps st st' := by rw [hst2e, hK1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨UInt32.le_refl _, rfl⟩⟩
  have hsend : st'.sym_next < st'.sym_end := by
    rw [hsym, hk7]; apply UInt32.lt_iff_toNat_lt.mpr; simp; omega
  obtain ⟨z0, z4, ob, oo, k, h0, h4, e0, e4, ek⟩ := F.out
  obtain rfl : z = z4 := Option.some.inj (hz.symm.trans h4)
  have hdo : dOutputRanges h (some i) = [(z0.next_out, z0.avail_out.toNat)] := by simp [dOutputRanges, h0]
  refine ⟨by simp only [avIn, hz', hz]; rw [hze], ⟨P.inv, P.io, P.set, ?_, ⟨z', hz', hzs⟩, F.blk0, ?_, ?_,
    F.inp.keep hz hz' (by rw [hze]) (by rw [hze]), ?_, ?_, ?_, fb_acc F P hz hst c last fun e0 => hsy0 e0 st hst⟩,
    fun st3 hst3 => ?_, fun z3 st3 hz3 hst3 ha => ?_⟩
  · obtain ⟨⟨-, -, -, -, -, -, ec, ex, -, -⟩, -⟩ := P.frame
    exact ⟨by rw [ec]; exact F.crc.1, by rw [ex]; exact F.crc.2⟩
  · refine dframe_trans F.frame (dframe_wmono P.frame ?_)
    rw [hdo]
    intro c' j hw w hm off he
    rw [List.mem_singleton] at hm; subst hm
    simp only [] at he
    rw [e4] at he
    injection he with he1 he2
    injection he1 with he1
    subst he1; subst he2
    have := hw _ (List.mem_singleton_self _) oo e0
    simp only [] at this
    omega
  · exact ⟨z0, z', ob, oo, k + L, h0, hz', e0, by rw [hadv ob (oo + k) e4]; rw [Nat.add_assoc], by omega⟩
  · obtain ⟨st0, h0', hw⟩ := F.win
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    rw [hk3]; exact hw st hst
  · obtain ⟨st0, h0', hw⟩ := F.keeps
    refine ⟨st0, h0', fun st3 hst3 => ?_⟩
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact StratKeeps.trans (hw st hst) hK
  · intro st3 hst3
    obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact ⟨by rw [hk4]; exact hlv, by rw [hk5]; exact (F.st st hst).2.1, fun _ => hsym, P.bits _ hst'⟩
  · obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    exact ⟨hsym, hsend, st, hst, hk1, hk2, hk3⟩
  · obtain rfl : st' = st3 := Option.some.inj (hst'.symm.trans hst3)
    obtain rfl : z' = z3 := Option.some.inj (hz'.symm.trans hz3)
    exact hpz' ha
end ZlibNgF.Proof.Strategy
