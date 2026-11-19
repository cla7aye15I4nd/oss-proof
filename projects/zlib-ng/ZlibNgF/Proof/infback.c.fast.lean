import ZlibNgF.Proof.«infback.c.stored»
import ZlibNgF.Proof.«inflate.c.callees»

/-!
# `inflateBack()`: the fast path of `LEN` (`ZlibNgF`)

With at least 15 input bytes and 3 bytes of room, `LEN` stores the locals into the stream and the state (`RESTORE`),
calls `inflate_fast_safe_c(strm, state->wsize)` with its output inside the caller's window (`next_out == window +
(wsize - left)`, so `beg == window`), and loads them back (`LOAD`). `inflate_fast_post_w` (same-block case) gives the
records it leaves: fewer than 8 bits held, at least one input bit consumed, a new mode among `LEN`, `TYPE`, `BAD` and
`MATCH` with a non-zero distance, only window bytes written, nothing allocated.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InflateLoop (withS)
open ZlibNgF.Proof.ChunkCopy (B)

/-- A frame that names a part of the window is in the frame that names the window. -/
theorem Frame.sub {h h' : Heap} {S L G : List Nat} {wb woff n j k : Nat}
    (f : Frame h h' S L G [(.ref (.heap wb) (woff + j), k)]) (hjk : j + k ≤ n) :
    Frame h h' S L G [(.ref (.heap wb) woff, n)] := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩
  obtain ⟨d', e', sz', q⟩ := b1 c hc hn data hd
  refine ⟨d', e', sz', fun x hx hw => q x hx ?_⟩
  intro w hw' off hoff
  simp only [List.mem_singleton] at hw'
  subst hw'
  simp only [Ptr.ref.injEq, BRef.heap.injEq] at hoff
  obtain ⟨rfl, rfl⟩ := hoff
  have := hw _ (List.mem_singleton_self _) woff rfl
  simp only at this ⊢
  omega

theorem Frame.sub' {h h' : Heap} {S L G : List Nat} {p : BPtr} {wb woff n j k : Nat}
    (f : Frame h h' S L G [(p, k)]) (hp : p = .ref (.heap wb) (woff + j)) (hjk : j + k ≤ n) :
    Frame h h' S L G [(.ref (.heap wb) woff, n)] := by
  subst hp; exact Frame.sub f hjk

theorem space_withS (H : Heap) (b : Nat) (S : InflateState) (r : BRef) :
    Space.get (withS H b S) r = Space.get H r := by cases r <;> rfl

theorem space_withZ (H : Heap) (i : Nat) (z : ZStream) (r : BRef) :
    Space.get (withZ H i z) r = Space.get H r := by cases r <;> rfl

theorem rank_le5 (m : UInt32) : rank m ≤ 5 := rank_le m

/-- The fast path of `LEN`. -/
theorem len_fast {E : BEnv} (cb : E.CB) {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bl : BL E l H t z S) (hm : S.mode = LEN) (hh : 15 ≤ l.have_.toNat) (hl : 3 ≤ l.left.toNat) {m : Nat}
    (hμ : μ l t S ≤ m) :
    SatX H l (do
      RESTORE E.c.ctx
      ZlibNg.ChunksetC.inflate_fast_safe_c E.c.strm (← rdS E.c.st (·.wsize))
      LOAD E.c.ctx : X Unit) (Post E m) := by
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 1 ≤ m := by
    unfold μ at hμ; rw [hm, rank_LEN] at hμ; exact hμ
  have hn := bl.sh.ws
  have hL := bl.left
  have hh0 : l.have_ ≠ 0 := fun e => by rw [e] at hh; simp at hh
  obtain ⟨ri, oi, A, hnx, hA, hAs, -⟩ := InB.src cb bl.inB hh0
  obtain ⟨wd, hwd, hws⟩ := bl.sh.wd
  obtain ⟨bd, hbd⟩ := bl.sh.hd
  obtain ⟨hlt, hdt⟩ := bl.modes.dec (Or.inl hm)
  unfold RESTORE
  refine SatX.bind (SatX.bind (SatX.get ?_))
  dsimp only [BEnv.c, BCtx.ctx]
  refine SatX.bind (SatX.lift (Sat.of_eq (bl.sh.wrZ _) ?_))
  have bm1 := bl.toBM.wZ cb { z with
    next_out := l.put
    avail_out := l.left
    next_in := l.next
    avail_in := l.have_ } rfl rfl
  refine SatX.lift (Sat.of_eq (bm1.sh.wrS _) ?_)
  dsimp only
  have bm2 := bm1.wS cb (S' := { S with
    hold := l.hold
    bits := l.bits.toUInt32 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.bind (liftEq (bm2.sh.rdS _) ?_)
  dsimp only
  have hst2 := bm2.sh.istate
  have hz2 := bm2.sh.hz
  have hlp : (S.wsize - l.left).toNat = E.n - l.left.toNat := by
    rw [u32_sub_le (by rw [hn]; exact hL), hn]
  have hlc : ∀ (p : Ival CodePtr) (n : UInt32) (dist : Bool), RTab E.b S.codes p n 28 dist →
      ∃ c, p = .val c ∧ ∀ r o b', c = .ref r o → r = .codes b' → b' ≠ E.wb := by
    intro p n dist ht
    rcases ht with ⟨o, e, hp, -⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · refine ⟨_, hp, fun r o' b' e1 e2 => ?_⟩
      cases e1; cases e2; exact Ne.symm bl.sh.wbb
    · exact ⟨_, hp, fun r o' b' e1 e2 => by cases e1; cases e2⟩
    · exact ⟨_, hp, fun r o' b' e1 e2 => by cases e1; cases e2⟩
  obtain ⟨lc, dc, hlc', hdc', htab⟩ := ZlibNgF.Proof.InffastFacts.tabAt_fast' hst2 hlt.tabAt hdt.tabAt
  obtain ⟨lc', e1, hlnb⟩ := hlc _ _ _ hlt
  obtain ⟨dc', e2, hdnb⟩ := hlc _ _ _ hdt
  have hlnb' : ∀ r o b', lc = .ref r o → r = .codes b' → b' ≠ E.wb := by
    intro r o b' h1 h2; rw [e1] at hlc'; cases hlc'; exact hlnb r o b' h1 h2
  have hdnb' : ∀ r o b', dc = .ref r o → r = .codes b' → b' ≠ E.wb := by
    intro r o b' h1 h2; rw [e2] at hdc'; cases hdc'; exact hdnb r o b' h1 h2
  have hfast := ZlibNgF.Proof.InffastMain.inflate_fast_post_w true _ E.i E.b _
    { S with
      hold := l.hold
      bits := l.bits.toUInt32 } S.wsize ri oi E.wb E.woff A wd hm
    hz2 bl.sh.zs hst2 (by rw [UInt32.lt_iff_toNat_lt]; simp; omega) bl.sh.wbb bd hbd E.wb E.woff wd
    (Or.inr ⟨rfl, rfl, rfl, rfl, bl.sh.wnext⟩) bl.sh.win hwd (by rw [hn]; exact hws)
    (by rcases bl.whave with e | e <;> rw [e] <;> simp [UInt32.le_iff_toNat_le])
    (by rw [bl.sh.wnext]; simp [UInt32.le_iff_toNat_le]) lc dc hlc' hdc' htab hlnb' hdnb'
    (by rw [UInt32.le_iff_toNat_le]; exact hh) (by rw [UInt32.le_iff_toNat_le, hn]; exact hL)
    (by simp only [↓reduceIte]; rw [UInt32.le_iff_toNat_le]; exact hl) hnx
    (by rw [space_withS, space_withZ]; exact hA) hAs
    (by show l.put = _; rw [bl.put, hlp]) hwd (by rw [hn]; exact hws)
  refine SatX.bind (SatX.lift (Sat.mono hfast ?_))
  rintro _ H3 ⟨⟨ai, ao, m', hold, bits, len, was, off, msg, hmeas, hai, hao, hz3, hs3, hmode, hbits, hmeas2,
    hbb, hia, hoth, hbo, hfr⟩, hnb⟩
  have hbd3 : H3.bytes E.b = some bd := by rw [hbb]; exact hbd
  have hs3' := (show H3.istate E.b = H3.istates E.b by simp only [Heap.istate, hbd3]).trans hs3
  unfold LOAD
  dsimp only [BEnv.c, BCtx.ctx]
  refine SatX.bind (liftEq (InflateInv.ldStream_app hz3) ?_)
  refine SatX.bind (liftEq (InflateInv.ldState_app hs3') ?_)
  refine SatX.modify ?_
  have hb32 : bits.toNat < 8 := by rw [UInt32.lt_iff_toNat_lt] at hbits; simpa using hbits
  have hai' : ai.toNat ≤ l.have_.toNat := UInt32.le_iff_toNat_le.mp hai
  have hao' : ao.toNat ≤ l.left.toNat := UInt32.le_iff_toNat_le.mp hao
  have hb8' : bits.toUInt8.toNat = bits.toNat := by
    rw [UInt32.toNat_toUInt8]; exact Nat.mod_eq_of_lt (by omega)
  have hmeas' : 8 * ai.toNat + bits.toNat + 1 ≤ 8 * l.have_.toNat + l.bits.toNat := by
    have := hmeas; simp only [UInt8.toNat_toUInt32] at this; exact this
  obtain ⟨wd3, hwd3, hws3⟩ := hbo wd hwd
  have sh3 : BShape E H3 _ _ :=
    { bm2.sh with
      hz := hz3
      hd := ⟨bd, hbd3⟩
      hs := hs3
      al := by rw [hia]; exact bm2.sh.al
      wd := ⟨wd3, hwd3, by omega⟩ }
  have hin3 := InB.lstep cb bm2.inB ⟨Frame.sub' (n := E.n) (k := l.left.toNat) hfr bl.put (by omega), hnb⟩
  refine ⟨t, _, _, ⟨⟨sh3, InB.adv hin3 hnx (c := (l.have_ - ai).toNat) (by rw [u32_sub_le hai']; omega)
    (by show ai.toNat = _; rw [u32_sub_le hai']; omega) rfl, by have := bl.tot; show ai.toNat + t < _; omega,
    ?_, ?_, bl.whave⟩, Or.inr (by show bits.toUInt8.toNat < 8; omega), ?_⟩, ?_⟩
  · show Ptr.ref _ _ = _
    rw [u32_sub_le (by rw [hn]; omega), hn]
  · show ao.toNat ≤ E.n; omega
  · refine ⟨fun _ => ⟨hlt, hdt⟩, fun hM => ?_⟩
    rcases hmode with e | e | e | ⟨-, -, ho⟩
    · exact absurd (hM.symm.trans e) (by decide)
    · exact absurd (hM.symm.trans e) (by decide)
    · exact absurd (hM.symm.trans e) (by decide)
    · exact ho
  · have := rank_le5 m'
    unfold μ; dsimp only
    rw [hb8']
    omega

end ZlibNgF.Proof.InfbackLoop
