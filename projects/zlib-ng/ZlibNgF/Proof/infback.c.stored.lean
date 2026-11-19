import ZlibNgF.Proof.«infback.c.match»

/-!
# `inflateBack()`: the mode `STORED` (`ZlibNgF`)

`STORED` drops the bits up to a byte boundary, reads the 32-bit length pair, and copies `length` bytes from the
input chunks to the window in pieces of at most `have` and `left` bytes, calling `in()` when the chunk is used up
(`PULL`) and `out()` when the window is full (`ROOM`). The `memcpy` source lies in the chunk that `in()` handed out
and the destination in the window: `BackCallbacks.chunk` says they do not overlap.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InfbackLoop
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Infback ZlibNg.InflateP
open ZlibNgF.Proof.InflateX
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.mono Sat.of_eq)
open ZlibNgF.Proof.InfbackPull
open ZlibNgF.Proof.InfbackRoom
open ZlibNgF.Proof.InflateLoop (withS strIdx bytebits_ok bytebits_le initbits_ok memcpy_heap' copyFold_out)
open ZlibNgF.Proof.InflateDict (copyFold copyFold_size)

/-- The input bytes `[next, next + have)` are readable and lie outside the window. -/
theorem InB.src {E : BEnv} (cb : E.CB) {H : Heap} {l : IL} {t : Nat} (hin : InB E.I H l t) (h0 : l.have_ ≠ 0) :
    ∃ r o d, l.next = .ref r o ∧ Space.get H r = some d ∧ o + l.have_.toNat ≤ d.size ∧
      (r = .heap E.wb → o + l.have_.toNat ≤ E.woff ∨ E.woff + E.n ≤ o) := by
  obtain ⟨r, o, d, hnx, hg, hsz⟩ := InB.bytes cb hin h0
  refine ⟨r, o, d, hnx, hg, hsz, fun hr => ?_⟩
  obtain ⟨p, m, hI, hle, hat⟩ := hin
  obtain ⟨r', o', hp, hn'⟩ := hat h0
  rw [hnx] at hn'
  simp only [Ptr.ref.injEq] at hn'
  obtain ⟨rfl, ho⟩ := hn'
  have hm : m ≠ 0 := by have := u32_ne_zero h0; omega
  obtain ⟨-, hdj, -⟩ := cb.chunk H p m t hI hm
  rw [hp] at hdj
  simp only [Disjoint, BEnv.w, hr] at hdj
  rcases hdj with h | h | h
  · exact absurd rfl h
  · left; omega
  · right; omega

/-- `InB` after `copy` bytes of the input are used. -/
theorem InB.adv {I : Heap → BPtr → Nat → Nat → Prop} {H : Heap} {l l' : IL} {t : Nat} (hin : InB I H l t)
    {r : BRef} {o c : Nat} (hnx : l.next = .ref r o) (hc : c ≤ l.have_.toNat) (hh : l'.have_.toNat = l.have_.toNat - c)
    (hn : l'.next = .ref r (o + c)) : InB I H l' t := by
  obtain ⟨p, m, hI, hle, hat⟩ := hin
  refine ⟨p, m, hI, by omega, fun h0 => ?_⟩
  have h1 : l.have_ ≠ 0 := fun e => by rw [e] at hh; simp at hh; exact h0 (UInt32.toNat_inj.mp (by rw [hh]; rfl))
  obtain ⟨r', o', hp, hn'⟩ := hat h1
  rw [hnx] at hn'
  simp only [Ptr.ref.injEq] at hn'
  obtain ⟨rfl, ho⟩ := hn'
  refine ⟨r, o', hp, ?_⟩
  rw [hn, hh]
  simp only [Ptr.ref.injEq, true_and]
  omega

theorem rank_STORED : rank STORED = 4 := by decide

/-- The state of the copy loop of `STORED`, with at most `K` input bytes left. -/
def SP (E : BEnv) (K : Nat) (l : IL) (H : Heap) : Prop :=
  ∃ t z S, BM E l H t z S ∧ S.mode = STORED ∧ l.bits = 0 ∧ l.have_.toNat + t ≤ K

theorem BM.rk {E : BEnv} {l : IL} {H : Heap} {t : Nat} {z : ZStream} {S : InflateState}
    (bm : BM E l H t z S) : lenRank E H = S.length.toNat := by
  unfold lenRank; rw [bm.sh.istate]

theorem get_win {E : BEnv} {H : Heap} {a' : Array UInt8} {r : BRef} {d : Array UInt8} (hg : Space.get H r = some d)
    {a : Array UInt8} (ha : H.bytes E.wb = some a) (hsz : a'.size = a.size) :
    ∃ d', Space.get ({ H with bytes := upd H.bytes E.wb (some a') } : Heap) r = some d' ∧ d'.size = d.size := by
  cases r with
  | heap c =>
    by_cases e : c = E.wb
    · subst e
      have : d = a := by
        have h2 : Space.get H (BRef.heap E.wb) = H.bytes E.wb := rfl
        rw [h2, ha] at hg; cases hg; rfl
      subst this
      exact ⟨a', upd_same _ _ _, hsz⟩
    · refine ⟨d, ?_, rfl⟩
      show upd H.bytes E.wb (some a') c = some d
      rw [upd_ne _ _ _ _ e]; exact hg
  | const c => exact ⟨d, hg, rfl⟩
  | str c => exact ⟨d, hg, rfl⟩

theorem add_ref {H : Heap} {r : BRef} {o : Nat} {a : Array UInt8} (hd : Space.get H r = some a) (j : Nat)
    (h : o + j ≤ a.size) : (Ptr.ref r o : BPtr).add (Int.ofNat j) H = .ok (.ref r (o + j), H) := by
  have hc : o ≤ a.size ∧ 0 ≤ (o : Int) + Int.ofNat j ∧ (o : Int) + Int.ofNat j ≤ (a.size : Int) := by
    refine ⟨by omega, by simp; omega, by simp; omega⟩
  simp only [Ptr.add, hd, hc, and_self, ↓reduceIte]
  congr 3

/-- The copy of one piece, after `PULL` and `ROOM`. -/
theorem stored_rest {E : BEnv} (cb : E.CB) {K : Nat} {l : IL} {H : Heap} {t : Nat} {z : ZStream}
    {S : InflateState} (bm : BM E l H t z S) (hm : S.mode = STORED) (hb : l.bits = 0) (hK : l.have_.toNat + t ≤ K)
    (hc : l.copy = S.length) (hne : S.length ≠ 0) (hh : l.have_ ≠ 0) (hl : l.left ≠ 0) {R : Nat}
    (hR : S.length.toNat ≤ R) :
    SatX H l (do
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32 }
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.left.toUInt64).toUInt32 }
      let l ← get
      Ptr.memcpy l.put l.next l.copy.toNat
      let nx ← l.next.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
      let pt ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with left := l.left - l.copy, put := pt }
      let copy := (← get).copy
      wrS E.c.st fun s => { s with length := s.length - copy } : X Unit) (fun r l' H' => match r with
        | .ok () => SP E K l' H' ∧ lenRank E H' < R
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  have hh1 := u32_ne_zero hh
  have hl1 := u32_ne_zero hl
  have hn1 := u32_ne_zero hne
  have hL := bm.left
  obtain ⟨a, ha, haN⟩ := bm.winBytes
  obtain ⟨r, o, d, hnx, hg, hsz, hdj⟩ := InB.src cb bm.inB hh
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only
  have e1 : (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32.toNat =
      min S.length.toNat l.have_.toNat := by
    rw [min32 _ _ (by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _), UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt64, hc]
  generalize (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32 = c1 at e1 ⊢
  have e2 : (ZlibNg.Zbuild.MIN c1.toUInt64 l.left.toUInt64).toUInt32.toNat = min c1.toNat l.left.toNat := by
    rw [min32 _ _ (by rw [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _), UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt64]
  generalize (ZlibNg.Zbuild.MIN c1.toUInt64 l.left.toUInt64).toUInt32 = c at e2 ⊢
  have hc1 : 1 ≤ c.toNat := by rw [e2, e1]; omega
  have hch : c.toNat ≤ l.have_.toNat := by rw [e2, e1]; omega
  have hcl : c.toNat ≤ l.left.toNat := by rw [e2]; omega
  have hcn : c.toNat ≤ S.length.toNat := by rw [e2, e1]; omega
  rw [bm.put, hnx]
  have hov : r = .heap E.wb → E.woff + (E.n - l.left.toNat) + c.toNat ≤ o ∨ o + c.toNat ≤ E.woff + (E.n - l.left.toNat) := by
    intro hr; rcases hdj hr with h | h
    · right; omega
    · left; omega
  refine SatX.bind (SatX.lift (Sat.of_eq (memcpy_heap' ha hg hov (by omega) (by omega)) ?_))
  have hsz' := copyFold_size d (E.woff + (E.n - l.left.toNat)) o (List.range' 0 c.toNat) a
  have bm4 := bm.winW cb ha hsz' (fun j hj => copyFold_out _ _ _ _ _ j (by omega))
  obtain ⟨d4, hg4, hs4⟩ := get_win (E := E) hg ha hsz'
  refine SatX.bind (liftEq (add_ref hg4 _ (by omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  obtain ⟨a4, ha4, ha4N⟩ := bm4.winBytes
  refine SatX.bind (liftEq (add_nat ha4 _ (by omega)) ?_)
  refine SatX.bind (SatX.modify ?_)
  refine SatX.bind (SatX.get ?_)
  dsimp only [BEnv.c]
  have bm5 := bm4.wS cb (S' := { S with length := S.length - c }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SatX.lift (Sat.of_eq (bm4.sh.wrS _) ⟨⟨t, z, _, ⟨bm5.sh, ?_, ?_, ?_, ?_, bm5.whave⟩, hm, hb, ?_⟩, ?_⟩)
  · refine InB.adv bm5.inB hnx hch ?_ ?_
    · show (l.have_ - c).toNat = _; exact u32_sub_le hch
    · rfl
  · show (l.have_ - c).toNat + t < 2 ^ 48
    have := bm.tot; rw [u32_sub_le hch]; omega
  · show Ptr.ref _ _ = Ptr.ref _ (E.woff + (E.n - (l.left - c).toNat))
    rw [u32_sub_le hcl]
    simp only [Ptr.ref.injEq, true_and]; omega
  · show (l.left - c).toNat ≤ E.n
    rw [u32_sub_le hcl]; omega
  · show (l.have_ - c).toNat + t ≤ K
    rw [u32_sub_le hch]; omega
  · show lenRank E _ < R
    rw [BM.rk bm5]
    show (S.length - c).toNat < R
    rw [u32_sub_le hcn]; omega

/-- One piece of the copy of `STORED`. -/
theorem stored_piece {E : BEnv} (cb : E.CB) {K : Nat} {l : IL} {H : Heap} {t : Nat} {z : ZStream}
    {S : InflateState} (bm : BM E l H t z S) (hm : S.mode = STORED) (hb : l.bits = 0) (hK : l.have_.toNat + t ≤ K)
    (hne : S.length ≠ 0) :
    SatX H l (do
      let len ← rdS E.c.st (·.length)
      modify fun l => { l with copy := len }
      PULL E.c
      ROOM E.c
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32 }
      modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.left.toUInt64).toUInt32 }
      let l ← get
      Ptr.memcpy l.put l.next l.copy.toNat
      let nx ← l.next.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
      let pt ← l.put.add (Int.ofNat l.copy.toNat)
      modify fun l => { l with left := l.left - l.copy, put := pt }
      let copy := (← get).copy
      wrS E.c.st fun s => { s with length := s.length - copy } : X Unit) (fun r l' H' => match r with
        | .ok () => SP E K l' H' ∧ lenRank E H' < lenRank E H
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) := by
  have hR : S.length.toNat ≤ lenRank E H := by rw [BM.rk bm]; exact Nat.le_refl _
  refine SatX.bind (liftEq (bm.sh.rdS _) ?_)
  refine SatX.bind (SatX.modify ?_)
  dsimp only
  have bm1 := bm.locals (l' := { l with copy := S.length }) rfl rfl rfl rfl
  have room : ∀ l2 H2 t2 (bm2 : BM E l2 H2 t2 z S), l2.have_ ≠ 0 → l2.bits = 0 → l2.copy = S.length →
      l2.have_.toNat + t2 ≤ K → SatX H2 l2 (do
        ROOM E.c
        modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.have_.toUInt64).toUInt32 }
        modify fun l => { l with copy := (ZlibNg.Zbuild.MIN l.copy.toUInt64 l.left.toUInt64).toUInt32 }
        let l ← get
        Ptr.memcpy l.put l.next l.copy.toNat
        let nx ← l.next.add (Int.ofNat l.copy.toNat)
        modify fun l => { l with have_ := l.have_ - l.copy, next := nx }
        let pt ← l.put.add (Int.ofNat l.copy.toNat)
        modify fun l => { l with left := l.left - l.copy, put := pt }
        let copy := (← get).copy
        wrS E.c.st fun s => { s with length := s.length - copy } : X Unit) (fun r l' H' => match r with
          | .ok () => SP E K l' H' ∧ lenRank E H' < lenRank E H
          | .error .leave => BLv E l' H'
          | .error (.ret _) => False) := by
    intro l2 H2 t2 bm2 hh2 hb2 hc2 hK2
    refine SatX.bind (bm2.room cb (fun hl => stored_rest cb bm2 hm hb2 hK2 hc2 hne hh2 hl hR) ?_)
    intro _ H3 bm3
    have hn := bm2.sh.ws
    have hn1 := bm2.sh.n_pos
    have hw0 : S.wsize ≠ 0 := fun e => by rw [e] at hn; simp at hn; omega
    exact ⟨(bm3.locals rfl rfl rfl rfl).leave,
      stored_rest cb (S := { S with whave := S.wsize }) bm3 hm hb2 hK2 hc2 hne hh2 hw0 hR⟩
  refine SatX.bind (pull_ok cb E.c rfl rfl bm1.inB ?_ ?_ ?_)
  · intro hh
    exact room _ _ _ bm1 hh hb rfl hK
  · intro h0 H' q hk hI
    refine ⟨t, z, S, bm.sh.keep hk, ⟨q, 0, hI, Nat.zero_le _, fun h => absurd rfl h⟩, bm.put, bm.left⟩
  · intro h0 k q H' hk0 hkeep hkt hin'
    have hh0 : l.have_.toNat = 0 := by rw [h0]; rfl
    refine room _ _ (t - k.toNat) ⟨bm.sh.keep hkeep, hin', ?_, bm.put, bm.left, bm.whave⟩ hk0 hb rfl ?_
    · have := bm.tot; show k.toNat + (t - k.toNat) < 2 ^ 48; omega
    · show k.toNat + (t - k.toNat) ≤ K; omega

theorem run_STORED (E : BEnv) : ModeRun E back_STORED (fun S => S.mode = STORED) := by
  intro cb l H t z S bl hm m hμ
  have hb8 : l.bits.toNat < 8 := by
    rcases bl.bits with e | e
    · rw [hm] at e; exact absurd e (by decide)
    · exact e
  have hμ' : 32 * (8 * (l.have_.toNat + t) + l.bits.toNat) + 4 ≤ m := by
    unfold μ at hμ; rw [hm, rank_STORED] at hμ; exact hμ
  unfold back_STORED
  refine SatX.bind (bytebits_ok ?_)
  have hbz : (l.bits - (l.bits &&& 7)).toNat = 0 := by
    have : l.bits &&& 7 = l.bits := by
      apply UInt8.toNat_inj.mp; rw [UInt8.toNat_and]
      show l.bits.toNat &&& 7 = l.bits.toNat
      rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
    rw [this]; simp
  have bm0 := bl.toBM.locals (l' := { l with
    hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64
    bits := l.bits - (l.bits &&& 7) }) rfl rfl rfl rfl
  refine SatX.bind (needbits_ok cb E.c rfl rfl bm0.inB 32 (by decide) ?_ ?_)
  · intro l' H' t' q hk hI hp h0 _ _
    exact leave_of_pull bm0 hk hI hp h0
  intro l1 H1 t1 hk hin1 hmeas h32 hb1 hp1 _
  have h32' : 32 ≤ l1.bits.toNat := h32
  have hb0 : ({ l with
    hold := l.hold >>> (l.bits &&& 7).toUInt32.toUInt64
    bits := l.bits - (l.bits &&& 7) } : IL).bits.toNat = 0 := hbz
  have hmeas' : 8 * (l1.have_.toNat + t1) + l1.bits.toNat = 8 * (l.have_.toNat + t) := by
    have := hmeas; rw [hb0] at this; exact this
  clear hmeas
  have bm1 : BM E l1 H1 t1 z S := by
    refine ⟨bl.sh.keep hk, hin1, ?_, by rw [hp1]; exact bl.put, by rw [hp1]; exact bl.left, bl.whave⟩
    have := bl.tot; omega
  refine SatX.bind (SatX.get ?_)
  dsimp only
  split
  · obtain ⟨H', z', e, bm'⟩ := bm1.setBad cb "invalid stored block lengths"
      (strIdx 24 (by decide) (by decide) (by decide))
    refine SatX.bind (SatX.lift (Sat.of_eq e ?_))
    refine SatX.pure ⟨t1, z', _, ⟨bm', Or.inl rfl, BModeOK.quiet _ { S with mode := BAD }
      (by show BAD ≠ LEN; decide) (by show BAD ≠ MATCH; decide)⟩, ?_⟩
    unfold μ; dsimp only; rw [rank_BAD]; omega
  · refine SatX.bind (SatX.lift (Sat.of_eq (bm1.sh.wrS _) ?_))
    have bm2 := bm1.wS cb (S' := { S with length := l1.hold.toUInt16.toUInt32 }) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine SatX.bind (initbits_ok ?_)
    have bm3 := bm2.locals (l' := { l1 with hold := 0, bits := 0 }) rfl rfl rfl rfl
    unfold xwhile
    refine SatX.bind (SatX.mono (xwhileBrk_rank (SP E (l1.have_.toNat + t1)) (fun _ H' => lenRank E H')
      (fun r l' H' => match r with
        | .ok () => SP E (l1.have_.toNat + t1) l' H'
        | .error .leave => BLv E l' H'
        | .error (.ret _) => False) ?_ ⟨t1, z, _, bm3, hm, rfl, Nat.le_refl _⟩ ?_) ?_)
    · rintro l2 H2 ⟨t2, z2, S2, bm2', hm2, hb2, hK2⟩
      refine SatX.bind (liftEq (bm2'.sh.rdS _) ?_)
      refine SatX.pure ?_
      dsimp only
      by_cases hne : S2.length = 0
      · have e : (S2.length != 0) = false := by simp [hne]
        rw [e]
        exact ⟨t2, z2, S2, bm2', hm2, hb2, hK2⟩
      · have e : (S2.length != 0) = true := by simpa using hne
        rw [e]
        refine SatX.bind (SatX.mono (stored_piece cb bm2' hm2 hb2 hK2 hne) ?_)
        rintro r l3 H3 p
        match r, p with
        | .ok (), p => exact SatX.pure p
        | .error .leave, p => exact p
        | .error (.ret _), p => exact p.elim
    · rw [BM.rk bm3]
      show (l1.hold.toUInt16.toUInt32).toNat + 2 < fuel
      have := (l1.hold.toUInt16.toUInt32).toNat_lt; unfold fuel; omega
    · rintro r l2 H2 p
      match r, p with
      | .error .leave, p => exact p
      | .ok (), ⟨t2, z2, S2, bm2', hm2, hb2, hK2⟩ =>
        obtain ⟨e, bm4⟩ := bm2'.setMode cb TYPE
        refine SatX.lift (Sat.of_eq e ⟨t2, z2, _, ⟨bm4, Or.inr (by rw [hb2]; decide),
          BModeOK.quiet _ { S2 with mode := TYPE } (by show TYPE ≠ LEN; decide) (by show TYPE ≠ MATCH; decide)⟩, ?_⟩)
        unfold μ; dsimp only; rw [rank_TYPE, hb2]; simp only [UInt8.toNat_zero]; omega

end ZlibNgF.Proof.InfbackLoop
