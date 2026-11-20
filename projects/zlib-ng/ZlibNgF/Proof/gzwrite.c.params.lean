import ZlibNgF.Proof.«gzwrite.c.calls»
import ZlibNgF.Proof.«gzwrite.c.compdone»

/-!
# `gzsetparams` on a write handle (`ZlibNgF`)

`gzsetparams_spec`: on a write handle, `gzsetparams` keeps the invariant `GzInvWS` and is a step of the file
(`CallPost`), given `DeflateGz`. The pending seek goes through `gz_zero_spec`, input left in the
buffer through `gz_comp(Z_BLOCK)` (`comp_inv`), then the loop of `deflateParams` (`params_stepW`) and
`gz_comp(Z_BLOCK)` (`GzCompSpec` with the potential of `DeflateGz`). The loop ends by
`2^52 [reset ≠ 0] + pot ψ Z_BLOCK + [avail_out = 0]` (`spMu`): with no input, `deflateParams` lowers `ψ` by the bytes
it produces; `gz_comp` without a pending `reset` does not raise `pot`, and one with a pending `reset` clears it and
leaves `pot ≤ 2^50`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- The `deflateParams` clause of `DeflateGz` for a potential `ψ` and growth `G`. -/
def ParamsClause (ψ : Int32 → C.DeflateState → Nat) (G : Nat) : Prop :=
  ∀ (h h' : Heap) (s : StreamPtr) (level strategy r : Int32), DeflateInv.DInv h s → DeflateSide.DSide h s →
    CrcGlobals h → DRegisteredHeader h s none → DStreamIO h s →
    C.run (ZlibNg.Deflate.deflateParams s level strategy) h = .ok (r, h') →
    CallOk (ψ ZlibNg.Inflate.Z_BLOCK) G 0 h h' s ∧ DKeep h h' s

/-- **`deflateParams`** on the stream of a write handle with buffers (not direct): no fault, the buffer fields move
(`BufAdv`), the potential drops by the bytes produced (less `G` per input byte), and the invariant of the handle. -/
theorem params_stepW (P : DeflateReach.DPending) {ψ : Int32 → C.DeflateState → Nat} {G : Nat}
    (hP : ParamsClause ψ G)
    {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s)
    (hsz : s.size ≠ 0) (hd : s.direct = 0) (level strategy : Int32) :
    ∃ r H' z z', ZlibNg.Deflate.deflateParams (some s.strm) level strategy H = .ok (r, H') ∧
      H.streams s.strm = some z ∧ H'.streams s.strm = some z' ∧ BufAdv z z' ∧
      (∀ sb st st', DStateOf H (some s.strm) sb st → DStateOf H' (some s.strm) sb st' →
        ψ ZlibNg.Inflate.Z_BLOCK st' + (z.avail_out.toNat - z'.avail_out.toNat) ≤
          ψ ZlibNg.Inflate.Z_BLOCK st + G * (z.avail_in.toNat - z'.avail_in.toNat)) ∧
      GzInvWS W H' (some b) ∧ W.gz H' b = some s ∧ GStep W H W H' b [] := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z, hB, hz, WB⟩ := (sh.write hwm).bufs hsz
  obtain ⟨hdi, hside⟩ := WB.deflate hd
  have hdi0 := hdi
  obtain ⟨i, z0, sb, st, al, e0, hz0, hsb, hst, -, -⟩ := hdi0
  cases e0; rw [hz] at hz0; cases hz0
  have hcs : c ≠ sb := by
    have hsplit : ownL H b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ [c, sb] := by
      simp [ownL, hsz, hB.buffers, blkOf, stBlk, hz, hsb]
    have := (List.nodup_append.mp (hsplit ▸ hn)).2.1
    simp at this; exact this
  have hio := streamIO_W hB hz hwm hd WB hsb hcs hdi
  obtain ⟨r, H', e, f, hdi', hside'⟩ :=
    DeflateParams.params_ok (level := level) (strategy := strategy) P.deflate hdi hside hv.2.2.1 hio
  obtain ⟨hco, hk⟩ := hP H H' (some s.strm) level strategy r hdi hside hv.2.2.1 (regNone hz WB hdi) hio e
  obtain ⟨z', ⟨i', e1, hz'⟩, hadv, hmu⟩ := hco z ⟨_, rfl, hz⟩
  cases e1
  have hsi : stateIds H (some s.strm) = [sb] := by simp [stateIds, hz, hsb]
  have hdo : dOutputRanges H (some s.strm) = [(z.next_out, z.avail_out.toNat)] := by simp [dOutputRanges, hz]
  rw [hsi, hdo] at f
  obtain ⟨ko, kx, eo, -, -, -⟩ := WB.out hd
  obtain ⟨hinp', hout'⟩ := wbuf_adv hd WB.inp (WB.out hd) hadv
  obtain ⟨hv', hs', g⟩ := invWS_dcall hv hs hsz hd hB hz hsb (by simpa [streamIds] using f)
    (fun x hx c' off e2 => by simp at hx; rw [hx, eo] at e2; cases e2; rfl) hz' hadv.2.2.2.2 hinp' hout' hk
    ⟨hdi', hside'⟩
  refine ⟨r, H', z, z', e, hz, hz', hadv, fun sb0 st0 st1 h1 h2 => ?_, hv', hs', g⟩
  have := hmu sb0 st0 st1 h1 h2
  simpa using this

/-! ## The code of `gzsetparams`, with its parts named -/

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The body of the loop of `gzsetparams` (copied from the translation). -/
def spBody (state : GzPtr) (strm : StreamPtr) (level strategy : Int32) (s : Int32 × Ctl) : G (Int32 × Ctl) := do
  let ret ← lm (deflateParams strm level strategy)
  if ret != Z_BUF_ERROR || (← lm (rdZ strm (·.avail_out))) != 0 then
    return (ret, .brk)
  if (← gz_comp state Z_BLOCK) == -1 then
    return (ret, .ret)
  return (ret, s.2)

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The condition of the loop of `gzsetparams` (copied from the translation). -/
def spCond (s : Int32 × Ctl) : G (Bool × (Int32 × Ctl)) := do
  if s.2 != .go then return (false, s)
  return (s.1 == Z_BUF_ERROR, s)

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The stores of the new parameters. -/
def spFin (state : GzPtr) (level strategy : Int32) : G Int32 := do
  wrG state fun s => { s with level := level }
  wrG state fun s => { s with strategy := strategy }
  return Z_OK

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The loop of `gzsetparams` and what follows it. -/
def spAfter (state : GzPtr) (strm : StreamPtr) (level strategy : Int32) : G Int32 := do
  let lp ← gdoWhile (spBody state strm level strategy) spCond (0, .go)
  if lp.2 == .ret then
    return (← rdG state (·.err))
  if lp.1 != Z_OK then
    return lp.1
  spFin state level strategy

open ZlibNg.Inflate ZlibNg.Deflate in
/-- `gzsetparams` after the pending seek. -/
def spRest (state : GzPtr) (strm : StreamPtr) (level strategy : Int32) : G Int32 := do
  if (← rdG state (·.size)) != 0 then
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state Z_BLOCK) == -1 then
        return (← rdG state (·.err))
    spAfter state strm level strategy
  else
    spFin state level strategy

open ZlibNg.Inflate ZlibNg.Deflate in
theorem gzsetparams_eq (file : GzPtr) (level strategy : Int32) : gzsetparams file level strategy = (do
    if file == none then
      return Z_STREAM_ERROR
    let state := file
    let strm ← strmOf state
    if (← rdG state (·.mode)) != GZ_WRITE || (← rdG state (·.err)) != Z_OK || (← rdG state (·.direct)) != 0 then
      return Z_STREAM_ERROR
    if (level < 0 && level != Z_DEFAULT_COMPRESSION) || level > 9 ||
        strategy < Z_DEFAULT_STRATEGY || strategy > Z_FIXED then
      return Z_STREAM_ERROR
    if level == (← rdG state (·.level)) && strategy == (← rdG state (·.strategy)) then
      return Z_OK
    if (← rdG state (·.skip)) != 0 then
      if (← gz_zero state) == -1 then
        return (← rdG state (·.err))
    spRest state strm level strategy) := by
  unfold gzsetparams spRest spAfter spFin spBody spCond; rfl

/-! ## The pieces -/

/-- The stores of the new parameters: `CallPost`. -/
theorem spFin_spec {w W : World} {h H : Heap} {b : Nat} {s s2 : GzState} (hs0 : w.gz h b = some s)
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s2) (g : GStep w h W H b []) (level strategy : Int32) :
    GSat W H (spFin (some b) level strategy) (CallPost w h b) := by
  unfold spFin
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  refine GSat.bind (GSat.of_eq (wrG_app hs _) ?_)
  have sh1 : GzShape H { s2 with level := level } :=
    shape_congr sh ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨sh.msg.1, sh.msg.2⟩
  have hn1 : (ownL H b { s2 with level := level }).Nodup := hn
  have hsW1 := gz_upd_same (h := H) hs { s2 with level := level }
  obtain ⟨hv1, hs1, g1⟩ := invWS_store hv hs sh1 hn1 hwm rfl (fun c hc _ => by
    simp only [GzOwned, hsW1, hs] at hc ⊢; exact hc)
  refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
  have sh2 : GzShape H { { s2 with level := level } with strategy := strategy } :=
    shape_congr sh ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨sh.msg.1, sh.msg.2⟩
  have hn2 : (ownL H b { { s2 with level := level } with strategy := strategy }).Nodup := hn
  have hsW2 := gz_upd_same (h := H) hs1 { { s2 with level := level } with strategy := strategy }
  obtain ⟨hv2, hs2, g2⟩ := invWS_store hv1 hs1 sh2 hn2 hwm rfl (fun c hc _ => by
    simp only [GzOwned, hsW2, hs1] at hc ⊢; exact hc)
  exact GSat.pure ⟨hv2, (g.trans g1 ⟨s, hs0⟩ ⟨s2, hs⟩).trans g2 ⟨s, hs0⟩ ⟨_, hs1⟩⟩

/-- `spCond` decides on its argument. -/
theorem spCond_sat {x : Int32 × Ctl} {W : World} {H : Heap} {P : Bool × (Int32 × Ctl) → World → Heap → Prop}
    (h1 : x.2 ≠ .go → P (false, x) W H) (h2 : x.2 = .go → P (x.1 == ZlibNg.Inflate.Z_BUF_ERROR, x) W H) :
    GSat W H (spCond x) P := by
  unfold spCond
  by_cases hx : x.2 = .go
  · refine GSat.ite (fun hc => by simp [hx] at hc) (fun _ => GSat.pure (h2 hx))
  · exact GSat.ite (fun _ => GSat.pure (h1 hx)) (fun hc => by simp [hx] at hc)

/-- The facts of the potential of a write handle with buffers (not direct). -/
theorem pot_info {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat} (hψ : DeflatePsi ψ Gr) {W : World} {H : Heap}
    {b : Nat} {s : GzState} {z : ZStream} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s) (hsz : s.size ≠ 0)
    (hd : s.direct = 0) (hz : H.streams s.strm = some z) (f : Int32) :
    ∃ sb st, z.state = some sb ∧ DStateOf H (some s.strm) sb st ∧ ψ f st ≤ 2 ^ 48 ∧
      z.avail_out.toNat ≤ s.size.toNat ∧ s.size.toNat ≤ 2 ^ 30 ∧
      pot ψ f s.size.toNat H s.strm = (2 ^ 31 + 2 ^ 30) * z.avail_in.toNat + 3 * ψ f st +
        2 * (s.size.toNat - (if z.avail_out = 0 then s.size.toNat else z.avail_out.toNat)) := by
  obtain ⟨z1, hx, -⟩ := wx_of_inv hv hs hsz
  have hz1 : H.streams s.strm = some z1 := hx.2.1
  rw [hz] at hz1; cases hz1
  obtain ⟨sb, st, hsb, hst, hdi, hreg, -, h30, hao⟩ := wx_facts hx hd
  have hds : DStateOf H (some s.strm) sb st := ⟨⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst⟩
  exact ⟨sb, st, hsb, hds, hψ.2.1 H (some s.strm) sb st f hdi hreg hds, hao, h30, pot_eq ψ f _ hz hsb hst⟩

/-- The measure of the loop of `gzsetparams`: `2^52` while a `reset` is pending, the potential of the stream, and 1
while the output is full. -/
def spMu (ψ : Int32 → C.DeflateState → Nat) (b i : Nat) (S : Nat) (W : World) (H : Heap) : Nat :=
  (match W.gz H b with | some s => (if s.reset = 0 then 0 else 2 ^ 52) | none => 0) + pot ψ ZlibNg.Inflate.Z_BLOCK S H i +
    (match H.streams i with | some z => (if z.avail_out = 0 then 1 else 0) | none => 0)

theorem spMu_eq (ψ : Int32 → C.DeflateState → Nat) {b i S : Nat} {W : World} {H : Heap} {s : GzState} {z : ZStream}
    (hs : W.gz H b = some s) (hz : H.streams i = some z) :
    spMu ψ b i S W H = (if s.reset = 0 then 0 else 2 ^ 52) + pot ψ ZlibNg.Inflate.Z_BLOCK S H i +
      (if z.avail_out = 0 then 1 else 0) := by
  simp [spMu, hs, hz]

/-- The state of the loop of `gzsetparams`. -/
def SpInv (w : World) (h : Heap) (b : Nat) (s1 : GzState) (x : Int32 × Ctl) (W : World) (H : Heap) : Prop :=
  x.2 = .go ∧ ∃ s2 z2, W.gz H b = some s2 ∧ H.streams s1.strm = some z2 ∧ GzInvWS W H (some b) ∧
    GStep w h W H b [] ∧ s2.strm = s1.strm ∧ s2.direct = 0 ∧ s2.size = s1.size ∧ z2.avail_in = 0

/-- After the loop of `gzsetparams`. -/
def SpOut (w : World) (h : Heap) (b : Nat) (_x : Int32 × Ctl) (W : World) (H : Heap) : Prop :=
  ∃ s2, W.gz H b = some s2 ∧ GzInvWS W H (some b) ∧ GStep w h W H b []

/-- **The loop of `gzsetparams`**. -/
theorem sp_loop (G : DeflateGz) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat} (hψ : DeflatePsi ψ Gr)
    (hP : ParamsClause ψ Gr) {w : World} {h : Heap} {b : Nat} {s0 s1 : GzState} (hs0 : w.gz h b = some s0)
    (hsz : s1.size ≠ 0) {W : World} {H : Heap} (hI : SpInv w h b s1 (0, .go) W H) (level strategy : Int32) :
    GSat W H (gdoWhile (spBody (some b) (some s1.strm) level strategy) spCond (0, .go)) (SpOut w h b) := by
  refine gsat_gdoWhile (SpInv w h b s1) (fun _ W H => spMu ψ b s1.strm s1.size.toNat W H) (SpOut w h b)
    (fun x W H hI => ?_) hI ?_
  · obtain ⟨hx, s2, z2, hs2, hz2, hv2, g2, hstrm2, hd2, hsz2, hai2⟩ := hI
    have hz2' : H.streams s2.strm = some z2 := by rw [hstrm2]; exact hz2
    obtain ⟨r, H', za, z', e, hza, hz', hadv, hmu, hv', hs', g'⟩ :=
      params_stepW DeflatePublic.dpending hP hv2 hs2 (by rw [hsz2]; exact hsz) hd2 level strategy
    rw [hz2'] at hza; cases hza
    have hgo : ∃ s, W.gz H b = some s := ⟨s2, hs2⟩
    have g2' : GStep w h W H' b [] := g2.trans g' ⟨s0, hs0⟩ hgo
    unfold spBody
    rw [← hstrm2]
    refine GSat.bind (GSat.lm ⟨r, H', e, ?_⟩)
    refine GSat.bind (GSat.lm ⟨_, H', rdZ_run hz' _, ?_⟩)
    refine GSat.ite (fun hc => GSat.pure (spCond_sat (fun _ => ⟨fun e => by simp at e, fun _ => ⟨s2, hs', hv', g2'⟩⟩)
      (fun e => by simp at e))) (fun hc => ?_)
    have hr : r = ZlibNg.Inflate.Z_BUF_ERROR := by simp at hc; exact hc.1
    have hao' : z'.avail_out = 0 := by simp at hc; exact hc.2
    refine GSat.bind (GSat.mono (gz_comp_spec G ψ Gr hψ W H' b ZlibNg.Inflate.Z_BLOCK s2 z' hs' hz' (Or.inl hv'))
      fun rc W3 H3 q => ?_)
    obtain ⟨s3, z3, hs3, hz3, fx3, hsz3, g3, -, -, -, -, hinv3, -, -, -, hr3, hok3, -, hpot3⟩ := q
    have hv3 := hinv3 hv'
    have g3' : GStep w h W3 H3 b [] := g2'.trans g3 ⟨s0, hs0⟩ ⟨s2, hs'⟩
    refine GSat.ite (fun _ => GSat.pure (spCond_sat (fun _ => ⟨fun e => by simp at e, fun _ => ⟨s3, hs3, hv3, g3'⟩⟩)
      (fun e => by simp at e))) (fun hc3 => ?_)
    have r0 : rc = 0 := by
      rcases hr3 with e3 | e3
      · exact e3
      · rw [e3] at hc3; simp at hc3
    obtain ⟨hsz3', hai3, hout3⟩ := hok3 r0
    have hai3 := hai3 (by decide)
    obtain ⟨hao3, hres3⟩ := hout3 hd2 (by decide)
    have hres3 := hres3 (by decide)
    have hS3 : s3.size = s2.size := ((hsz3 (by rw [hsz2]; exact hsz)).1)
    refine GSat.pure (spCond_sat (fun e => absurd (by rw [hx]) e) (fun _ => ⟨fun _ => ?_, fun e => by
      simp [hr] at e⟩))
    have hz3' : H3.streams s1.strm = some z3 := by rw [← hstrm2]; exact hz3
    refine ⟨⟨hx, s3, z3, hs3, hz3', hv3, g3', by rw [fx3.strm, hstrm2], by rw [fx3.direct, hd2],
      by rw [hS3, hsz2], hai3⟩, ?_⟩
    -- the measure
    have hsz2' : s2.size ≠ 0 := by rw [hsz2]; exact hsz
    have hS : s2.size.toNat = s1.size.toNat := by rw [hsz2]
    rw [spMu_eq ψ hs2 hz2', spMu_eq ψ hs3 hz3]
    simp only [hres3, hao3, ↓reduceIte, Nat.zero_add, Nat.add_zero]
    obtain ⟨sb, st, hsb, hds, -, -, -, hpot⟩ := pot_info hψ hv2 hs2 hsz2' hd2 hz2' ZlibNg.Inflate.Z_BLOCK
    obtain ⟨sb', st', hsb', hds', -, -, -, hpot'⟩ := pot_info hψ hv' hs' hsz2' hd2 hz' ZlibNg.Inflate.Z_BLOCK
    have hsbe : sb' = sb := by rw [hadv.2.2.2.2, hsb] at hsb'; cases hsb'; rfl
    subst hsbe
    have hai' : z'.avail_in.toNat = 0 := by
      have := UInt32.le_iff_toNat_le.mp hadv.1; rw [hai2] at this; simp at this; omega
    have hm' : ψ ZlibNg.Inflate.Z_BLOCK st' + z2.avail_out.toNat ≤ ψ ZlibNg.Inflate.Z_BLOCK st := by
      have := hmu sb' st st' hds hds'
      rw [hai2, hai', hao'] at this; simpa using this
    have hpH' : pot ψ ZlibNg.Inflate.Z_BLOCK s2.size.toNat H' s2.strm = 3 * ψ ZlibNg.Inflate.Z_BLOCK st' := by
      rw [hpot', hai', hao']; simp
    rw [hS] at hpot hpH'
    rw [hpot, hai2]
    simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.zero_add]
    have hS3' : s3.size ≠ 0 := by rw [hS3]; exact hsz2'
    by_cases hres : s2.reset = 0
    · have hp := hpot3 r0 (by decide) hsz2' hd2 hres
      rw [hS, hpH'] at hp
      simp only [hres, ↓reduceIte, Nat.zero_add]
      by_cases h0 : z2.avail_out = 0
      · simp only [h0, ↓reduceIte, Nat.sub_self, Nat.mul_zero, Nat.add_zero]; omega
      · simp only [h0, ↓reduceIte, Nat.add_zero]
        have : 0 < z2.avail_out.toNat := by
          rcases Nat.eq_zero_or_pos z2.avail_out.toNat with e0 | e0
          · exact absurd (UInt32.toNat_inj.mp (by simpa using e0)) h0
          · exact e0
        omega
    · simp only [hres, ↓reduceIte]
      obtain ⟨-, st3, -, -, hψ3, -, h30, hpot3'⟩ := pot_info hψ hv3 hs3 hS3' (by rw [fx3.direct, hd2]) (by rw [fx3.strm]; exact hz3)
        ZlibNg.Inflate.Z_BLOCK
      rw [fx3.strm, hS3, hS] at hpot3'
      rw [hpot3', hai3]
      rw [hS3, hsz2] at h30
      have e1 : s1.size.toNat - (if z3.avail_out = 0 then s1.size.toNat else z3.avail_out.toNat) ≤ s1.size.toNat :=
        Nat.sub_le _ _
      simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.zero_add] at e1 ⊢
      omega
  · obtain ⟨-, s2, z2, hs2, hz2, hv2, -, hstrm2, hd2, hsz2, hai2⟩ := hI
    have hz2' : H.streams s2.strm = some z2 := by rw [hstrm2]; exact hz2
    have hsz2' : s2.size ≠ 0 := by rw [hsz2]; exact hsz
    obtain ⟨-, st, -, -, hψb, -, h30, hpot⟩ := pot_info hψ hv2 hs2 hsz2' hd2 hz2' ZlibNg.Inflate.Z_BLOCK
    rw [hstrm2, hsz2] at hpot
    rw [hsz2] at h30
    show spMu ψ b s1.strm s1.size.toNat W H < 2 ^ 64
    rw [spMu_eq ψ hs2 hz2, hpot, hai2]
    have e1 : s1.size.toNat - (if z2.avail_out = 0 then s1.size.toNat else z2.avail_out.toNat) ≤ s1.size.toNat :=
      Nat.sub_le _ _
    have e2 : (if s2.reset = 0 then 0 else 2 ^ 52) ≤ 2 ^ 52 := by split <;> omega
    have e3 : (if z2.avail_out = 0 then 1 else 0) ≤ 1 := by split <;> omega
    simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.zero_add] at *
    omega

/-- The loop of `gzsetparams` and what follows it: `CallPost`. -/
theorem sp_after (G : DeflateGz) {ψ : Int32 → C.DeflateState → Nat} {Gr : Nat} (hψ : DeflatePsi ψ Gr)
    (hP : ParamsClause ψ Gr) {w : World} {h : Heap} {b : Nat} {s0 s1 : GzState} (hs0 : w.gz h b = some s0)
    (hsz : s1.size ≠ 0) {W : World} {H : Heap} (hI : SpInv w h b s1 (0, .go) W H) (level strategy : Int32) :
    GSat W H (spAfter (some b) (some s1.strm) level strategy) (CallPost w h b) := by
  unfold spAfter
  refine GSat.bind (GSat.mono (sp_loop G hψ hP hs0 hsz hI level strategy) fun lp W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2⟩ := q
  refine GSat.ite (fun _ => GSat.of_eq (rdG_app' hs2 _) ⟨hv2, g2⟩) (fun _ => ?_)
  refine GSat.ite (fun _ => GSat.pure ⟨hv2, g2⟩) (fun _ => ?_)
  exact spFin_spec hs0 hv2 hs2 g2 level strategy

/-- `gzsetparams` after the pending seek: `CallPost`. -/
theorem sp_rest (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState} (hs0 : w.gz h b = some s)
    {W : World} {H : Heap} {s1 : GzState} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1)
    (g : GStep w h W H b []) (hstrm : s1.strm = s.strm) (hd : s1.direct = 0) (level strategy : Int32) :
    GSat W H (spRest (some b) (some s.strm) level strategy) (CallPost w h b) := by
  obtain ⟨ψ, Gr, hG, hb, hdc, hP⟩ := G.2.2
  have hψ : DeflatePsi ψ Gr := ⟨hG, fun h s sb st f a b c => hb h s sb st f a b c, hdc⟩
  unfold spRest
  rw [← hstrm]
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hsz => ?_) (fun _ => spFin_spec hs0 hv hs g level strategy)
  have hsz' : s1.size ≠ 0 := by simpa using hsz
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  obtain ⟨z, hz⟩ := sh.strm
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_run hz _, ?_⟩)
  refine GSat.ite (fun _ => ?_) (fun hai => sp_after G hψ hP hs0 hsz'
    ⟨rfl, s1, z, hs, hz, hv, g, rfl, hd, rfl, by simpa using hai⟩ level strategy)
  refine GSat.bind (GSat.mono (comp_inv gz_comp_spec G hv hs ZlibNg.Inflate.Z_BLOCK) fun rc W2 H2 q => ?_)
  obtain ⟨s2, z2, hs2, hz2, hv2, g2, fx, hsz2, hr, hok⟩ := q
  have g2' : GStep w h W2 H2 b [] := g.trans g2 ⟨s, hs0⟩ ⟨s1, hs⟩
  refine GSat.ite (fun _ => GSat.of_eq (rdG_app' hs2 _) ⟨hv2, g2'⟩) (fun hc => ?_)
  have r0 : rc = 0 := by
    rcases hr with e3 | e3
    · exact e3
    · rw [e3] at hc; simp at hc
  exact sp_after G hψ hP hs0 hsz' ⟨rfl, s2, z2, hs2, hz2, hv2, g2', fx.strm, by rw [fx.direct, hd],
    hsz2 hsz', (hok r0).2 (by decide)⟩ level strategy

/-- **`gzsetparams`** on a write handle: `CallPost`. -/
theorem gzsetparams_spec (G : DeflateGz) {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvWS w h (some b)) (hs : w.gz h b = some s) (level strategy : Int32) :
    GSat w h (gzsetparams (some b) level strategy) (CallPost w h b) := by
  rw [gzsetparams_eq]
  refine GSat.ite (fun hc => by simp at hc) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun hc => ?_)
  have hd : s.direct = 0 := by simp at hc; exact hc.2
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun _ => GSat.pure (CallPost.refl hv _)) (fun _ => ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.ite (fun hk => ?_) (fun _ => sp_rest G hs hv hs (GStep.refl w h b []) rfl hd level strategy)
  refine GSat.bind (GSat.mono (gz_zero_spec gz_comp_spec G hv hs (by simpa using hk)) fun rz W2 H2 q => ?_)
  obtain ⟨s2, hs2, hv2, g2, zf, -, -⟩ := q
  exact GSat.ite (fun _ => GSat.of_eq (rdG_app' hs2 _) ⟨hv2, g2⟩)
    (fun _ => sp_rest G hs hv2 hs2 g2 zf.strm (by rw [zf.direct, hd]) level strategy)

end ZlibNgF.Proof.GzWrite
