import ZlibNgF.Proof.«gzread.c.skip»

/-!
# `gz_read` on a read handle (`ZlibNgF`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzMode
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzDecomp

/-! ## `gz_read` in parts (copied from the translation) -/

/-- The end of a trip of the loop of `gz_read` that delivered `n` bytes. -/
def readAdv (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  let len := s.len - n.toUInt64
  let buf ← lm (s.buf.add (Int.ofNat n.toNat))
  let got := s.got + n.toUInt64
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  return { s with buf := buf, len := len, got := got }

/-- The copy of `n` buffered bytes into the caller's buffer. -/
def readCopy (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  lm (Ptr.memcpy s.buf (← (← ldGz state).next.get) n.toNat)
  let nx ← lm ((← (← ldGz state).next.get).add (Int.ofNat n.toNat))
  wrG state fun st => { st with next := .val nx }
  wrG state fun st => { st with «have» := st.«have» - n }
  readAdv state s n

open ZlibNg.Inflate in
/-- A trip of the loop of `gz_read` after the room test, with the count `n`. -/
def readMain (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  if (← rdG state (·.«have»)) != 0 then
    if (← rdG state (·.«have»)) < n then
      readCopy state s (← rdG state (·.«have»))
    else readCopy state s n
  else if (← rdG state (·.eof)) != 0 && (← lm (rdZ (← strmOf state) (·.avail_in))) == 0 then
    wrG state fun st => { st with past := 1 }
    return { s with ctl := .brk }
  else if (← rdG state (·.how)) == LOOK || n < ((← rdG state (·.size)) <<< 1) then
    if (← gz_fetch state) == -1 then
      return { s with ctl := .ret }
    return s
  else if (← rdG state (·.how)) == ZlibNg.Gz.COPY then
    let (r, n') ← gz_load state s.buf n false
    if r == -1 then
      return { s with ctl := .ret }
    readAdv state s n'
  else
    lm (wrZ (← strmOf state) fun z => { z with avail_out := n })
    lm (wrZ (← strmOf state) fun z => { z with next_out := s.buf })
    if (← gz_decomp state) == -1 then
      return { s with ctl := .ret }
    let n ← rdG state (·.«have»)
    wrG state fun st => { st with «have» := 0 }
    readAdv state s n

open ZlibNg.Inflate in
/-- A trip of the loop of `gz_read` from the room test on. -/
def readRoom (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  let pos ← rdG state (·.pos)
  if pos > 0 && n.toUInt64 > (GZ_OFF_MAX - pos).toUInt64 then
    let n := (GZ_OFF_MAX - pos).toUInt64.toUInt32
    if n == 0 then
      gz_error state Z_DATA_ERROR (← gzLit "read position does not fit in z_off64_t")
      return { s with ctl := .brk }
    readMain state s n
  else readMain state s n

/-- The body of the loop of `gz_read`. -/
def readBody (state : GzPtr) (s : ReadLoop) : G ReadLoop :=
  if (4294967295 : UInt32).toUInt64 > s.len then readRoom state s s.len.toUInt32 else readRoom state s 4294967295

/-- The condition of the loop of `gz_read`. -/
def readCond (s : ReadLoop) : G (Bool × ReadLoop) := do
  if s.ctl != .go then return (false, s)
  return (s.len != 0, s)

/-- The loop of `gz_read` and what follows it. -/
def readLoop (state : GzPtr) (buf : BPtr) (len : UInt64) : G UInt64 := do
  let lp ← gdoWhile (readBody state) readCond ⟨buf, len, 0, .go⟩
  if lp.ctl == .ret then
    return 0
  return lp.got

theorem gz_read_eq (state : GzPtr) (buf : BPtr) (len : UInt64) : gz_read state buf len =
    (if len == 0 then pure 0 else do
      if (← rdG state (·.skip)) != 0 then
        if (← gz_skip state) == -1 then pure 0 else readLoop state buf len
      else readLoop state buf len) := by
  rfl

/-! ## Small facts -/

/-- The room test of `gz_read` (patch 0016): after it, `x.pos + n <= GZ_OFF_MAX`, and a count lowered by it reaches
`GZ_OFF_MAX` exactly. -/
theorem room_n (pos : Int64) (n : UInt32) (hlo : -GZ_OFF_MAX.toInt ≤ pos.toInt) (hhi : pos.toInt ≤ GZ_OFF_MAX.toInt) :
    ((decide (pos > 0) && decide (n.toUInt64 > (GZ_OFF_MAX - pos).toUInt64)) = true →
      pos.toInt + ((GZ_OFF_MAX - pos).toUInt64.toUInt32).toNat = GZ_OFF_MAX.toInt ∧
      ((GZ_OFF_MAX - pos).toUInt64.toUInt32).toNat < n.toNat) ∧
    (¬ (decide (pos > 0) && decide (n.toUInt64 > (GZ_OFF_MAX - pos).toUInt64)) = true →
      pos.toInt + n.toNat ≤ GZ_OFF_MAX.toInt) := by
  have hmx := gzmax
  have hn := n.toNat_lt
  have hsub : 0 < pos.toInt → (GZ_OFF_MAX - pos).toInt = GZ_OFF_MAX.toInt - pos.toInt := by
    intro hp
    rw [Int64.toInt_sub, Int.bmod_eq_of_le] <;> omega
  have hge : 0 < pos.toInt → (0 : Int64) ≤ GZ_OFF_MAX - pos := by
    intro hp; rw [Int64.le_iff_toInt_le, hsub hp]; simp; omega
  have hval : 0 < pos.toInt → (GZ_OFF_MAX - pos).toUInt64.toNat = (GZ_OFF_MAX.toInt - pos.toInt).toNat := by
    intro hp; rw [Int64.toNat_toUInt64_of_le (hge hp), ← Int64.toNat_toInt, hsub hp]
  have hpos : (pos > 0) ↔ 0 < pos.toInt := by
    rw [gt_iff_lt, Int64.lt_iff_toInt_lt]; simp
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    have hp := hpos.mp h1
    have h2' : (GZ_OFF_MAX - pos).toUInt64.toNat < n.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp h2; simpa using this
    have e32 : ((GZ_OFF_MAX - pos).toUInt64.toUInt32).toNat = (GZ_OFF_MAX.toInt - pos.toInt).toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega), hval hp]
    rw [hval hp] at h2'
    rw [e32]; omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
    by_cases hp : 0 < pos.toInt
    · have h2 := hc (hpos.mpr hp)
      have h2' : ¬ (GZ_OFF_MAX - pos).toUInt64.toNat < n.toNat := by
        intro e; exact h2 (UInt64.lt_iff_toNat_lt.mpr (by simpa using e))
      rw [hval hp] at h2'; omega
    · omega

/-- A step whose write range lies inside a larger one of the same block writes inside the larger one. -/
theorem GStep.cover {w W : World} {h H : Heap} {b c oo n o L : Nat} (g : GStep w h W H b [(.ref (.heap c) oo, n)])
    (h1 : o ≤ oo) (h2 : oo + n ≤ o + L) : GStep w h W H b [(.ref (.heap c) o, L)] := by
  obtain ⟨⟨⟨f1, f2⟩, cc, gz⟩, ow, t⟩ := g
  refine ⟨⟨⟨frame_wcover f1 (fun c' j hw w' hw' off e => ?_), f2⟩, cc, gz⟩, ow, t⟩
  simp only [List.mem_singleton] at hw'
  subst hw'
  cases e
  rcases hw _ (List.mem_singleton_self _) o rfl with e | e <;> omega

/-- The potential sees the heap only through its streams. -/
theorem Phi_strm {W : World} {H H' : Heap} (s : GzState) (e : H'.streams = H.streams) : Phi W H' s = Phi W H s := by
  unfold Phi dD AtEnd; rw [e]

/-- Moving `x.pos` by `k` with the output kept lowers the potential by twice the blocks of 16 bytes in `k`. -/
theorem Phi_pos {W : World} {H : Heap} {s : GzState} {p : Int64} {k : Nat} (hp : p.toInt = s.pos.toInt + k)
    (hph : s.pos.toInt + k + s.«have».toNat ≤ GZ_OFF_MAX.toInt) :
    Phi W H { s with pos := p } + 2 * (k / 16) ≤ Phi W H s := by
  have hx : xq { s with pos := p } + k = xq s := by unfold xq; simp only; rw [hp]; omega
  have hd : dD { s with pos := p } W H = dD s W H := rfl
  have h2 : ph2 { s with pos := p } = ph2 s := rfl
  have ha : AtEnd H { s with pos := p } = AtEnd H s := rfl
  unfold Phi; rw [hd, h2, ha]
  omega

/-! ## The end of a trip: `buf`, `len`, `got` and `x.pos` -/

/-- **The end of a trip** that delivered `k` bytes: the caller's pointer and `x.pos` move by `k`. -/
theorem readAdv_spec {W : World} {H : Heap} {b cb o j : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (hsk : s.skip = 0) (st : ReadLoop) (hbk : st.buf = .ref (.heap cb) (o + j)) (k : UInt32)
    {d : Array UInt8} (hd : H.bytes cb = some d) (hfit : o + j + k.toNat ≤ d.size)
    (hpk : s.pos.toInt + k.toNat + s.«have».toNat ≤ GZ_OFF_MAX.toInt)
    (hlk : s.how = LOOK → s.direct ≠ 0 → s.pos.toInt + k.toNat + s.«have».toNat ≤ 0) :
    GSat W H (readAdv (some b) st k) (fun st1 W1 H1 =>
      st1 = { st with buf := .ref (.heap cb) (o + j + k.toNat), len := st.len - k.toUInt64, got := st.got + k.toUInt64 } ∧
      H1 = H ∧ W1 = { W with gzs := upd W.gzs b (some { s with pos := Int64.ofInt (s.pos.toInt + k.toNat) }) } ∧
      GzInvR W1 H1 (some b) ∧ GStep W H W1 H1 b []) := by
  obtain ⟨sh, -⟩ := inv_of hs hv.1
  have R := sh.read (modeOf hs hv.2.1)
  have P := sh.pos
  have hmx := gzmax
  unfold readAdv
  rw [hbk]
  refine GSat.bind (GSat.lm ⟨_, H, addH hd (off := o + j) k.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hb1 : -(2 ^ 63 : Int) ≤ s.pos.toInt + (k.toNat : Int) ∧ s.pos.toInt + (k.toNat : Int) < 2 ^ 63 := by
    have := P.3; constructor <;> omega
  refine GSat.bind (GSat.lm ⟨_, H, chkI64_ok hb1.1 hb1.2 H, ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hs _) (GSat.pure ?_))
  have e2 := toInt_ofInt' hb1.1 hb1.2
  obtain ⟨hvF, gF⟩ := invR_hp hv hs (s' := { s with pos := Int64.ofInt (s.pos.toInt + k.toNat) }) rfl
    (by show _ ≤ (Int64.ofInt _).toInt; rw [e2]; have := P.3; omega)
    (by show (Int64.ofInt _).toInt + _ ≤ _; rw [e2, hsk]; simp; omega)
    (hout_self R) (fun e => absurd hsk e)
    (by show (Int64.ofInt _).toInt + _ ≤ _; rw [e2]; omega)
    (fun h1 h2 => by show (Int64.ofInt _).toInt + _ ≤ _; rw [e2]; have := hlk h1 h2; omega)
  exact ⟨rfl, rfl, rfl, hvF, gF⟩

/-! ## The copy of buffered output -/

/-- **The copy** of `m` bytes, `1 <= m <= x.have`, from `x.next` to `buf + j` with `j + m` inside the caller's `L`
bytes, and the end of the trip: the potential is kept. -/
theorem readCopy_spec {W : World} {H : Heap} {b cb o j L : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (hsk : s.skip = 0) (st : ReadLoop) (hbk : st.buf = .ref (.heap cb) (o + j)) (m : UInt32)
    (hm1 : 1 ≤ m.toNat) (hmh : m.toNat ≤ s.«have».toNat) (hjm : j + m.toNat ≤ L)
    {dc : Array UInt8} (hdc : H.bytes cb = some dc) (hfit : o + L ≤ dc.size) (hno : cb ∉ GzOwned W H (some b)) :
    GSat W H (readCopy (some b) st m) (fun st1 W1 H1 =>
      st1 = { st with buf := .ref (.heap cb) (o + j + m.toNat), len := st.len - m.toUInt64, got := st.got + m.toUInt64 } ∧
      GzInvR W1 H1 (some b) ∧ GStep W H W1 H1 b [(.ref (.heap cb) o, L)] ∧ W1.fs = W.fs ∧
      (LookIdle W H (some b) → LookIdle W1 H1 (some b)) ∧
      ∃ s', W1.gz H1 b = some s' ∧ s'.«have».toNat = s.«have».toNat - m.toNat ∧ s'.skip = s.skip ∧
        Phi W1 H1 s' = Phi W H s) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have R := sh.read (modeOf hs hv.2.1)
  have P := sh.pos
  have hmx := gzmax
  have hh : s.«have» ≠ 0 := fun e => by rw [e] at hmh; simp at hmh; omega
  have hsz : s.size ≠ 0 := fun e => hh (R.nobuf e)
  obtain ⟨c, base, z, hb, -, -, hhv, -, -⟩ := R.bufs hsz
  obtain ⟨p, hp, k1, hpk, hlo, hhi⟩ := hhv.resolve_left hh
  obtain ⟨d, hd, hds⟩ := hb.fits
  have hcO : c ∈ GzOwned W H (some b) := ownL_owned hs c (by simp [ownL, hsz, hb.buffers, blkOf])
  have hcb : c ≠ cb := fun e => hno (e ▸ hcO)
  have hbc : b ≠ cb := fun e => hno (by subst e; simp [GzOwned, hs])
  unfold readCopy
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨p, H, by show Ival.get s.next H = _; rw [hp]; rfl, ?_⟩)
  rw [hbk, hpk]
  obtain ⟨H1, em, x⟩ := memcpy_hbuf (od := o + j) (os := base + k1) (n := m.toNat) hdc (rs := .heap c) (src := d) hd
    (fun e => hcb (by cases e; rfl)) (by omega) (by omega)
  refine GSat.bind (GSat.lm ⟨(), H1, em, ?_⟩)
  have hv1 : GzInvR W H1 (some b) := invR_caller hv hno x
  have hs1 : W.gz H1 b = some s := by rw [x.gz hbc]; exact hs
  have g1 : GStep W H W H1 b [(.ref (.heap cb) o, L)] := gstep_caller x hno hbc (by omega) (by omega)
  have hd1 : H1.bytes c = some d := by rw [x.bytes_ne hcb]; exact hd
  have hstr : H1.streams = H.streams := by obtain ⟨t, et, -⟩ := x; rw [et]
  obtain ⟨dc1, hdc1, hsz1⟩ := x.size hdc
  refine GSat.bind (GSat.of_eq (ldGz_app hs1) ?_)
  refine GSat.bind (GSat.lm ⟨_, H1, by show Ival.get s.next H1 = _; rw [hp, hpk]; rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H1, addH hd1 (off := base + k1) m.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
  let sn : GzState := { s with next := .val (.ref (.heap c) (base + k1 + m.toNat)) }
  have hsn := gz_upd_same hs1 sn
  refine GSat.bind (GSat.of_eq (wrG_app hsn _) ?_)
  let s2 : GzState := { s with next := .val (.ref (.heap c) (base + k1 + m.toNat)), «have» := s.«have» - m }
  have hhm : (s.«have» - m).toNat = s.«have».toNat - m.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hmh)]
  have ew : ({ ({ W with gzs := upd W.gzs b (some sn) } : World) with
      gzs := upd (upd W.gzs b (some sn)) b (some ({ sn with «have» := sn.«have» - m } : GzState)) } : World) =
      { W with gzs := upd W.gzs b (some s2) } := by
    simp only [InflateInv.upd_upd]; rfl
  rw [ew]
  have hs2 : ({ W with gzs := upd W.gzs b (some s2) } : World).gz H1 b = some s2 := gz_upd_same hs1 s2
  have hph := R.pos_have
  have hph2 : s.pos.toInt + ((s.«have» - m).toNat : Int) + m.toNat ≤ GZ_OFF_MAX.toInt := by rw [hhm]; omega
  have hlk2 : s.how = LOOK → s.direct ≠ 0 → s.pos.toInt + ((s.«have» - m).toNat : Int) + m.toNat ≤ 0 :=
    fun h1 h2 => by rw [hhm]; have := R.look_pos h1 h2; omega
  obtain ⟨hv2, g2⟩ := invR_hp hv1 hs1 (s' := s2) rfl P.3
    (by show s.pos.toInt + s.skip.toInt ≤ _; rw [hsk]; simp; omega)
    (Or.inr ⟨hsz, fun c' base' hb' => by
      have e1 := hb'.buffers; rw [hb.buffers] at e1; cases e1
      refine ⟨_, rfl, k1 + m.toNat, by rw [Nat.add_assoc], by omega, ?_⟩
      show k1 + m.toNat + (s.«have» - m).toNat ≤ _; rw [hhm]; omega⟩)
    (fun e => absurd hsk e) (by show s.pos.toInt + ((s.«have» - m).toNat : Int) ≤ _; omega)
    (fun h1 h2 => by show s.pos.toInt + ((s.«have» - m).toNat : Int) ≤ 0; have := hlk2 h1 h2; omega)
  refine GSat.mono (readAdv_spec hv2 hs2 hsk st hbk m hdc1 (by omega)
    (by show s.pos.toInt + m.toNat + ((s.«have» - m).toNat : Int) ≤ _; omega)
    (fun h1 h2 => by show s.pos.toInt + m.toNat + ((s.«have» - m).toNat : Int) ≤ 0; have := hlk2 h1 h2; omega))
    fun st1 W1 H2 q => ?_
  obtain ⟨rfl, rfl, rfl, hv3, g3⟩ := q
  have hb1 : -(2 ^ 63 : Int) ≤ s.pos.toInt + (m.toNat : Int) ∧ s.pos.toInt + (m.toNat : Int) < 2 ^ 63 := by
    have := P.3; constructor <;> omega
  have e2 := toInt_ofInt' hb1.1 hb1.2
  let s3 : GzState := { s2 with pos := Int64.ofInt (s2.pos.toInt + m.toNat) }
  have hs3 := gz_upd_same hs2 s3
  refine ⟨rfl, hv3, (g1.trans (GStep.widen g2 _) ⟨s, hs⟩ ⟨s, hs1⟩).trans (GStep.widen g3 _) ⟨s, hs⟩ ⟨s2, hs2⟩, rfl,
    fun hi => idle_same hi hs hs3 rfl rfl rfl (by rw [hstr]), s3, hs3, hhm, rfl, ?_⟩
  rw [Phi_strm s3 hstr]
  refine Phi_consume rfl rfl ?_
  show (Int64.ofInt (s.pos.toInt + m.toNat)).toInt + ((s.«have» - m).toNat : Int) = _
  rw [e2, hhm]; omega

end ZlibNgF.Proof.GzMode
