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

/-- The direct read of a transparent file into the caller's buffer. -/
def readLoadC (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  let (r, n') ← gz_load state s.buf n false
  if r == -1 then
    return { s with ctl := .ret }
  readAdv state s n'

open ZlibNg.Inflate in
/-- The direct decompression into the caller's buffer. -/
def readDecompC (state : GzPtr) (s : ReadLoop) (n : UInt32) : G ReadLoop := do
  lm (wrZ (← strmOf state) fun z => { z with avail_out := n })
  lm (wrZ (← strmOf state) fun z => { z with next_out := s.buf })
  if (← gz_decomp state) == -1 then
    return { s with ctl := .ret }
  let n ← rdG state (·.«have»)
  wrG state fun st => { st with «have» := 0 }
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
    readLoadC state s n
  else
    readDecompC state s n

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

/-! ## `gz_load` into the caller's buffer -/

/-- A block of the caller is neither the state's block, its `path`, nor the block of its stream's state. -/
theorem caller_facts {W : World} {H : Heap} {b cb : Nat} {s : GzState} (hs : W.gz H b = some s)
    (hno : cb ∉ GzOwned W H (some b)) : b ≠ cb ∧ cb ∉ blkOf s.path ∧ cb ∉ stBlk H s := by
  refine ⟨fun e => hno (by subst e; simp [GzOwned, hs]), fun m => hno ?_, fun m => hno ?_⟩
  · simp only [GzOwned, hs, List.mem_append]; left; left; left; right; unfold blkOf at m; split at m <;> simp_all
  · simp only [GzOwned, hs, List.mem_append]; right; unfold stBlk at m; exact m

/-- **`gz_load(state, buf, len, &n)`** with a local count (`gz_read`'s direct read of a transparent file into the
caller's buffer): an error (`-1`, `gz_error` with `Z_ERRNO`), or `0` with at most `len` bytes read into
`[p, p + len)` of the caller's block, out of the read measure, and `eof` set when fewer than `len` came. -/
theorem gz_load_caller {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) {cb p : Nat} {a : Array UInt8} (ha : h.bytes cb = some a) (len : UInt32)
    (hp : p + len.toNat ≤ a.size) (hno : cb ∉ GzOwned w h (some b)) :
    GSat w h (gz_load (some b) (.ref (.heap cb) p) len false) (fun r W H =>
      (r.1 = -1 ∧ ∃ s', W.gz H b = some s' ∧ ErrOf s Z_ERRNO s' ∧ GzInvR W H (some b) ∧
        GStep w h W H b [(.ref (.heap cb) p, len.toNat)] ∧ FsRd w.fs W.fs ∧ H.streams = h.streams) ∨
      (r.1 = 0 ∧ r.2.toNat ≤ len.toNat ∧ ∃ (fs' : Fs) (e : Int32), FsRd w.fs fs' ∧
        rdLeft fs' s.fd + r.2.toNat ≤ rdLeft w.fs s.fd ∧ (r.2.toNat < len.toNat → e = 1) ∧
        W = { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } ∧ HBuf h H cb p (p + len.toNat))) := by
  obtain ⟨hbc, hpath, hst⟩ := caller_facts hs hno
  rw [gz_load_false]
  refine GSat.bind (GSat.pure ?_)
  refine GSat.bind (GSat.mono (loadLoop_budget hs ha len hp hbc) fun lp W1 H1 q => ?_)
  obtain ⟨hlp, hex, fs', hfs, hleft, rfl, x⟩ := q
  have hv1 : GzInvR { w with fs := fs' } H1 (some b) := invR_hbuf hv hs x hbc hpath hst hfs
  have hsH : w.gz H1 b = some s := by rw [x.gz hbc]; exact hs
  have hs1 : ({ w with fs := fs' } : World).gz H1 b = some s := hsH
  have g1 : GStep w h { w with fs := fs' } H1 b [(.ref (.heap cb) p, len.toNat)] :=
    (gstep_caller x hno hbc (Nat.le_refl _) (Nat.le_refl _)).trans (GStep.widen (gstep_fs hsH fs') _) ⟨s, hs⟩ ⟨s, hsH⟩
  have hstr : H1.streams = h.streams := by obtain ⟨t, rfl, -⟩ := x; rfl
  unfold loadTail
  apply GSat.ite
  · intro _
    obtain ⟨pm, am, ez, hcs, hmk⟩ := zstrerror_spec { w with fs := fs' } H1
    refine GSat.bind (GSat.of_eq ez ?_)
    refine GSat.bind (GSat.mono (GSat.and (gz_error_inv (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk)
      (gz_error_strm (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk)) fun _ W H2 q => ?_)
    obtain ⟨⟨s', hsW, herr, hvW, -, hfsW, hstep⟩, hstr2⟩ := q
    refine GSat.pure (Or.inl ⟨rfl, s', hsW, herr, hvW, ?_, by rw [hfsW]; exact hfs, hstr2.trans hstr⟩)
    exact (g1.trans (GStep.widen (gstep_lit hs1 am) _) ⟨s, hs⟩ ⟨s, hs1⟩).trans (GStep.widen hstep _) ⟨s, hs⟩ ⟨s, hs1⟩
  · intro hneg
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure ?_))
      exact Or.inr ⟨rfl, hlp, fs', 1, hfs, hleft, fun _ => rfl, rfl, x⟩
    · intro hn0
      refine GSat.pure (Or.inr ⟨rfl, hlp, fs', s.eof, hfs, hleft, fun hlt => ?_, ?_, x⟩)
      · exfalso
        rcases hex with hle | hle
        · have a1 : lp.ret.toInt ≤ 0 := by have := Int64.le_iff_toInt_le.mp hle; simpa using this
          have a2 : ¬ lp.ret.toInt < 0 := fun e => hneg (Int64.lt_iff_toInt_lt.mpr (by simpa using e))
          have a3 : lp.ret ≠ 0 := by simpa using hn0
          exact a3 (Int64.toInt_inj.mp (by simp; omega))
        · exact absurd hlt (by simp only; omega)
      · show { w with fs := fs' } = _
        rw [show ({ s with eof := s.eof } : GzState) = s from rfl, DeflateReset.upd_self w.gzs b s (gzs_of hs)]

/-! ## The invariant of the loop -/

/-- The invariant of the loop of `gz_read` at the start of a trip, for the caller's `L` bytes at offset `o` of block
`cb`: `got` bytes delivered at `buf - got`, `len` still asked for, a read handle with no skip pending unless at the end
of the input with no output, a step of the call writing only the caller's range, the file system only read. -/
def RInv (w : World) (h : Heap) (b cb o L : Nat) (st : ReadLoop) (W : World) (H : Heap) : Prop :=
  st.ctl = .go ∧ st.len ≠ 0 ∧ st.buf = .ref (.heap cb) (o + st.got.toNat) ∧ st.got.toNat + st.len.toNat = L ∧
  GzInvR W H (some b) ∧ (∃ s1, W.gz H b = some s1 ∧ (s1.skip = 0 ∨ (s1.«have» = 0 ∧ AtEnd H s1))) ∧
  GStep w h W H b [(.ref (.heap cb) o, L)] ∧ FsRd w.fs W.fs ∧ (LookIdle w h (some b) → LookIdle W H (some b))

/-- The exit of the loop of `gz_read`. -/
def RQ (w : World) (h : Heap) (b cb o L : Nat) (st : ReadLoop) (W : World) (H : Heap) : Prop :=
  st.got.toNat ≤ L ∧ GzInvR W H (some b) ∧ GStep w h W H b [(.ref (.heap cb) o, L)] ∧ FsRd w.fs W.fs ∧
    (LookIdle w h (some b) → LookIdle W H (some b))

/-- What a trip of the loop of `gz_read` leaves: an exit, and the invariant with a smaller measure when the loop goes
on. -/
def RTrip (w : World) (h : Heap) (b cb o L μ0 : Nat) (st : ReadLoop) (W : World) (H : Heap) : Prop :=
  RQ w h b cb o L st W H ∧ (st.ctl = .go → st.len ≠ 0 → RInv w h b cb o L st W H ∧ smu b W H < μ0)

theorem readCond_spec {w : World} {h : Heap} {b cb o L μ0 : Nat} {st : ReadLoop} {W : World} {H : Heap}
    (q : RTrip w h b cb o L μ0 st W H) :
    GSat W H (readCond st) (fun cs W2 H2 => (cs.1 = true → RInv w h b cb o L cs.2 W2 H2 ∧ smu b W2 H2 < μ0) ∧
      (cs.1 = false → RQ w h b cb o L cs.2 W2 H2)) := by
  unfold readCond
  apply GSat.ite
  · intro _; exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => q.1⟩
  · intro hc
    have hgo : st.ctl = .go := by simpa using hc
    exact GSat.pure ⟨fun e => q.2 hgo (by simpa using e), fun _ => q.1⟩

/-- A trip that stops the loop. -/
theorem trip_stop {w : World} {h : Heap} {b cb o L μ0 : Nat} {st : ReadLoop} (hgl : st.got.toNat + st.len.toNat = L)
    (c : Ctl) (hc : c ≠ .go) {W : World} {H : Heap} (hv : GzInvR W H (some b))
    (g : GStep w h W H b [(.ref (.heap cb) o, L)]) (hf : FsRd w.fs W.fs)
    (hi : LookIdle w h (some b) → LookIdle W H (some b)) : RTrip w h b cb o L μ0 { st with ctl := c } W H :=
  ⟨⟨by show st.got.toNat ≤ L; omega, hv, g, hf, hi⟩, fun e => absurd e hc⟩

/-- A trip that delivered `k` bytes. -/
theorem trip_adv {w : World} {h : Heap} {b cb o L μ0 : Nat} {st : ReadLoop} (hgo : st.ctl = .go)
    (hgl : st.got.toNat + st.len.toNat = L) (hL : L < 2 ^ 64) (k : UInt32) (hk : k.toNat ≤ st.len.toNat)
    {W : World} {H : Heap} (hv : GzInvR W H (some b)) (hsk : ∃ s1, W.gz H b = some s1 ∧ s1.skip = 0)
    (g : GStep w h W H b [(.ref (.heap cb) o, L)]) (hf : FsRd w.fs W.fs)
    (hi : LookIdle w h (some b) → LookIdle W H (some b)) (hmu : k.toNat < st.len.toNat → smu b W H < μ0) :
    RTrip w h b cb o L μ0
      { st with buf := .ref (.heap cb) (o + st.got.toNat + k.toNat), len := st.len - k.toUInt64, got := st.got + k.toUInt64 }
      W H := by
  have hk64 : k.toUInt64.toNat = k.toNat := UInt32.toNat_toUInt64 k
  have hsub : (st.len - k.toUInt64).toNat = st.len.toNat - k.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk64]; exact hk)), hk64]
  have hadd : (st.got + k.toUInt64).toNat = st.got.toNat + k.toNat := by
    rw [UInt64.toNat_add, hk64]; omega
  obtain ⟨s1, hs1, hk1⟩ := hsk
  refine ⟨⟨by show (st.got + k.toUInt64).toNat ≤ L; omega, hv, g, hf, hi⟩, fun _ hl => ?_⟩
  have hl' : (st.len - k.toUInt64).toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  refine ⟨⟨hgo, hl, ?_, ?_, hv, ⟨s1, hs1, Or.inl hk1⟩, g, hf, hi⟩, hmu (by omega)⟩
  · show Ptr.ref _ (o + st.got.toNat + k.toNat) = Ptr.ref _ (o + (st.got + k.toUInt64).toNat)
    rw [hadd, Nat.add_assoc]
  · show (st.got + k.toUInt64).toNat + (st.len - k.toUInt64).toNat = L
    omega

/-! ## The direct read of a transparent file -/

/-- **A trip that reads a transparent file directly into the caller's buffer** (`COPY`, at least `2 * size` bytes
asked for): `k` bytes read lower the read measure by `k`; no byte read sets `eof` at the end of the input. -/
theorem readLoadC_spec {w : World} {h : Heap} {b cb o L : Nat} (hL : L < 2 ^ 64) (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (hfit0 : o + L ≤ data.size) {st : ReadLoop} {W : World} {H : Heap} (hI : RInv w h b cb o L st W H)
    {s1 : GzState} (hs1 : W.gz H b = some s1) (h0 : s1.«have» = 0) (hk0 : s1.skip = 0) (hne : ¬ AtEnd H s1)
    (hcp : s1.how = ZlibNg.Gz.COPY) (n : UInt32) (hn1 : 1 ≤ n.toNat) (hnl : n.toNat ≤ st.len.toNat)
    (hpn : s1.pos.toInt + n.toNat ≤ GZ_OFF_MAX.toInt) :
    GSat W H (readLoadC (some b) st n) (RTrip w h b cb o L (smu b W H)) := by
  obtain ⟨hgo, hl0, hbk, hgl, hv, -, g, hf, hi⟩ := hI
  obtain ⟨dc, hdc, hdcs, hno⟩ := caller_blk g hcbn hno0 hd0
  obtain ⟨sh, -⟩ := inv_of hs1 hv.1
  have R := sh.read (modeOf hs1 hv.2.1)
  have hmx := gzmax
  obtain ⟨z, hz⟩ := sh.strm
  have hz0 : z.avail_in = 0 := R.copy_in hcp z hz
  have hz0' : z.avail_in.toNat = 0 := by rw [hz0]; rfl
  have hμ := smu_of hs1
  obtain ⟨hbc, hpath, hst⟩ := caller_facts hs1 hno
  obtain ⟨buf0, len0, got0, ctl0⟩ := st
  dsimp only at hgo hl0 hbk hgl hnl ⊢
  subst hbk
  unfold readLoadC
  refine GSat.bind (GSat.mono (gz_load_caller hv hs1 hdc n (p := o + got0.toNat) (by omega) hno) fun r W1 H1 q => ?_)
  obtain ⟨r1, r2⟩ := r
  dsimp only
  rcases q with ⟨hr1, s', hs', herr, hv1, gL, hfL, -⟩ | ⟨hr1, hk, fs', e, hfs, hbl, hke, rfl, x⟩
  · simp only at hr1
    subst hr1
    refine GSat.ite (fun _ => GSat.pure ?_) (fun hc => absurd rfl hc)
    exact trip_stop (st := ⟨_, len0, got0, ctl0⟩) hgl .ret (by decide) hv1 (g.trans (gL.cover (by omega) (by omega)) hw0 ⟨s1, hs1⟩) (hf.trans hfL)
      (fun _ => idle_mk hs' fun _ _ e => absurd (hcp.symm.trans ((congrArg GzState.how herr.1).symm.trans e)) (by decide))
  · simp only at hr1
    subst hr1
    replace hk : r2.toNat ≤ n.toNat := hk
    replace hbl : rdLeft fs' s1.fd + r2.toNat ≤ rdLeft W.fs s1.fd := hbl
    replace hke : r2.toNat < n.toNat → e = 1 := hke
    refine GSat.ite (fun hc => absurd hc (by decide)) (fun _ => ?_)
    let s2 : GzState := { s1 with eof := e }
    have hs2 := gzX_upd hs1 x hbc fs' s2
    have hsW : W.gz H1 b = some s1 := by rw [x.gz hbc]; exact hs1
    have hsA : ({ W with fs := fs' } : World).gz H1 b = some s1 := hsW
    have hvA : GzInvR { W with fs := fs' } H1 (some b) := invR_hbuf hv hs1 x hbc hpath hst hfs
    obtain ⟨sh1, hn1⟩ := inv_of hsA hvA.1
    have sh1' := shape_msg sh1 e s1.past s1.err s1.msg ⟨sh1.msg.1, sh1.msg.2⟩
    have hvE : GzInvR { W with fs := fs', gzs := upd W.gzs b (some s2) } H1 (some b) :=
      (keeps_store hsA (HLess.refl H1) (fun _ e => e) sh1' hn1 rfl rfl).1 hvA
    have gA : GStep W H { W with fs := fs', gzs := upd W.gzs b (some s2) } H1 b [(.ref (.heap cb) o, L)] :=
      (gstep_caller x hno hbc (by omega) (by omega)).trans (GStep.widen (gstep_st (s' := s2) hsW fs' rfl rfl rfl rfl) _)
        ⟨s1, hs1⟩ ⟨s1, hsW⟩
    obtain ⟨dc1, hdc1, hdcs1⟩ := x.size hdc
    have hstr : H1.streams = H.streams := by obtain ⟨t, rfl, -⟩ := x; rfl
    have hz1 : H1.streams s2.strm = some z := by rw [hstr]; exact hz
    refine (readAdv_spec hvE hs2 hk0 _ rfl r2 hdc1 (by omega)
      (by show s1.pos.toInt + _ + ((s1.«have»).toNat : Int) ≤ _; rw [h0]; simp; omega)
      (fun e' => absurd (hcp.symm.trans e') (by decide))).mono fun st1 W2 H2 q => ?_
    obtain ⟨rfl, rfl, rfl, hv2, g2⟩ := q
    let s3 : GzState := { s2 with pos := Int64.ofInt (s2.pos.toInt + r2.toNat) }
    have hs3 := gz_upd_same hs2 s3
    refine trip_adv hgo hgl hL r2 (by show r2.toNat ≤ len0.toNat; omega) hv2 ⟨s3, hs3, hk0⟩
      ((g.trans gA hw0 ⟨s1, hs1⟩).trans (GStep.widen g2 _) hw0 ⟨s2, hs2⟩) (hf.trans hfs)
      (fun _ => idle_mk hs3 fun _ _ e' => absurd (hcp.symm.trans e') (by decide)) (fun _ => ?_)
    rw [smu_of hs3, hμ]
    have h03 : s3.«have» = 0 := h0
    simp only [h03, h0, ite_true, Nat.add_zero]
    have hb1 : -(2 ^ 63 : Int) ≤ s1.pos.toInt + (r2.toNat : Int) ∧ s1.pos.toInt + (r2.toNat : Int) < 2 ^ 63 := by
      have := sh.pos.3; constructor <;> omega
    suffices key : ∀ W' : World, W'.fs = fs' → Phi W' H2 s3 < Phi W H s1 from key _ rfl
    intro W' hW'
    have hP3 : Phi W' H2 s3 + 2 * (r2.toNat / 16) ≤ Phi W' H2 s2 :=
      Phi_pos (toInt_ofInt' hb1.1 hb1.2) (by show s1.pos.toInt + _ + ((s1.«have»).toNat : Int) ≤ _; rw [h0]; simp; omega)
    have hD2 : dD s2 W' H2 = rdLeft fs' s1.fd + z.avail_in.toNat := by rw [dD_of hz1, hW']
    have hD1 : dD s1 W H = rdLeft W.fs s1.fd + z.avail_in.toNat := dD_of hz
    have hp2 : ph2 s2 = 0 := ph2_copy hcp
    have hp1 : ph2 s1 = 0 := ph2_copy hcp
    have hx : xq s2 = xq s1 := rfl
    rw [Phi_ne hne, hD1, hp1]
    by_cases hk1 : r2.toNat = 0
    · have hat : AtEnd H2 s2 := ⟨by show e ≠ 0; rw [hke (by omega)]; decide, z, hz1, hz0⟩
      have := Phi_end' hat (Nat.le_of_eq hD2) (Nat.le_of_eq hp2)
      rw [hx] at this
      omega
    · have := Phi_le' (Nat.le_of_eq hD2) (Nat.le_of_eq hp2)
      rw [hx] at this
      omega

end ZlibNgF.Proof.GzMode
