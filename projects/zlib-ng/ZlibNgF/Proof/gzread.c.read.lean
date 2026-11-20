import ZlibNgF.Proof.«gzread.c.skip»

/-!
# `gz_read` on a read handle (`ZlibNgF`)

`gz_read` (`gzread.c:308-388`, patch 0016) does a pending skip first (`gz_skip`), then loops while the caller still
asks for bytes: it caps the count `n` at `UINT_MAX` and at the room `GZ_OFF_MAX - x.pos` (failing at `x.pos ==
GZ_OFF_MAX`), then copies buffered output, stops at the end of the input (`past = 1`), fetches output (`gz_fetch`) when
looking for a header or asked for less than `2 * size` bytes, or reads (`COPY`) or decompresses (`GZIP`) directly into
the caller's buffer. Every byte it delivers lies in `[buf, buf + len)`, and `x.pos + n <= GZ_OFF_MAX` keeps `x.pos`
from overflowing.

**Termination.** The measure is `smu`, the potential `Phi` of the read handle plus 1 while output is buffered (as for
`gz_skip`). A copy keeps `Phi`; one that leaves output behind delivered all the caller asked for (the room cannot be the
smaller count, since `x.pos + x.have <= GZ_OFF_MAX`), so the loop ends. A fetch lowers the measure (`FetchMu`). A direct
read of `k >= 1` bytes lowers the input still to come by `k`, and of no byte reaches the end of the input. A direct
decompression ends a member (`GZIP` to `LOOK`), fills the caller's range of at least `2 * size >= 16` bytes (one block
of 16 bytes of room less), or reaches the end of the input.
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

/-! ## The direct decompression into the caller's buffer -/

/-- **A trip that decompresses directly into the caller's buffer** (`GZIP`, at least `2 * size >= 16` bytes asked
for): the end of a member lowers the phase by 2; otherwise the output range is full (`n >= 16` bytes, one block of 16
bytes less room) or the input has ended. -/
theorem readDecompC_spec {w : World} {h : Heap} {b cb o L : Nat} (hL : L < 2 ^ 64) (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (hfit0 : o + L ≤ data.size) {st : ReadLoop} {W : World} {H : Heap} (hI : RInv w h b cb o L st W H)
    {s1 : GzState} (hs1 : W.gz H b = some s1) (h0 : s1.«have» = 0) (hk0 : s1.skip = 0) (hne : ¬ AtEnd H s1)
    (hgz : s1.how = GZIP) (n : UInt32) (hn2 : 2 * s1.size.toNat ≤ n.toNat) (hnl : n.toNat ≤ st.len.toNat)
    (hpn : s1.pos.toInt + n.toNat ≤ GZ_OFF_MAX.toInt) :
    GSat W H (readDecompC (some b) st n) (RTrip w h b cb o L (smu b W H)) := by
  obtain ⟨hgo, hl0, hbk, hgl, hv, -, g, hf, hi⟩ := hI
  obtain ⟨dc, hdc, hdcs, hno⟩ := caller_blk g hcbn hno0 hd0
  obtain ⟨sh, -⟩ := inv_of hs1 hv.1
  have R := sh.read (modeOf hs1 hv.2.1)
  have hmx := gzmax
  have hwl := sh.want_lo
  have hsz1 : s1.size ≠ 0 := fun e => by have := R.look e; rw [hgz] at this; exact absurd this (by decide)
  obtain ⟨c, base, z, hB, -, hz, -, hai, -, -⟩ := R.bufs hsz1
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hμ := smu_of hs1
  have hdir0 : s1.direct = 0 := R.gzip_direct hgz
  obtain ⟨buf0, len0, got0, ctl0⟩ := st
  dsimp only at hgo hl0 hbk hgl hnl ⊢
  subst hbk
  unfold readDecompC
  let z1 : ZStream := { z with avail_out := n }
  let z2 : ZStream := { z with avail_out := n, next_out := .ref (.heap cb) (o + got0.toNat) }
  let H3 : Heap := { H with streams := upd H.streams s1.strm (some z2) }
  refine GSat.bind (GSat.of_eq (strmOf_app hs1) ?_)
  refine GSat.bind (GSat.lm ⟨(), { H with streams := upd H.streams s1.strm (some z1) }, wrZ_app hz _, ?_⟩)
  refine GSat.bind (GSat.of_eq (strmOf_app (show W.gz { H with streams := upd H.streams s1.strm (some z1) } b = some s1
    from hs1)) ?_)
  refine GSat.bind (GSat.lm ⟨(), H3, (by rw [wrZ_app (z := z1) (by simp)]; simp [InflateInv.upd_upd, z1, z2, H3]), ?_⟩)
  have hz3 : H3.streams s1.strm = some z2 := by simp [H3]
  have hv3 : GzInvR W H3 (some b) := invR_strm (z' := z2) hv hs1 hsz1 hz rfl (fun c' base' hB' => by
    have e1 := hB'.buffers; rw [hB.buffers] at e1; cases e1; exact hai) (fun e => absurd (hgz.symm.trans e) (by decide))
  have hs3 : W.gz H3 b = some s1 := hs1
  have g3 : GStep W H W H3 b [] := gstep_strm hs1 z2 hz rfl
  have hcbH : cb < H.nextBlk := live_lt hv.2.2.2.1.1 ⟨dc, hdc⟩
  have hno3 : cb ∉ GzOwned W H3 (some b) := fun m => hno (g3.own _ m hcbH)
  have hao : z2.avail_out.toNat = n.toNat := rfl
  have hao0 : z2.avail_out ≠ 0 := fun e => by
    have := congrArg UInt32.toNat e; rw [hao] at this; simp at this; omega
  have ht : OutTgt W H3 b s1 cb (o + got0.toNat) z2.avail_out.toNat := Or.inr ⟨hno3, dc, hdc, by rw [hao]; omega⟩
  refine GSat.bind (GSat.mono (gz_decomp_spec hv3 hs3 h0 hsz1 hgz hz3 hao0 rfl ht) fun r W1 H1 q => ?_)
  obtain ⟨hr1, gD, fD, s', hs', hv0, hshape, herr, hok⟩ := q
  have gD' : GStep W H3 W1 H1 b [(.ref (.heap cb) o, L)] := gD.cover (by omega) (by rw [hao]; omega)
  have gAll : GStep w h W1 H1 b [(.ref (.heap cb) o, L)] :=
    (g.trans (GStep.widen g3 _) hw0 ⟨s1, hs1⟩).trans gD' hw0 ⟨s1, hs3⟩
  have hf' : FsRd w.fs W1.fs := hf.trans fD
  have hk' : s'.skip = 0 := by rw [hshape]; exact hk0
  have hdir' : s'.direct = 0 := by rw [hshape]; exact hdir0
  have hp' : s'.pos = s1.pos := by rw [hshape]
  have hfd' : s'.fd = s1.fd := by rw [hshape]
  have hst' : s'.strm = s1.strm := by rw [hshape]
  apply GSat.ite
  · intro e
    have he : r = -1 := by simpa using e
    obtain ⟨h0', -, -⟩ := herr he
    have hv1 : GzInvR W1 H1 (some b) := by
      rw [have0_self h0', DeflateReset.upd_self W1.gzs b s' (gzs_of hs')] at hv0; exact hv0
    exact GSat.pure (trip_stop (st := ⟨_, len0, got0, ctl0⟩) hgl .ret (by decide) hv1 gAll hf'
      (fun _ => idle_mk hs' fun _ _ _ hd => absurd hdir' hd))
  · intro e
    have hr0 : r = 0 := hr1.resolve_left (by simpa using e)
    obtain ⟨z', hz1', hle, hhv, -, -, -, hhow', -, -, hDle, -, hao0'⟩ := hok hr0
    refine GSat.bind (GSat.of_eq (rdG_app' hs' _) ?_)
    refine GSat.bind (GSat.of_eq (wrG_app hs' _) ?_)
    let s4 : GzState := { s' with «have» := 0 }
    have hs4 := gz_upd_same hs' s4
    obtain ⟨dc1, hdc1, hdcs1, -⟩ := caller_blk gAll hcbn hno0 hd0
    have hk : s'.«have».toNat ≤ n.toNat := by rw [hhv, hao]; exact Nat.sub_le _ _
    have g4 : GStep W1 H1 { W1 with gzs := upd W1.gzs b (some s4) } H1 b [] := gstep_st hs' W1.fs rfl rfl rfl rfl
    refine (readAdv_spec hv0 hs4 hk' _ rfl s'.«have» hdc1 (by omega)
      (by show s'.pos.toInt + _ + ((0 : UInt32).toNat : Int) ≤ _; rw [hp']; simp; omega)
      (fun _ hd => absurd hdir' hd)).mono fun st1 W2 H2 q => ?_
    obtain ⟨rfl, rfl, rfl, hv2, g2⟩ := q
    let s5 : GzState := { s4 with pos := Int64.ofInt (s4.pos.toInt + s'.«have».toNat) }
    have hs5 := gz_upd_same hs4 s5
    refine trip_adv hgo hgl hL s'.«have» (by show _ ≤ len0.toNat; omega) hv2 ⟨s5, hs5, hk'⟩
      ((gAll.trans (GStep.widen g4 _) hw0 ⟨s', hs'⟩).trans (GStep.widen g2 _) hw0 ⟨s4, hs4⟩) hf'
      (fun _ => idle_mk hs5 fun _ _ _ hd => absurd hdir' hd) (fun _ => ?_)
    rw [smu_of hs5, hμ]
    have h05 : s5.«have» = 0 := rfl
    simp only [h05, h0, ite_true, Nat.add_zero]
    have hb1 : -(2 ^ 63 : Int) ≤ s1.pos.toInt + (s'.«have».toNat : Int) ∧
        s1.pos.toInt + (s'.«have».toNat : Int) < 2 ^ 63 := by
      have := sh.pos.3; constructor <;> omega
    suffices key : ∀ W' : World, W'.fs = W1.fs → Phi W' H2 s5 < Phi W H s1 from key _ rfl
    intro W' hW'
    have hP5 : Phi W' H2 s5 + 2 * (s'.«have».toNat / 16) ≤ Phi W' H2 s4 :=
      Phi_pos (by show (Int64.ofInt (s'.pos.toInt + _)).toInt = s'.pos.toInt + _; rw [hp']; exact toInt_ofInt' hb1.1 hb1.2)
        (by show s'.pos.toInt + _ + ((0 : UInt32).toNat : Int) ≤ _; rw [hp']; simp; omega)
    have hD4 : dD s4 W' H2 = dD s1 W1 H2 := by
      rw [dD_congr W' H2 (s' := s4) hfd' hst']; unfold dD; rw [hW']
    have hD3 : dD s1 W H3 = dD s1 W H := by rw [dD_of hz3, dD_of hz]
    rw [hD3] at hDle
    have hx : xq s4 = xq s1 := by
      unfold xq; rw [show s4.pos = s1.pos from hp', show s4.«have» = (0 : UInt32) from rfl, h0]
    have hp1 : ph2 s1 = 4 := ph2_gz hgz
    rw [Phi_ne hne, hp1]
    rcases hhow' with e1 | e1
    · have hp4 : ph2 s4 = 2 := ph2_look0 e1 hdir'
      have := Phi_le' (Nat.le_trans (Nat.le_of_eq hD4) hDle) (Nat.le_of_eq hp4)
      rw [hx] at this
      omega
    · have hp4 : ph2 s4 = 4 := ph2_gz (e1.trans hgz)
      rcases hao0' e1 with e2 | ⟨e2, e3⟩
      · have hk2 : s'.«have».toNat = n.toNat := by rw [hhv, hao, e2]; rfl
        have := Phi_le' (Nat.le_trans (Nat.le_of_eq hD4) hDle) (Nat.le_of_eq hp4)
        rw [hx] at this
        omega
      · have hat : AtEnd H2 s4 := ⟨e2, z', by rw [show s4.strm = s1.strm from hst']; exact hz1', e3⟩
        have := Phi_end' hat (Nat.le_trans (Nat.le_of_eq hD4) hDle) (Nat.le_of_eq hp4)
        rw [hx] at this
        omega

/-! ## One trip of the loop -/

/-- **A trip of the loop of `gz_read` after the room test**, with `1 <= n <= len` and `x.pos + n <= GZ_OFF_MAX`; `n`
is below `len` only when it is `UINT_MAX` or reaches `GZ_OFF_MAX`. -/
theorem readMain_spec {w : World} {h : Heap} {b cb o L : Nat} (hL : L < 2 ^ 64) (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (hfit0 : o + L ≤ data.size) {st : ReadLoop} {W : World} {H : Heap} (hI : RInv w h b cb o L st W H)
    {s1 : GzState} (hs1 : W.gz H b = some s1) (n : UInt32) (hn1 : 1 ≤ n.toNat) (hnl : n.toNat ≤ st.len.toNat)
    (hpn : s1.pos.toInt + n.toNat ≤ GZ_OFF_MAX.toInt)
    (hnx : n.toNat < st.len.toNat → n.toNat = 4294967295 ∨ s1.pos.toInt + n.toNat = GZ_OFF_MAX.toInt) :
    GSat W H (readMain (some b) st n) (RTrip w h b cb o L (smu b W H)) := by
  have hI0 := hI
  obtain ⟨hgo, hl0, hbk, hgl, hv, ⟨s0', hs0', hsk⟩, g, hf, hi⟩ := hI
  rw [hs1] at hs0'; cases hs0'
  obtain ⟨dc, hdc, hdcs, hno⟩ := caller_blk g hcbn hno0 hd0
  obtain ⟨sh, -⟩ := inv_of hs1 hv.1
  have R := sh.read (modeOf hs1 hv.2.1)
  have hmx := gzmax
  have hμ := smu_of hs1
  unfold readMain
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  apply GSat.ite
  · intro hh
    have hh' : s1.«have» ≠ 0 := by simpa using hh
    have hh'' : s1.«have».toNat ≠ 0 := fun e => hh' (UInt32.toNat_inj.mp (by simpa using e))
    have hk0 : s1.skip = 0 := hsk.resolve_right fun e => hh' e.1
    have hph := R.pos_have
    have deliver : ∀ m : UInt32, 1 ≤ m.toNat → m.toNat ≤ s1.«have».toNat → m.toNat ≤ n.toNat →
        (m.toNat < s1.«have».toNat → m.toNat = n.toNat) →
        GSat W H (readCopy (some b) st m) (RTrip w h b cb o L (smu b W H)) := by
      intro m hm1 hmh hmn hmx'
      refine (readCopy_spec hv hs1 hk0 st hbk m hm1 hmh (L := L) (by omega) hdc (by omega) hno).mono
        fun st1 W1 H1 q => ?_
      obtain ⟨rfl, hv1, g1, hfs1, hi1, s', hs', hh2, hk2, hP⟩ := q
      refine trip_adv hgo hgl hL m (by omega) hv1 ⟨s', hs', by rw [hk2]; exact hk0⟩ (g.trans g1 hw0 ⟨s1, hs1⟩)
        (by rw [hfs1]; exact hf) (fun hi0 => hi1 (hi hi0)) (fun hlt => ?_)
      have hz : s'.«have».toNat = 0 := by
        rw [hh2]
        rcases Nat.lt_or_ge m.toNat s1.«have».toNat with hc | hc
        · have e1 := hmx' hc
          rcases hnx (by omega) with e2 | e2
          · have := s1.«have».toNat_lt; omega
          · omega
        · omega
      have hz' : s'.«have» = 0 := UInt32.toNat_inj.mp (by simpa using hz)
      rw [smu_of hs', hμ, hP]
      simp [hz', hh']
    refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
    apply GSat.ite
    · intro hlt
      have hlt' : s1.«have».toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      exact deliver _ (by omega) (Nat.le_refl _) (by omega) (fun e => absurd e (Nat.lt_irrefl _))
    · intro hlt
      have hge : n.toNat ≤ s1.«have».toNat := by
        have := mt UInt32.lt_iff_toNat_lt.mpr hlt; omega
      exact deliver n hn1 hge (Nat.le_refl _) (fun _ => rfl)
  · intro hh
    have h0 : s1.«have» = 0 := by simpa using hh
    obtain ⟨z, hz⟩ := sh.strm
    refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
    refine GSat.bind (GSat.of_eq (strmOf_app hs1) ?_)
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
    apply GSat.ite
    · intro _
      obtain ⟨hvP, gP⟩ := invR_past hv hs1 1
      refine GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure ?_))
      exact trip_stop (st := st) hgl .brk (by decide) hvP (g.trans (GStep.widen gP _) hw0 ⟨s1, hs1⟩) hf
        (fun hi0 => idle_upd (hi hi0) hs1 _ rfl rfl rfl)
    · intro hc
      have hne : ¬ AtEnd H s1 := by
        rintro ⟨e1, z', hz', e2⟩
        rw [hz] at hz'; cases hz'
        exact hc (by simp [e1, e2])
      have hk0 : s1.skip = 0 := hsk.resolve_right fun e => hne e.2
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
      apply GSat.ite
      · intro _
        refine GSat.bind (GSat.mono (gz_fetch_specM hv hs1 h0) fun r W1 H1 q => ?_)
        obtain ⟨⟨⟨hr1, g1, hf1, s', hm', -, hk', -, hinv, -⟩, hid⟩, hmu, -⟩ := q
        have hv1 := hinv hk0
        have g' := g.trans (GStep.widen g1 _) hw0 ⟨s1, hs1⟩
        apply GSat.ite
        · intro _
          exact GSat.pure (trip_stop (st := st) hgl .ret (by decide) hv1 g' (hf.trans hf1) (fun hi0 => hid (hi hi0)))
        · intro e
          have hr : r = 0 := hr1.resolve_left (by simpa using e)
          refine GSat.pure ⟨⟨by omega, hv1, g', hf.trans hf1, fun hi0 => hid (hi hi0)⟩, fun _ _ =>
            ⟨⟨hgo, hl0, hbk, hgl, hv1, ⟨s', hm'.1, Or.inl (by rw [hk']; exact hk0)⟩, g', hf.trans hf1,
              fun hi0 => hid (hi hi0)⟩, ?_⟩⟩
          rw [smu_of hm'.1, hμ]
          have hd := hmu hr hne s' hm'.1
          by_cases hh2 : s'.«have» = 0
          · have := hd.2 hh2; simp [hh2, h0]; omega
          · have := hd.1 hh2; simp [hh2, h0]; omega
      · intro hc2
        have hc2' : ¬ (s1.how = LOOK ∨ n < s1.size <<< 1) := by simpa using hc2
        have hlk : s1.how ≠ LOOK := fun e => hc2' (Or.inl e)
        have hns : ¬ n < s1.size <<< 1 := fun e => hc2' (Or.inr e)
        have hsz1 : s1.size ≠ 0 := fun e => hlk (R.look e)
        obtain ⟨c, base, z0, hB, -⟩ := R.bufs hsz1
        have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
        have hwh := sh.want_hi
        have h2s := shl1_toNat s1.size (by omega)
        have hn2 : 2 * s1.size.toNat ≤ n.toNat := by
          have := mt UInt32.lt_iff_toNat_lt.mpr hns; omega
        refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
        apply GSat.ite
        · intro hcp
          exact readLoadC_spec hL hw0 hcbn hno0 hd0 hfit0 hI0 hs1 h0 hk0 hne (by simpa using hcp) n hn1 hnl hpn
        · intro hcp
          have hcp' : s1.how ≠ ZlibNg.Gz.COPY := by simpa using hcp
          have hgz : s1.how = GZIP := by
            rcases R.how with e | e | e
            · exact absurd e hlk
            · exact absurd e hcp'
            · exact e
          exact readDecompC_spec hL hw0 hcbn hno0 hd0 hfit0 hI0 hs1 h0 hk0 hne hgz n hn2 hnl hpn

/-- **A trip of the loop of `gz_read` from the room test on**, with `1 <= n <= len` and `n` below `len` only when it
is `UINT_MAX`. -/
theorem readRoom_spec {w : World} {h : Heap} {b cb o L : Nat} (hL : L < 2 ^ 64) (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (hfit0 : o + L ≤ data.size) {st : ReadLoop} {W : World} {H : Heap} (hI : RInv w h b cb o L st W H)
    (n : UInt32) (hn1 : 1 ≤ n.toNat) (hnl : n.toNat ≤ st.len.toNat)
    (hnx0 : n.toNat < st.len.toNat → n.toNat = 4294967295) :
    GSat W H (readRoom (some b) st n) (RTrip w h b cb o L (smu b W H)) := by
  have hI0 := hI
  obtain ⟨hgo, hl0, hbk, hgl, hv, ⟨s1, hs1, hsk⟩, g, hf, hi⟩ := hI
  obtain ⟨sh, -⟩ := inv_of hs1 hv.1
  have P := sh.pos
  have hmx := gzmax
  unfold readRoom
  refine GSat.bind (GSat.of_eq (rdG_app' hs1 _) ?_)
  obtain ⟨hA, hB⟩ := room_n s1.pos n P.3 (by have := P.1; have := P.2; omega)
  apply GSat.ite
  · intro hc
    obtain ⟨e1, e2⟩ := hA hc
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.mono (errlit_strm hv hs1 ZlibNg.Inflate.Z_DATA_ERROR _ 14 lit_readpos (by decide))
        fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => ?_))
      obtain ⟨s2, hs2, herr, hv2, hfs2, g2, hstr⟩ := q3
      exact GSat.pure (trip_stop (st := st) hgl .brk (by decide) hv2 (g.trans (GStep.widen g2 _) hw0 ⟨s1, hs1⟩)
        (by rw [hfs2]; exact hf) (fun hi0 => idle_same (hi hi0) hs1 hs2 ((congrArg GzState.how herr.1).trans rfl)
          ((congrArg GzState.direct herr.1).trans rfl) ((congrArg GzState.strm herr.1).trans rfl) (by rw [hstr])))
    · intro hz
      have hx0 : (GZ_OFF_MAX - s1.pos).toUInt64.toUInt32 ≠ 0 := by simpa using hz
      have hx1 : ((GZ_OFF_MAX - s1.pos).toUInt64.toUInt32).toNat ≠ 0 := fun e =>
        hx0 (UInt32.toNat_inj.mp (by simpa using e))
      exact readMain_spec hL hw0 hcbn hno0 hd0 hfit0 hI0 hs1 _ (by omega) (by omega) (Int.le_of_eq e1)
        (fun _ => Or.inr e1)
  · intro hc
    exact readMain_spec hL hw0 hcbn hno0 hd0 hfit0 hI0 hs1 n hn1 hnl (hB hc) (fun hlt => Or.inl (hnx0 hlt))

/-- **One trip of the loop of `gz_read`** and its condition. -/
theorem readBody_spec {w : World} {h : Heap} {b cb o L : Nat} (hL : L < 2 ^ 64) (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (hfit0 : o + L ≤ data.size) {st : ReadLoop} {W : World} {H : Heap} (hI : RInv w h b cb o L st W H) :
    GSat W H (readBody (some b) st) (fun st1 W1 H1 => GSat W1 H1 (readCond st1) (fun cs W2 H2 =>
      (cs.1 = true → RInv w h b cb o L cs.2 W2 H2 ∧ smu b W2 H2 < smu b W H) ∧
      (cs.1 = false → RQ w h b cb o L cs.2 W2 H2))) := by
  have hl0 := hI.2.1
  have hl0' : st.len.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
  unfold readBody
  apply GSat.ite
  · intro hc
    have hc' : st.len.toNat < 4294967295 := by have := UInt64.lt_iff_toNat_lt.mp hc; simpa using this
    have e : st.len.toUInt32.toNat = st.len.toNat := by rw [UInt64.toNat_toUInt32]; omega
    exact (readRoom_spec hL hw0 hcbn hno0 hd0 hfit0 hI _ (by omega) (by omega) (fun _ => by omega)).mono
      fun _ _ _ q => readCond_spec q
  · intro hc
    have hc' : 4294967295 ≤ st.len.toNat := by
      have := mt UInt64.lt_iff_toNat_lt.mpr hc; simp at this; omega
    exact (readRoom_spec hL hw0 hcbn hno0 hd0 hfit0 hI 4294967295 (by decide) (by simpa using hc')
      (fun _ => rfl)).mono fun _ _ _ q => readCond_spec q

/-! ## `gz_read` -/

/-- **The loop of `gz_read`** into the caller's `len` bytes at offset `o` of block `cb`, from a read handle with no
skip pending unless at the end of the input with no output. -/
theorem readLoop_spec {w : World} {h : Heap} {b cb o : Nat} (hw0 : ∃ s0, w.gz h b = some s0)
    (hcbn : cb < h.nextBlk) (hno0 : cb ∉ GzOwned w h (some b)) {data : Array UInt8} (hd0 : h.bytes cb = some data)
    (len : UInt64) (hfit0 : o + len.toNat ≤ data.size) (hl0 : len ≠ 0) {W : World} {H : Heap} {s : GzState}
    (hv : GzInvR W H (some b)) (hs : W.gz H b = some s) (hsk : s.skip = 0 ∨ (s.«have» = 0 ∧ AtEnd H s))
    (g : GStep w h W H b [(.ref (.heap cb) o, len.toNat)]) (hf : FsRd w.fs W.fs)
    (hi : LookIdle w h (some b) → LookIdle W H (some b)) :
    GSat W H (readLoop (some b) (.ref (.heap cb) o) len) (fun r W' H' => r.toNat ≤ len.toNat ∧
      GzInvR W' H' (some b) ∧ GStep w h W' H' b [(.ref (.heap cb) o, len.toNat)] ∧ FsRd w.fs W'.fs ∧
      (LookIdle w h (some b) → LookIdle W' H' (some b))) := by
  have hI : RInv w h b cb o len.toNat ⟨.ref (.heap cb) o, len, 0, .go⟩ W H :=
    ⟨rfl, hl0, by simp, by simp, hv, ⟨s, hs, hsk⟩, g, hf, hi⟩
  have hfuel : smu b W H < fuel := by
    rw [smu_of hs]
    have := Phi_lt (W := W) (fun fd => rdLeft_lt hv.2.2 fd) H s
    split <;> omega
  unfold readLoop
  refine GSat.bind (GSat.mono (gsat_gdoWhile (RInv w h b cb o len.toNat) (fun _ W H => smu b W H)
    (RQ w h b cb o len.toNat) (fun _ _ _ hI' => readBody_spec len.toNat_lt hw0 hcbn hno0 hd0 hfit0 hI') hI hfuel)
    fun lp W' H' q => ?_)
  obtain ⟨hgot, hv', g', hf', hi'⟩ := q
  apply GSat.ite
  · intro _; exact GSat.pure ⟨by simp, hv', g', hf', hi'⟩
  · intro _; exact GSat.pure ⟨hgot, hv', g', hf', hi'⟩

/-- **`gz_read`** on a read handle, with `LookIdle` kept. -/
theorem gz_read_specI {w : World} {h : Heap} {b : Nat} {buf : BPtr} {len : UInt64} (hv : GzInvR w h (some b))
    (hout : GzOut w h (some b) buf len.toNat) :
    GSat w h (gz_read (some b) buf len) (fun r W H => ReadPost w h b buf len r W H ∧
      (LookIdle w h (some b) → LookIdle W H (some b))) := by
  obtain ⟨b0, s, e0, hs, -, -⟩ := hv.1
  cases e0
  rw [gz_read_eq]
  apply GSat.ite
  · intro _; exact GSat.pure ⟨⟨by simp, hv, GStep.refl _ _ _ _, FsRd.refl _⟩, id⟩
  intro hl
  have hl' : len ≠ 0 := by simpa using hl
  have hl'' : len.toNat ≠ 0 := fun e => hl' (UInt64.toNat_inj.mp (by simpa using e))
  obtain ⟨⟨cb, o, data, rfl, hd, hfit⟩, hout'⟩ : WriteSlice h buf len.toNat ∧ OutsideGz w h (some b) buf :=
    hout.resolve_left hl''
  have hno : cb ∉ GzOwned w h (some b) := fun m => hout' cb m o rfl
  have hcbn : cb < h.nextBlk := live_lt hv.2.2.2.1.1 ⟨data, hd⟩
  have loop : ∀ (W : World) (H : Heap) (s1 : GzState), GzInvR W H (some b) → W.gz H b = some s1 →
      (s1.skip = 0 ∨ (s1.«have» = 0 ∧ AtEnd H s1)) → GStep w h W H b [] → FsRd w.fs W.fs →
      (LookIdle w h (some b) → LookIdle W H (some b)) →
      GSat W H (readLoop (some b) (.ref (.heap cb) o) len) (fun r W H =>
        ReadPost w h b (.ref (.heap cb) o) len r W H ∧ (LookIdle w h (some b) → LookIdle W H (some b))) := by
    intro W H s1 hvW hs1 hsk gW hfW hiW
    exact (readLoop_spec ⟨s, hs⟩ hcbn hno hd len hfit hl' hvW hs1 hsk (GStep.widen gW _) hfW hiW).mono
      fun r W' H' q => ⟨⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩, q.2.2.2.2⟩
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro hk
    have hk' : s.skip ≠ 0 := by simpa using hk
    refine GSat.bind (GSat.mono (gz_skip_specI (mid_of hv hs) hk') fun r W H q => ?_)
    obtain ⟨⟨hr, hvW, gW, hfW, s', hs', -, -, hend⟩, hiW⟩ := q
    apply GSat.ite
    · intro _; exact GSat.pure ⟨⟨by simp, hvW, GStep.widen gW _, hfW⟩, hiW⟩
    · intro hr1
      have hr0 : r = 0 := hr.resolve_left (by simpa using hr1)
      exact loop W H s' hvW hs' (hend hr0) gW hfW hiW
  · intro hk
    exact loop w h s hv hs (Or.inl (by simpa using hk)) (GStep.refl _ _ _ _) (FsRd.refl _) id

/-- **`gz_read`** on a read handle. -/
theorem gz_read_spec : GzReadSpec :=
  fun _ _ _ _ _ hv hout => (gz_read_specI hv hout).mono fun _ _ _ q => q.1

/-- **`gz_read` keeps `LookIdle`.** -/
theorem gz_read_idle : GzReadIdle := by
  intro w h b buf len r W H hv hi hout e
  obtain ⟨r2, W2, H2, e2, q⟩ := (gz_read_specI hv hout).run
  obtain ⟨-, rfl, rfl⟩ := gdet e2 e
  exact q.2 hi

end ZlibNgF.Proof.GzMode
