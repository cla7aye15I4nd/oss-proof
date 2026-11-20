import ZlibNgF.Proof.«gzwrite.c.zero»

/-!
# `gz_write` (`ZlibNgF`)

Helpers: a caller's buffer stays readable and outside the file across a step of the file (`callerBuf_step`);
`memcpy` from a caller's buffer into the buffer block of the file changes only that block (`memcpy_hbuf`).
`gz_write_eq` splits `gz_write` into the buffer setup, the pending seek and `wMid` (the position bound of patch
0017 and the two paths). The buffered path: one round (`wb_main`, `wb_body`: the input stays inside the first `size`
bytes of `in`, the position grows by the bytes copied, the caller's range moves on) and the loop (`wb_loop`, measure
`2 len + [avail_in ≠ 0]`). `gz_comp` enters through `GzCompSpec` and `DeflateGz`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzWrite
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode
open ZlibNgF.Proof.GzWriteNeeds

/-- A caller's buffer stays readable and outside the file's blocks across a step of the file. -/
theorem callerBuf_step {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) (hfr : FreshBlocks h)
    {p : BPtr} {n : Nat} (hr : ReadSlice h p n) (ho : OutsideGz w h (some b) p) :
    ReadSlice H p n ∧ OutsideGz W H (some b) p := by
  obtain ⟨r, off, d, ep, hd, hle⟩ := hr
  obtain ⟨⟨⟨fr, fd⟩, fc, -⟩, own, -⟩ := g
  have hget : Space.get H r = some d := by
    cases r with
    | heap c =>
      have hcl : c < h.nextBlk := live_lt hfr ⟨d, hd⟩
      have hno : c ∉ GzOwned w h (some b) := fun m => ho c m off ep
      have e2 : ({ H with consts := h.consts } : Heap).bytes c = h.bytes c := frame_bytes_eq fr hcl hno
      exact e2.trans hd
    | const k => exact fc k d hd
    | str k => exact hd
  refine ⟨⟨r, off, d, ep, hget, hle⟩, fun c hc off' e => ?_⟩
  rw [ep] at e; cases e
  by_cases hlt : c < h.nextBlk
  · exact ho c (own c hc hlt) off ep
  · exact hlt (live_lt hfr ⟨d, hd⟩)

/-- `memcpy` from another object into heap block `c`: only the range of block `c` changes. -/
theorem memcpy_hbuf {H : Heap} {c od : Nat} {rs : BRef} {os n : Nat} {a src : Array UInt8}
    (ha : H.bytes c = some a) (hs : Space.get H rs = some src) (hne : rs ≠ .heap c) (h1 : od + n ≤ a.size)
    (h2 : os + n ≤ src.size) :
    ∃ H', Ptr.memcpy (Ptr.ref (BRef.heap c) od : BPtr) (Ptr.ref rs os) n H = .ok ((), H') ∧ HBuf H H' c od (od + n) := by
  refine ⟨_, ZlibNgF.Proof.InflateDict.memcpy_heap ha hs hne h1 h2, ?_⟩
  refine ⟨upd H.bytes c (some (ZlibNgF.Proof.InflateDict.copyFold src od os (List.range' 0 n) a)), rfl, ?_, ?_, ?_⟩
  · intro c' hc'; exact upd_ne _ _ _ _ hc'
  · intro e; rw [ha] at e; cases e
  intro a' ha'
  rw [ha] at ha'; cases ha'
  exact ⟨_, upd_same _ _ _, ZlibNgF.Proof.InflateDict.copyFold_size _ _ _ _ _, fun j hj =>
    ZlibNgF.Proof.InflateDict.copyFold_get _ _ _ _ _ j (fun i hi => ChunkMem.mem_range'_bound hi hj)⟩

/-! ## The parts of `gz_write` (copied from the translation) -/

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the buffered path after `next_in` is set. -/
def wbMain (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  let e ← lm ((← lm (rdZ strm (·.next_in))).add (Int.ofNat (← lm (rdZ strm (·.avail_in))).toNat))
  let d ← lm (Ptr.diff e (← (← ldGz state).«in».get))
  let hv : UInt32 := d.toUInt64.toUInt32
  let mut copy : UInt32 := (← rdG state (·.size)) - hv
  if copy.toUInt64 > s.len then
    copy := s.len.toUInt32
  lm (Ptr.memcpy (← lm ((← (← ldGz state).«in».get).add (Int.ofNat hv.toNat))) s.buf copy.toNat)
  lm (wrZ strm fun z => { z with avail_in := z.avail_in + copy })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + copy.toNat))
  wrG state fun st => { st with pos := np }
  let buf ← lm (s.buf.add (Int.ofNat copy.toNat))
  let len := s.len - copy.toUInt64
  if len != 0 then
    if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
      return { s with buf := buf, len := len, ctl := .ret }
  return { s with buf := buf, len := len }

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the buffered path. -/
def wbBody (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  wbMain state strm s

/-- The condition of both loops of `gz_write`. -/
def wCond (s : WriteLoop) : G (Bool × WriteLoop) := do
  if s.ctl != .go then return (false, s)
  return (s.len != 0, s)

open ZlibNg.Inflate (rdZ wrZ) in
/-- The body of the loop of the direct path. -/
def wdBody (state : GzPtr) (strm : StreamPtr) (s : WriteLoop) : G WriteLoop := do
  let mut n : UInt32 := 0xFFFFFFFF
  if n.toUInt64 > s.len then
    n := s.len.toUInt32
  lm (wrZ strm fun z => { z with avail_in := n })
  let np ← lm (chkI64 ((← rdG state (·.pos)).toInt + n.toNat))
  wrG state fun st => { st with pos := np }
  if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
    lm (wrZ strm fun z => { z with avail_in := 0 })
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
    return { s with ctl := .ret }
  return { s with len := s.len - n.toUInt64 }

open ZlibNg.Inflate (rdZ wrZ) in
/-- `gz_write` after the buffers are made and the pending seek is done. -/
def wMid (state : GzPtr) (buf : BPtr) (len put : UInt64) : G UInt64 := do
  let room ← lm (chkI64 (GZ_OFF_MAX.toInt - (← rdG state (·.pos)).toInt))
  if len > room.toUInt64 then
    gz_error state ZlibNg.Inflate.Z_DATA_ERROR (← (gzLit "write position does not fit in z_off64_t"))
    return 0
  let strm ← strmOf state
  if len < (← rdG state (·.size)).toUInt64 then
    let lp ← gdoWhile (wbBody state strm) wCond ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
  else
    if (← lm (rdZ strm (·.avail_in))) != 0 then
      if (← gz_comp state ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
        return 0
    lm (wrZ strm fun z => { z with next_in := buf })
    let lp ← gdoWhile (wdBody state strm) wCond ⟨buf, len, .go⟩
    if lp.ctl == .ret then
      return 0
    let i ← (← ldGz state).«in».get
    lm (wrZ strm fun z => { z with next_in := i })
  return put

theorem gz_write_eq (state : GzPtr) (buf : BPtr) (len : UInt64) : gz_write state buf len = (do
    if len == 0 then
      return 0
    if (← rdG state (·.size)) == 0 then
      if (← gz_write_init state) == -1 then
        return 0
    if (← rdG state (·.skip)) != 0 then
      if (← gz_zero state) == -1 then
        return 0
    wMid state buf len len) := rfl

/-! ## Pointer steps -/

theorem padd_ok {h : Heap} {r : BRef} {off : Nat} {a : Array UInt8} (hg : Space.get h r = some a) (k : Nat)
    (hk : off + k ≤ a.size) : Ptr.add (Ptr.ref r off : BPtr) (Int.ofNat k) h = .ok (Ptr.ref r (off + k), h) := by
  have e : ((off : Int) + (k : Int)).toNat = off + k := by omega
  simp only [Ptr.add, hg, Int.ofNat_eq_natCast]
  split
  · rw [e]
  · next hc => exact absurd ⟨by omega, by omega, by omega⟩ hc

theorem pdiff_ok {h : Heap} {c o1 o2 : Nat} {a : Array UInt8} (ha : h.bytes c = some a) (h1 : o1 ≤ a.size)
    (h2 : o2 ≤ o1) (h3 : o1 < o2 + 2 ^ 62) :
    Ptr.diff (Ptr.ref (BRef.heap c) o1 : BPtr) (Ptr.ref (BRef.heap c) o2) h = .ok (Int64.ofInt ((o1 : Int) - o2), h) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  simp only [Ptr.diff, hg]
  split
  · split
    · split
      · rfl
      · next hc => exact absurd ⟨by omega, by omega⟩ hc
    · next hc => exact absurd ⟨h1, by omega⟩ hc
  · next hc => exact absurd trivial hc

theorem diff_u32 (k : Nat) (hk : k < 2 ^ 31) : (Int64.ofInt (k : Int)).toUInt64.toUInt32.toNat = k := by
  have e : (Int64.ofInt (k : Int)).toInt = k := Int64.toInt_ofInt_of_le (by omega) (by omega)
  rw [UInt64.toNat_toUInt32, i64_toNat_toUInt64 _ (by omega), e]
  omega

/-! ## A round of the buffered path -/

/-- What a round of the buffered path of `gz_write` leaves, from the state `s1` and the loop state `st`; `ai` is the
input in the stream at the start of the round. -/
def WBPost (W : World) (H : Heap) (b : Nat) (s1 : GzState) (st : WriteLoop) (ai : Nat) (r : WriteLoop)
    (W' : World) (H' : Heap) : Prop :=
  ∃ s2 z2, W'.gz H' b = some s2 ∧ H'.streams s1.strm = some z2 ∧ GzInvWS W' H' (some b) ∧ GStep W H W' H' b [] ∧
    ZFix s1 s2 ∧ s2.size = s1.size ∧ s2.skip = s1.skip ∧
    s2.pos.toInt + r.len.toNat = s1.pos.toInt + st.len.toNat ∧ r.len.toNat ≤ st.len.toNat ∧
    (r.ctl = .go → r.len ≠ 0 → z2.avail_in = 0) ∧ (r.len = st.len → ai ≠ 0) ∧ (r.ctl = .go ∨ r.ctl = .ret) ∧
    ReadSlice H' r.buf r.len.toNat ∧ OutsideGz W' H' (some b) r.buf

theorem wb_main (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState} {z1 : ZStream}
    {c base k : Nat} (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0)
    (hB : GzBufs H s1 c base) (hz : H.streams s1.strm = some z1) (hk : z1.next_in = .ref (.heap c) (base + k))
    (hka : k + z1.avail_in.toNat ≤ s1.size.toNat) (hk0 : z1.avail_in = 0 → k = 0) (hsk : s1.skip = 0)
    (st : WriteLoop) (hctl : st.ctl = .go) (hl0 : st.len ≠ 0)
    (hpos : s1.pos.toInt + st.len.toNat ≤ GZ_OFF_MAX.toInt) (hr : ReadSlice H st.buf st.len.toNat)
    (ho : OutsideGz W H (some b) st.buf) :
    GSat W H (wbMain (some b) (some s1.strm) st) (WBPost W H b s1 st z1.avail_in.toNat) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hfr : FreshBlocks H := hv.2.2.2.1.1
  have hP := sh.pos
  have hpw := hP.write_pos hwm
  have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
  have hsw : s1.size.toNat = s1.want.toNat := by rw [hB.size]
  have hw30 := sh.want_hi
  obtain ⟨d, hd, hds⟩ := hB.fits
  have hin : inSize s1 = 2 * s1.want.toNat := by simp [inSize, hwm]
  have hg : Space.get H (BRef.heap c) = some d := hd
  obtain ⟨hcb, hpth, hst, hown⟩ := bufBlk hs hn hsz hB
  obtain ⟨rs, os, src, ebuf, hsrc, hos⟩ := hr
  have hrs : rs ≠ .heap c := by
    intro e; subst e; exact ho c hown os ebuf
  unfold wbMain
  refine GSat.bind (GSat.of_eq (a := z1.next_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.bind (GSat.of_eq (a := z1.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  rw [hk]
  refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c) (base + k + z1.avail_in.toNat)) (w' := W) (h' := H)
    (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
  refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
  rw [hB.inp]
  refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
  refine GSat.bind (GSat.of_eq (a := Int64.ofInt (((base + k + z1.avail_in.toNat : Nat) : Int) - base)) (w' := W) (h' := H)
    (by rw [lm_app, pdiff_ok hd (by omega) (by omega) (by omega)]) ?_)
  have ehv : (Int64.ofInt (((base + k + z1.avail_in.toNat : Nat) : Int) - base)).toUInt64.toUInt32.toNat =
      k + z1.avail_in.toNat := by
    have : (((base + k + z1.avail_in.toNat : Nat) : Int) - base) = ((k + z1.avail_in.toNat : Nat) : Int) := by omega
    rw [this]; exact diff_u32 _ (by omega)
  generalize (Int64.ofInt (((base + k + z1.avail_in.toNat : Nat) : Int) - base)).toUInt64.toUInt32 = hvv at ehv
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  have hle : hvv ≤ s1.size := UInt32.le_iff_toNat_le.mpr (by omega)
  have hsub : (s1.size - hvv).toNat = s1.size.toNat - (k + z1.avail_in.toNat) := by
    rw [UInt32.toNat_sub_of_le _ _ hle, ehv]
  -- the rest of the body for a chosen `copy`
  have cont : ∀ cp : UInt32, cp.toNat ≤ s1.size.toNat - (k + z1.avail_in.toNat) → cp.toNat ≤ st.len.toNat →
      (cp.toNat < st.len.toNat → cp.toNat = s1.size.toNat - (k + z1.avail_in.toNat)) →
      GSat W H (do
        let __do_lift ← ldGz (some b)
        let __do_lift ← liftM __do_lift.in.get
        let __do_lift ← lm (Ptr.add __do_lift (Int.ofNat hvv.toNat))
        lm (Ptr.memcpy __do_lift st.buf cp.toNat)
        lm (ZlibNg.Inflate.wrZ (some s1.strm) fun z => { z with avail_in := z.avail_in + cp })
        let np ← lm (chkI64 ((← rdG (some b) (·.pos)).toInt + cp.toNat))
        wrG (some b) fun st => { st with pos := np }
        let buf ← lm (Ptr.add st.buf (Int.ofNat cp.toNat))
        let len := st.len - cp.toUInt64
        if len != 0 then
          if (← gz_comp (some b) ZlibNg.Deflate.Z_NO_FLUSH) == -1 then
            return { st with buf := buf, len := len, ctl := .ret }
        return { st with buf := buf, len := len })
        (WBPost W H b s1 st z1.avail_in.toNat) := by
    intro cp hc1 hc2 hc3
    have hrd : ReadSlice H st.buf st.len.toNat := ⟨rs, os, src, ebuf, hsrc, hos⟩
    have hl0' : 0 < st.len.toNat := by
      rcases Nat.eq_zero_or_pos st.len.toNat with e | e
      · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) hl0
      · exact e
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    rw [hB.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    rw [ehv]
    refine GSat.bind (GSat.of_eq (a := Ptr.ref (BRef.heap c) (base + (k + z1.avail_in.toNat))) (w' := W) (h' := H)
      (by rw [lm_app, padd_ok hg _ (by omega)]) ?_)
    have hds' : base + 2 * s1.size.toNat ≤ d.size := by rw [hin] at hds; omega
    obtain ⟨H2, em, x2⟩ := memcpy_hbuf hd hsrc hrs (od := base + (k + z1.avail_in.toNat)) (os := os) (n := cp.toNat)
      (by omega) (by omega)
    rw [ebuf]
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W) (h' := H2) (by rw [lm_app, em]) ?_)
    obtain ⟨hv2, hs2, g2⟩ := invWS_hbuf hv hs x2 hcb hpth hst hown
    have hz2 : H2.streams s1.strm = some z1 := by obtain ⟨t, e, -⟩ := x2; rw [e]; exact hz
    have hai : (z1.avail_in + cp).toNat = z1.avail_in.toNat + cp.toNat := by
      rw [UInt32.toNat_add]; omega
    obtain ⟨hv3, hs3, g3⟩ := invWS_setIn hv2 hs2 hsz hz2 z1.next_in (z1.avail_in + cp) (fun c' base' hb' => by
      have e := hb'.buffers; rw [hB.buffers] at e; cases e
      exact Or.inl ⟨k, hk, Nat.zero_le _, by rw [hai]; omega⟩)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
      (h' := setZ H2 s1.strm { z1 with next_in := z1.next_in, avail_in := z1.avail_in + cp })
      (by simp [lm_app, wrZ_run hz2]) ?_)
    refine GSat.bind (GSat.of_eq (rdG_app' hs3 _) ?_)
    have hmax : GZ_OFF_MAX.toInt = 2 ^ 63 - 1 := by decide
    refine GSat.bind (GSat.of_eq (a := Int64.ofInt (s1.pos.toInt + cp.toNat))
      (by simp only [lm_app, chkI64_ok (v := s1.pos.toInt + cp.toNat) (by omega) (by omega)]; rfl) ?_)
    refine GSat.bind (GSat.of_eq (wrG_app hs3 _) ?_)
    have hp1 : (Int64.ofInt (s1.pos.toInt + cp.toNat)).toInt = s1.pos.toInt + cp.toNat :=
      Int64.toInt_ofInt_of_le (by omega) (by omega)
    obtain ⟨sh3, hn3⟩ := inv_of hs3 hv3.1
    have hsk0 : s1.skip.toInt = 0 := by rw [hsk]; rfl
    have sh4 := shape_posW sh3 hwm (Int64.ofInt (s1.pos.toInt + cp.toNat)) s1.skip
      ⟨by dsimp only; omega, by dsimp only; rw [hp1]; omega, by dsimp only; rw [hp1]; omega,
        fun _ => by dsimp only; rw [hp1]; omega⟩
    obtain ⟨hv4, hs4, g4⟩ := invWS_store hv3 hs3 sh4 hn3 hwm rfl (fun c' hc _ => by
      simp only [GzOwned, gz_upd_same hs3, hs3] at hc ⊢; exact hc)
    have g24 := (g2.trans g3 ⟨s1, hs⟩ ⟨s1, hs2⟩).trans g4 ⟨s1, hs⟩ ⟨s1, hs3⟩
    obtain ⟨hrd4, ho4⟩ := callerBuf_step g24 hfr hrd ho
    obtain ⟨rs', os', src', ebuf', hsrc', hos'⟩ := hrd4
    rw [ebuf] at ebuf'; cases ebuf'
    refine GSat.bind (GSat.of_eq (a := Ptr.ref rs (os + cp.toNat)) (by rw [lm_app, padd_ok hsrc' _ (by omega)]) ?_)
    have hcl : cp.toUInt64 ≤ st.len := UInt64.le_iff_toNat_le.mpr (by rw [UInt32.toNat_toUInt64]; omega)
    have hlen : (st.len - cp.toUInt64).toNat = st.len.toNat - cp.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hcl, UInt32.toNat_toUInt64]
    have hrdf : ∀ {W' : World} {H' : Heap}, GStep W H W' H' b [] →
        ReadSlice H' (Ptr.ref rs (os + cp.toNat)) (st.len - cp.toUInt64).toNat ∧
          OutsideGz W' H' (some b) (Ptr.ref rs (os + cp.toNat)) := by
      intro W' H' g'
      obtain ⟨⟨rs2, os2, src2, e2, h2, hle2⟩, ho2⟩ := callerBuf_step g' hfr hrd ho
      rw [ebuf] at e2; cases e2
      refine ⟨⟨rs, os + cp.toNat, src2, rfl, h2, by rw [hlen]; omega⟩, fun c' hc' off e => ?_⟩
      cases e; exact ho2 c' hc' os ebuf
    have hsz4 : ({ s1 with pos := Int64.ofInt (s1.pos.toInt + cp.toNat) } : GzState).size ≠ 0 := hsz
    have hz4 : (setZ H2 s1.strm { z1 with next_in := z1.next_in, avail_in := z1.avail_in + cp }).streams s1.strm =
        some { z1 with next_in := z1.next_in, avail_in := z1.avail_in + cp } := setZ_streams_same _ _ _
    have hsame : cp.toNat = 0 → z1.avail_in.toNat ≠ 0 := by
      intro e0 e1
      have : z1.avail_in = 0 := UInt32.toNat_inj.mp (by simpa using e1)
      have := hk0 this
      have h8 : 8 ≤ s1.size.toNat := by rw [hsw]; exact sh.want_lo
      omega
    have hs0 : st.len - cp.toUInt64 = st.len → z1.avail_in.toNat ≠ 0 := fun e => hsame (by
      have := congrArg UInt64.toNat e; rw [hlen] at this; omega)
    refine GSat.ite (fun hne => ?_) (fun heq => ?_)
    · refine GSat.bind (GSat.mono (comp_inv C G hv4 hs4 _) fun r W5 H5 q => ?_)
      obtain ⟨s5, z5, hs5, hz5, hv5, g5, fx, hsz5, hr5, hok⟩ := q
      have g := g24.trans g5 ⟨s1, hs⟩ ⟨_, hs4⟩
      have z45 := ZFix.of_w fx
      have zf : ZFix s1 s5 := ⟨z45.want, z45.direct, z45.mode, z45.level, z45.strategy, z45.fd, z45.strm⟩
      have hsz15 : s5.size = s1.size := hsz5 hsz4
      have hpos5 : s5.pos.toInt = s1.pos.toInt + cp.toNat := by rw [fx.pos]; exact hp1
      have hne' : st.len - cp.toUInt64 ≠ 0 := by simpa using hne
      have hnl : (st.len - cp.toUInt64).toNat ≠ 0 := fun e => hne' (UInt64.toNat_inj.mp (by simpa using e))
      obtain ⟨hrd5, ho5⟩ := hrdf g
      refine GSat.ite (fun _ => GSat.pure ⟨s5, z5, hs5, hz5, hv5, g, zf, hsz15, fx.skip,
        by dsimp only; rw [hpos5, hlen]; omega, by dsimp only; rw [hlen]; omega, fun e => by simp at e, hs0, Or.inr rfl,
        hrd5, ho5⟩) (fun hc => ?_)
      have hr0 : r = 0 := by rcases hr5 with e | e; exact e; simp [e] at hc
      exact GSat.pure ⟨s5, z5, hs5, hz5, hv5, g, zf, hsz15, fx.skip, by dsimp only; rw [hpos5, hlen]; omega,
        by dsimp only; rw [hlen]; omega, fun _ _ => (hok hr0).2 (by decide), hs0, Or.inl hctl, hrd5, ho5⟩
    · obtain ⟨hrd5, ho5⟩ := hrdf g24
      have h0 : st.len - cp.toUInt64 = 0 := by simpa using heq
      exact GSat.pure ⟨_, _, hs4, hz4, hv4, g24, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
        by dsimp only; rw [hp1, hlen]; omega, by dsimp only; rw [hlen]; omega, fun _ e => absurd h0 e,
        hs0, Or.inl hctl, hrd5, ho5⟩
  dsimp only
  split
  · next hgt =>
    have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
    rw [UInt32.toNat_toUInt64, hsub] at hgt'
    have e : st.len.toUInt32.toNat = st.len.toNat := by rw [UInt64.toNat_toUInt32]; omega
    exact cont _ (by omega) (by omega) (fun _ => by omega)
  · next hng =>
    have hng' : ¬ st.len.toNat < (s1.size - hvv).toUInt64.toNat := fun h' => hng (UInt64.lt_iff_toNat_lt.mpr h')
    rw [UInt32.toNat_toUInt64, hsub] at hng'
    exact cont _ (by omega) (by omega) (fun _ => by omega)

theorem wb_body (C : GzCompSpec) (G : DeflateGz) {W : World} {H : Heap} {b : Nat} {s1 : GzState} {z : ZStream}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (hsz : s1.size ≠ 0) (hz : H.streams s1.strm = some z)
    (hsk : s1.skip = 0) (st : WriteLoop) (hctl : st.ctl = .go) (hl0 : st.len ≠ 0)
    (hpos : s1.pos.toInt + st.len.toNat ≤ GZ_OFF_MAX.toInt) (hr : ReadSlice H st.buf st.len.toNat)
    (ho : OutsideGz W H (some b) st.buf) :
    GSat W H (wbBody (some b) (some s1.strm) st) (WBPost W H b s1 st z.avail_in.toNat) := by
  have hwm := modeOf hs hv.2.1
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  obtain ⟨c, base, z0, hB, hz0, WB⟩ := (sh.write hwm).bufs hsz
  rw [hz] at hz0; cases hz0
  unfold wbBody
  refine GSat.bind (GSat.of_eq (a := z.avail_in) (w' := W) (h' := H) (by simp [lm_app, rdZ_run hz]) ?_)
  refine GSat.ite (fun hai => ?_) (fun hai => ?_)
  · have hai0 : z.avail_in = 0 := by simpa using hai
    refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
    rw [hB.inp]
    refine GSat.bind (GSat.of_eq (liftM_get_val _ _ _) ?_)
    obtain ⟨hv1, hs1, g1⟩ := invWS_setIn hv hs hsz hz (.ref (.heap c) base) z.avail_in (fun c' base' hb => by
      have e := hb.buffers; rw [hB.buffers] at e; cases e
      exact Or.inl ⟨0, by simp, Nat.le_refl _, by rw [hai0]; simp⟩)
    refine GSat.bind (GSat.of_eq (a := ()) (w' := W)
      (h' := setZ H s1.strm { z with next_in := .ref (.heap c) base, avail_in := z.avail_in })
      (by simp [lm_app, wrZ_run hz]) ?_)
    have hB1 : GzBufs (setZ H s1.strm { z with next_in := .ref (.heap c) base, avail_in := z.avail_in }) s1 c base :=
      ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩
    obtain ⟨hr1, ho1⟩ := callerBuf_step g1 hv.2.2.2.1.1 hr ho
    refine GSat.mono (wb_main C G hv1 hs1 hsz hB1 (setZ_streams_same _ _ _) (k := 0) (by simp)
      (by rw [hai0]; simp) (fun _ => rfl) hsk st hctl hl0 hpos hr1 ho1) fun r W2 H2 q => ?_
    obtain ⟨s2, z2, hs2, hz2, hv2, g2, rest⟩ := q
    exact ⟨s2, z2, hs2, hz2, hv2, g1.trans g2 ⟨s1, hs⟩ ⟨s1, hs1⟩, rest⟩
  · have hai0 : z.avail_in ≠ 0 := by simpa using hai
    rcases WB.inp with ⟨k, ek, -, hk⟩ | ⟨e1, -⟩
    · exact wb_main C G hv hs hsz hB hz ek hk (fun e => absurd e hai0) hsk st hctl hl0 hpos hr ho
    · exact absurd e1 hai0

/-- **The buffered path of `gz_write`**: the loop ends, keeping the invariant. -/
theorem wb_loop (C : GzCompSpec) (G : DeflateGz) {w W : World} {h H : Heap} {b : Nat} {s s1 : GzState}
    (hv : GzInvWS W H (some b)) (hs : W.gz H b = some s1) (g : GStep w h W H b []) (zf : ZFix s s1)
    (hsz : s1.size ≠ 0) (hsk : s1.skip = 0) (hs0 : ∃ s0, w.gz h b = some s0) (buf : BPtr) (len : UInt64)
    (hl0 : len ≠ 0) (hl : len.toNat < 2 ^ 31) (hpos : s1.pos.toInt + len.toNat ≤ GZ_OFF_MAX.toInt)
    (hr : ReadSlice H buf len.toNat) (ho : OutsideGz W H (some b) buf) :
    GSat W H (gdoWhile (wbBody (some b) (some s.strm)) wCond ⟨buf, len, .go⟩)
      (fun lp W' H' => ∃ s2, W'.gz H' b = some s2 ∧ GzInvWS W' H' (some b) ∧ GStep w h W' H' b [] ∧ ZFix s s2 ∧
        s2.size = s1.size ∧ s2.skip = 0 ∧ (lp.ctl = .go ∨ lp.ctl = .ret)) := by
  refine gsat_gdoWhile (fun st W H => st.ctl = .go ∧ st.len ≠ 0 ∧ st.len.toNat < 2 ^ 31 ∧ ∃ s2 z2,
      W.gz H b = some s2 ∧ H.streams s.strm = some z2 ∧ GzInvWS W H (some b) ∧ GStep w h W H b [] ∧ ZFix s s2 ∧
      s2.size = s1.size ∧ s2.skip = 0 ∧ s2.pos.toInt + st.len.toNat ≤ GZ_OFF_MAX.toInt ∧
      ReadSlice H st.buf st.len.toNat ∧ OutsideGz W H (some b) st.buf)
    (fun st _ H => 2 * st.len.toNat + (match H.streams s.strm with
      | some z => if z.avail_in = 0 then 0 else 1 | none => 0)) _ ?_ ?_ ?_
  · rintro st W1 H1 ⟨hctl, hl1, hlt, s2, z2, hs2, hz2, hv2, g2, zf2, hsz2, hsk2, hpos2, hr2, ho2⟩
    rw [← zf2.strm] at hz2 ⊢
    refine GSat.mono (wb_body C G hv2 hs2 (by rw [hsz2]; exact hsz) hz2 hsk2 st hctl hl1 hpos2 hr2 ho2)
      fun r W3 H3 q => ?_
    obtain ⟨s3, z3, hs3, hz3, hv3, g3, zf3, hsz3, hsk3, hpos3, hle3, hgo, hsame, hrr, hr3, ho3⟩ := q
    have g' := g2.trans g3 hs0 ⟨s2, hs2⟩
    have zf' : ZFix s s3 := zf2.trans zf3
    unfold wCond
    rcases hrr with hrr | hrr
    · refine GSat.ite (fun hc => by simp [hrr] at hc) (fun _ => GSat.pure ⟨fun e => ?_, fun _ =>
        ⟨s3, hs3, hv3, g', zf', by rw [hsz3, hsz2], by rw [hsk3, hsk2], Or.inl hrr⟩⟩)
      dsimp only at e ⊢
      have hl3 : r.len ≠ 0 := by simpa using e
      refine ⟨⟨hrr, hl3, by omega, s3, z3, hs3, hz3, hv3, g', zf', by rw [hsz3, hsz2], by rw [hsk3, hsk2],
        by omega, hr3, ho3⟩, ?_⟩
      have h0 := hgo hrr hl3
      simp only [hz3, h0, hz2, ite_true]
      by_cases hz0 : z2.avail_in = 0
      · have : r.len ≠ st.len := fun e => hsame e (by rw [hz0]; rfl)
        have : r.len.toNat ≠ st.len.toNat := fun e => this (UInt64.toNat_inj.mp e)
        simp only [hz0, ite_true]; omega
      · simp only [hz0, ite_false]; omega
    · refine GSat.ite (fun _ => GSat.pure ⟨fun e => by simp at e, fun _ =>
        ⟨s3, hs3, hv3, g', zf', by rw [hsz3, hsz2], by rw [hsk3, hsk2], Or.inr hrr⟩⟩) (fun hc => by simp [hrr] at hc)
  · obtain ⟨sh, -⟩ := inv_of hs hv.1
    obtain ⟨z, hz⟩ := sh.strm
    exact ⟨rfl, hl0, hl, s1, z, hs, by rw [← zf.strm]; exact hz, hv, g, zf, rfl, hsk, hpos, hr, ho⟩
  · show 2 * len.toNat + _ < fuel
    unfold fuel
    split <;> (try split) <;> omega

end ZlibNgF.Proof.GzWrite
