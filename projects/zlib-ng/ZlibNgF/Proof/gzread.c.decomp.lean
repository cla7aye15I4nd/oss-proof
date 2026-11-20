import ZlibNgF.Proof.«gzread.c.init»
import ZlibNgF.Proof.«gzlib.c.seek64»
import ZlibNgF.Proof.«gzread.c.facts»

/-!
# `gz_avail` with its read measure, and `gz_decomp` (`ZlibNgF`)

`gz_decomp` loops while `inflate` makes progress and the caller's output has room. Its measure is the input still
to come: the bytes the read oracle may still deliver (`Fs.budget`), the bytes of the file of the descriptor after its
offset (`rdLeft`), and the input `avail_in` already in the buffer, plus the room `avail_out`. `gz_avail` does not raise
`rdLeft + avail_in` (`gz_avail_budget`), and a trip of the loop that does not end it lowers `avail_in + avail_out`
(`inflate` returned `Z_OK`).

`InflateGz` and `InflateMsg` are what `gz_decomp` needs of `inflate` beyond `inflate_ok`: the set of its results, that
it moves `next_in` and `next_out` exactly by the bytes it consumed and wrote, and that it leaves `msg` as it was or
sets it to one of its string literals; both hold (`inflateGz`, `inflateMsg`). `InflateFresh` (no end of the stream
without input from a just reset state) is what `gz_fetch` needs for its termination; `gz_decomp_spec` states its
consequence as an implication, so no theorem here assumes it.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ZlibNgF.Proof.GzDecomp
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz ZlibNgF.Proof.GzInv ZlibNgF.Proof.GzSat ZlibNgF.Proof.GzMode

open ZlibNg.Inflate in
/-- What the gz read path needs of `inflate` beyond `inflate_ok`: its result is one of the codes of `zlib.h` it can
return; once its entry check passes (and, for `io`, unless it returned `Z_STREAM_ERROR`), `next_in` moved exactly by
the input consumed and `next_out` exactly by the output written, with the state kept. -/
structure InflateGz : Prop where
  res : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    r = Z_OK ∨ r = Z_STREAM_END ∨ r = Z_NEED_DICT ∨ r = Z_BUF_ERROR ∨ r = Z_DATA_ERROR ∨ r = Z_STREAM_ERROR
  io : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    r ≠ Z_STREAM_ERROR → ∀ z, h.streams i = some z →
    ∃ z', h'.streams i = some z' ∧ z'.state = z.state ∧
      InflateLoop.InAt z.next_in z.avail_in z'.next_in z'.avail_in ∧ z'.avail_out ≤ z.avail_out ∧
      ∃ bo oo, z.next_out = .ref (.heap bo) oo ∧ z'.next_out = .ref (.heap bo) (oo + (z.avail_out - z'.avail_out).toNat)
  io' : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ z, h.streams i = some z → z.next_out ≠ .null → (z.avail_in = 0 ∨ z.next_in ≠ .null) →
    ∃ z', h'.streams i = some z' ∧ z'.state = z.state ∧
      InflateLoop.InAt z.next_in z.avail_in z'.next_in z'.avail_in ∧ z'.avail_out ≤ z.avail_out ∧
      ∃ bo oo, z.next_out = .ref (.heap bo) oo ∧ z'.next_out = .ref (.heap bo) (oo + (z.avail_out - z'.avail_out).toNat)

open ZlibNg.Inflate in
/-- What `gz_fetch` needs of `inflate` for its termination: from a just reset state (`HEAD`, no bits held, not the
last block) it does not end the stream without consuming input. -/
structure InflateFresh : Prop where
  fresh_end : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ z sb st, h.streams i = some z → z.state = some sb → h.istate sb = some st →
    st.mode = ZlibNg.Inflate.HEAD → st.bits = 0 → st.last = 0 → r = Z_STREAM_END →
    ∀ z', h'.streams i = some z' → z'.avail_in < z.avail_in

open ZlibNg.Inflate in
/-- What `gz_decomp` needs of `inflate` for its `Z_DATA_ERROR` message: `inflate` leaves the stream's `msg` as it was
or sets it to one of its string literals. -/
structure InflateMsg : Prop where
  msg : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ z, h.streams i = some z → ∃ z', h'.streams i = some z' ∧
      (z'.msg = z.msg ∨ ∃ k, z'.msg = .ref (.str k) 0 ∧ k < strTable.size)

/-- `InflateGz` holds (`inflate.c.extra`). -/
theorem inflateGz : InflateGz :=
  ⟨InflateExtra.inflate_res, InflateExtra.inflate_io, InflateExtra.inflate_io_entry⟩

/-- `InflateMsg` holds (`inflate.c.extra`). -/
theorem inflateMsg : InflateMsg := ⟨InflateExtra.inflate_msg⟩

open ZlibNg.Inflate in
/-- What `gz_fetch` and `gz_read` need of `inflate` for their termination: from a just reset state (`HEAD`, no bits
held, not the last block) with input, every return other than `Z_STREAM_ERROR` consumed input, so a gzip member
costs input before it gives output or ends. -/
structure InflateFreshIn : Prop where
  fresh_in : ∀ h i flush r h', InflateInv.Inv h (some i) → StreamIO h (some i) →
    h.crcTable = ZlibNg.Crc32Tbl.crc_table → ZlibNg.Inflate.inflate (some i) flush h = .ok (r, h') →
    ∀ z sb st, h.streams i = some z → z.state = some sb → h.istate sb = some st →
    st.mode = ZlibNg.Inflate.HEAD → st.bits = 0 → st.last = 0 → z.avail_in ≠ 0 → r ≠ Z_STREAM_ERROR →
    ∀ z', h'.streams i = some z' → z'.avail_in < z.avail_in

/-- `InflateFresh` holds (`inflate.c.extra`). -/
theorem inflateFresh : InflateFresh := ⟨InflateExtra.inflate_fresh_end⟩

/-- `InflateFreshIn` holds (`inflate.c.extra`). -/
theorem inflateFreshIn : InflateFreshIn := ⟨InflateExtra.inflate_fresh_in⟩

/-! ## The read measure -/

/-- The bytes that reads of descriptor `fd` may still deliver: the read oracle's `budget`, and the bytes of the file
of `fd` after its offset. -/
def rdLeft (fs : Fs) (fd : Int32) : Nat :=
  fs.budget + match fs.ofile? fd with
    | some o => (fs.nodes[o.node]?.getD #[]).size - o.pos
    | none => 0

theorem ofile_setFd (w : Fs) (fd : Int32) (h0 : 0 ≤ fd) (o : OFile) :
    (w.setFd fd.toNatClampNeg (some o)).ofile? fd = some o := by
  unfold Fs.ofile? Fs.setFd
  have : ¬ fd < 0 := Int32.not_lt.mpr h0
  simp only [this, ite_false]
  split
  · next hi => simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hi]
  · next hi =>
    have : fd.toNatClampNeg < w.fds.size + (fd.toNatClampNeg + 1 - w.fds.size) := by omega
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, this]

theorem rdLeft_tick (fs : Fs) (fd : Int32) : rdLeft fs.tick fd = rdLeft fs fd := rfl

theorem rdLeft_errno (fs : Fs) (fd : Int32) (e : Int32) : rdLeft { fs with errno := e } fd = rdLeft fs fd := rfl

theorem readReg_left (fs : Fs) (fd : Int32) (n : UInt64) (hn : n.toNat < 2 ^ 63) :
    rdLeft (fs.readReg fd n).2.2 fd + (fs.readReg fd n).1.toInt.toNat ≤ rdLeft fs fd := by
  unfold Fs.readReg
  split
  · next o ho =>
    split
    · simp [rdLeft_errno]
    · have h0 : 0 ≤ fd := by
        unfold Fs.ofile? at ho; split at ho
        · cases ho
        · next hl => exact Int32.not_lt.mp hl
      have hk : min n.toNat ((fs.nodes[o.node]?.getD #[]).size - o.pos) < 2 ^ 63 := by omega
      simp only
      rw [Int64.toInt_ofNat_of_lt hk]
      unfold rdLeft
      rw [ofile_setFd _ _ h0, ho]
      simp only [Fs.setFd]
      omega
  · simp [rdLeft_errno]

theorem readCall_left (fs : Fs) (fd : Int32) (n : UInt64) (hn : n.toNat < 2 ^ 63) :
    rdLeft (fs.readCall fd n).2.2 fd + (fs.readCall fd n).1.toInt.toNat ≤ rdLeft fs fd := by
  unfold Fs.readCall
  simp only
  split
  · exact readReg_left _ _ _ hn
  · simp [rdLeft_errno, rdLeft_tick]
  · next k _ =>
    have h1 : (min n (UInt64.ofNat k)).toNat ≤ n.toNat := by
      rw [UInt64.min_def]; split
      · exact Nat.le_refl _
      · next hl => have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); omega
    exact readReg_left fs.tick fd _ (by omega)
  · next bs _ =>
    have hk : min (min bs.size n.toNat) fs.tick.budget < 2 ^ 63 := by
      have := Nat.min_le_left (min bs.size n.toNat) fs.tick.budget
      have := Nat.min_le_right bs.size n.toNat
      omega
    rw [Int64.toInt_ofNat_of_lt hk]
    unfold rdLeft
    simp only [Fs.tick]
    have := Nat.min_le_right (min bs.size n.toNat) fs.budget
    simp only [Fs.ofile?] at *
    omega

/-! ## `gz_load` with its read measure -/

/-- `loadLoop_spec` with the read measure: the bytes counted come out of `rdLeft`, and the loop stops on a read
that returned at most 0 or with `len` bytes counted. -/
theorem loadLoop_budget {w : World} {h : Heap} {b : Nat} {s : GzState} (hs : w.gz h b = some s) {cb p : Nat}
    {a : Array UInt8} (ha : h.bytes cb = some a) (len : UInt32) (hp : p + len.toNat ≤ a.size) (hcb : b ≠ cb) :
    GSat w h (gdoWhile (loadBody (some b) (.ref (.heap cb) p) len) (loadCond len) ⟨0, 0, .go⟩)
      (fun lp W H => lp.hv.toNat ≤ len.toNat ∧ (lp.ret ≤ 0 ∨ len.toNat ≤ lp.hv.toNat) ∧ ∃ fs', FsRd w.fs fs' ∧
        rdLeft fs' s.fd + lp.hv.toNat ≤ rdLeft w.fs s.fd ∧ W = { w with fs := fs' } ∧
        HBuf h H cb p (p + len.toNat)) := by
  refine gsat_gdoWhile (fun (st : LoadLoop) W H => st.ctl = .go ∧ st.hv.toNat ≤ len.toNat ∧ ∃ fs', FsRd w.fs fs' ∧
      rdLeft fs' s.fd + st.hv.toNat ≤ rdLeft w.fs s.fd ∧ W = { w with fs := fs' } ∧ HBuf h H cb p (p + len.toNat))
    (fun st _ _ => len.toNat - st.hv.toNat) _ ?_ ⟨rfl, by simp, w.fs, FsRd.refl _, by simp, rfl, HBuf.refl _ _ _ _⟩
    (by have := len.toNat_lt; simp [fuel]; omega)
  intro st W H ⟨hgo, hle, fs', hfs, hleft, hW, x⟩
  subst hW
  have hsW : ({ w with fs := fs' } : World).gz H b = some s := by rw [x.gz hcb]; exact hs
  obtain ⟨a1, ha1, hsz⟩ := x.size ha
  unfold loadBody
  refine GSat.bind (GSat.pure ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hsW _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, addH ha1 st.hv.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.pure ?_)
  have hn : (len - st.hv).toUInt64.toNat = len.toNat - st.hv.toNat := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hle)]
  have hlen := len.toNat_lt
  refine GSat.bind (GSat.mono (readG_spec ha1 s.fd (len - st.hv).toUInt64 (by rw [hn]; omega)
    (by rw [hn]; omega)) fun r W1 H1 q => ?_)
  obtain ⟨rfl, hr, x1⟩ := q
  have x2 : HBuf h H1 cb p (p + len.toNat) := x.trans x1 (by omega) (by rw [hn]; omega)
  have hfs2 : FsRd w.fs (fs'.readCall s.fd (len - st.hv).toUInt64).2.2 := hfs.trans (readCall_rd _ _ _)
  have hl2 := readCall_left fs' s.fd (len - st.hv).toUInt64 (by rw [hn]; omega)
  rw [← hr] at hl2
  have hres := readCall_res fs' s.fd (len - st.hv).toUInt64 (by rw [hn]; omega)
  rw [← hr, hn] at hres
  apply GSat.ite
  · intro hr0
    refine GSat.pure (GSat.of_eq rfl ⟨fun e => absurd e (by simp), fun _ => ⟨hle, Or.inl hr0, _, hfs2, by simp only; omega,
      rfl, x2⟩⟩)
  · intro hr0
    have h0 : (0 : Int64) ≤ r := by
      rw [Int64.le_iff_toInt_le] at hr0 ⊢; simp at hr0 ⊢; omega
    have hpos : 0 < r.toInt := by
      rw [Int64.le_iff_toInt_le] at hr0; simp at hr0; omega
    have hle2 : r.toInt ≤ (len.toNat - st.hv.toNat : Nat) := by
      rcases hres with ⟨e, -⟩ | ⟨-, e, -⟩
      · rw [e] at hpos; simp at hpos
      · exact e
    have hk : r.toUInt64.toUInt32.toNat = r.toInt.toNat := by
      rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le h0, ← Int64.toNat_toInt]; omega
    have hsum : (st.hv + r.toUInt64.toUInt32).toNat = st.hv.toNat + r.toInt.toNat := by
      rw [UInt32.toNat_add, hk]; omega
    refine GSat.bind (GSat.pure ?_)
    refine GSat.bind (GSat.pure ?_)
    refine GSat.pure ?_
    unfold loadCond
    apply GSat.ite
    · intro hc
      exact GSat.pure ⟨fun e => absurd e (by simp), fun _ => absurd hc (by simp [hgo])⟩
    · intro _
      refine GSat.bind (GSat.pure ?_)
      refine GSat.pure ⟨fun _ => ⟨⟨hgo, by simp only; omega, _, hfs2, by simp only; omega, rfl, x2⟩, by simp only; omega⟩,
        fun hc => ⟨by simp only; omega, Or.inr ?_, _, hfs2, by simp only; omega, rfl, x2⟩⟩
      simp only [decide_eq_false_iff_not] at hc
      have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp hc)
      simp only; omega

/-! ## `gz_error` keeps the stream -/

theorem GSat.and {α : Type} {w : World} {h : Heap} {m : G α} {P Q : α → World → Heap → Prop} (p : GSat w h m P)
    (q : GSat w h m Q) : GSat w h m (fun r W H => P r W H ∧ Q r W H) := by
  obtain ⟨r, W, H, e, hp⟩ := p
  obtain ⟨r', W', H', e', hq⟩ := q
  rw [e] at e'; cases e'
  exact ⟨r, W, H, e, hp, hq⟩

/-- `gz_error` on a read handle does not change the heap's streams. -/
theorem gz_error_strm {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ _ H => H.streams = h.streams) := by
  have hlit : LitOk w h := hv.2.2.lit
  obtain ⟨⟨b0, s0, e0, hs0, sh, hn⟩, -, hw⟩ := hv
  cases e0; rw [hs] at hs0; cases hs0
  obtain ⟨db, hdb⟩ := gz_live hs
  have fr : FreshBlocks h := hw.2.1.1
  have hdb1 : (freeMsg h s).bytes b = some db := freeMsg_bytes_b hn hdb
  have hs1 : ({ w with gzs := upd w.gzs b (some (errSt s e)) } : World).gz (freeMsg h s) b = some (errSt s e) := by
    unfold World.gz; rw [hdb1]; simp
  obtain ⟨sh1, -⟩ := err0_keep sh hn e
  have fr1 : FreshBlocks (freeMsg h s) := (HLess.free h s).freshB fr
  obtain ⟨r, W, H, eq, -, -, -, -, -, x, -, -⟩ := errTail_spec hs1 fr1
    (LitOk.ext (w := w) hlit rfl fun k a e' => by rw [freeMsg_consts]; exact e') sh1.path rfl e rfl msg
    (hmsg.imp_right fun hp => cstr_free hp hmk)
  exact ⟨r, W, H, by rw [gz_error_run hs sh.msg (msg_ne_b hn) e msg]; exact eq,
    x.streams.trans (freeMsg_streams h s)⟩

/-! ## `gz_avail` with its read measure -/

/-- What `gz_decomp` needs of a `gz_avail` that returned 0, beyond `AvailPost`: only `next_in` and `avail_in` of the
stream `z` changed, the input in the buffer grew by at most what came out of the read measure, and there is input or
`eof` is set. -/
def AvailBudget (w : World) (b : Nat) (s : GzState) (z : ZStream) (r : Int32) (W : World) (H : Heap) : Prop :=
  (r = 0 → ∃ s' z', W.gz H b = some s' ∧ H.streams s.strm = some z' ∧
    z' = { z with next_in := z'.next_in, avail_in := z'.avail_in } ∧
    rdLeft W.fs s.fd + z'.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat ∧ (z'.avail_in ≠ 0 ∨ s'.eof ≠ 0)) ∧
  (r = -1 → H.streams s.strm = some z) ∧
  (r = 0 → (s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR) ∧ ∀ s', W.gz H b = some s' → s'.err = s.err)

theorem availTail_budget {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) (hnc : s.how ≠ ZlibNg.Gz.COPY) {c base : Nat} {z : ZStream}
    (hB : GzBufs h s c base) (hz : h.streams s.strm = some z)
    (hai : z.avail_in = 0 ∨ Inside c base 0 (inSize s) z.next_in z.avail_in.toNat)
    {H : Heap} (x : HBuf h H c base (base + inSize s)) (hok : s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR) :
    GSat w H (availTail (some b) (some s.strm)) (fun r W H' => AvailPost w H b s r W H' ∧ AvailBudget w b s z r W H') := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  have hsH : w.gz H b = some s := by rw [x.gz hcb]; exact hs
  have hstrH : H.streams = h.streams := by obtain ⟨t, rfl, -⟩ := x; rfl
  have hzH : H.streams s.strm = some z := by rw [hstrH]; exact hz
  have hownH : c ∈ GzOwned w H (some b) := by
    have : GzOwned w H (some b) = GzOwned w h (some b) := by simp only [GzOwned, hsH, hs, hstrH]
    rw [this]; exact hown
  obtain ⟨d, hd, hds⟩ := hB.fits
  obtain ⟨dH, hdH, hszH⟩ := x.size hd
  have hin : inSize s = s.want.toNat := by simp [inSize, hr, read_ne_write]
  have hsize : s.size.toNat = inSize s := by rw [hin, hB.size]
  have hwl := sh.want_hi
  have hai' : z.avail_in.toNat ≤ inSize s := by
    rcases hai with e | ⟨k, -, -, e⟩
    · rw [e]; simp
    · omega
  unfold availTail
  refine GSat.bind (GSat.of_eq (ldGz_app hsH) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, by rw [hB.inp]; rfl, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hzH _, ?_⟩)
  refine GSat.bind (GSat.lm ⟨_, H, addH hdH (off := base) z.avail_in.toNat (by omega), ?_⟩)
  refine GSat.bind (GSat.of_eq (rdG_app' hsH _) ?_)
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hzH _, ?_⟩)
  have hlen : (s.size - z.avail_in).toNat = inSize s - z.avail_in.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), hsize]
  refine GSat.bind ?_
  rw [gz_load_false]
  refine GSat.bind (GSat.pure ?_)
  refine GSat.bind (GSat.mono (loadLoop_budget hsH hdH (p := base + z.avail_in.toNat) (s.size - z.avail_in)
    (by rw [hlen]; omega) hcb) fun lp W1 H1 q => ?_)
  obtain ⟨hlp, hex, fs', hfs, hleft, rfl, x1⟩ := q
  have x01 : HBuf h H1 c base (base + inSize s) := x.trans x1 (by omega) (by rw [hlen]; omega)
  have hv1 : GzInvR { w with fs := fs' } H1 (some b) := invR_hbuf hv hs x01 hcb hpath hst hfs
  have hs1 : ({ w with fs := fs' } : World).gz H1 b = some s := by rw [x01.gz hcb]; exact hs
  have g1 : GStep w H { w with fs := fs' } H1 b [] := by
    have := gstep_hbuf hsH x1 hcb hownH fs' s rfl rfl rfl rfl
    rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
    exact this
  unfold loadTail
  apply GSat.ite
  · intro _
    obtain ⟨pm, am, ez, hcs, hmk⟩ := zstrerror_spec { w with fs := fs' } H1
    refine GSat.bind (GSat.of_eq ez ?_)
    refine GSat.bind (GSat.mono (GSat.and (gz_error_inv (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk)
      (gz_error_strm (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk)) fun _ W H2 q => ?_)
    obtain ⟨⟨s', hsW, herr, hvW, -, hfsW, hstep⟩, hstr⟩ := q
    have hzH1 : H1.streams s.strm = some z := by obtain ⟨t, rfl, -⟩ := x1; exact hzH
    refine GSat.pure (GSat.pure ⟨⟨Or.inl rfl, hvW, ?_, by rw [hfsW]; exact hfs, s', hsW, errOf_shape herr h0⟩,
      fun e => absurd e (by decide), fun _ => by rw [hstr]; exact hzH1, fun e => absurd e (by decide)⟩)
    exact (g1.trans (gstep_lit hs1 am) ⟨s, hsH⟩ ⟨s, hs1⟩).trans hstep ⟨s, hsH⟩ ⟨s, hs1⟩
  · intro hneg
    have hz1 : H1.streams s.strm = some z := by
      obtain ⟨t, rfl, -⟩ := x1; exact hzH
    have tail : ∀ e : Int32, (e ≠ 0 ∨ 0 < z.avail_in.toNat + lp.hv.toNat) → GSat { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } H1
        (match ((0 : Int32), lp.hv) with
          | (r, got) =>
            if (r == -1) = true then (pure (-1) : G Int32)
            else do
              lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with avail_in := z.avail_in + got })
              let inb ← (← ldGz (some b)).«in».get
              lm (ZlibNg.Inflate.wrZ (some s.strm) fun z => { z with next_in := inb })
              return 0) (fun r W H' => AvailPost w H b s r W H' ∧ AvailBudget w b s z r W H') := by
      intro e he
      have hs2 := gzX_upd hs x01 hcb fs' { s with eof := e }
      let z1 : ZStream := { z with avail_in := z.avail_in + lp.hv }
      let z' : ZStream := { z with avail_in := z.avail_in + lp.hv, next_in := .ref (.heap c) base }
      apply GSat.ite
      · intro hc; exact absurd hc (by decide)
      · intro _
        refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z1) },
          wrZ_app hz1 _, ?_⟩)
        refine GSat.bind (GSat.of_eq (ldGz_app hs2) ?_)
        refine GSat.bind (GSat.lm ⟨.ref (.heap c) base, { H1 with streams := upd H1.streams s.strm (some z1) },
          (by show Ival.get s.«in» _ = _; rw [hB.inp]; rfl), ?_⟩)
        refine GSat.bind (GSat.lm ⟨(), { H1 with streams := upd H1.streams s.strm (some z') },
          (by rw [wrZ_app (z := z1) (by simp)]; simp [InflateInv.upd_upd, z1, z']), ?_⟩)
        have hsum : (z.avail_in + lp.hv).toNat = z.avail_in.toNat + lp.hv.toNat := by
          rw [UInt32.toNat_add]; rw [hlen] at hlp; omega
        refine GSat.pure ⟨⟨Or.inr rfl, ?_, ?_, hfs, _, hs2, rfl⟩, fun _ => ⟨_, z', hs2, by simp, rfl, ?_, ?_⟩,
          fun e => absurd e (by decide), fun _ => ⟨hok, fun s2 h2 => by
            unfold World.gz at h2; split at h2
            · simp at h2; rw [← h2]
            · cases h2⟩⟩
        · obtain ⟨sh1, hn1⟩ := inv_of hs1 hv1.1
          have sh1' := shape_msg sh1 e s.past s.err s.msg ⟨sh1.msg.1, sh1.msg.2⟩
          have hvE : GzInvR { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } H1 (some b) :=
            (keeps_store hs1 (HLess.refl H1) (fun _ e => e) sh1' hn1 rfl rfl).1 hv1
          refine invR_strm (s := { s with eof := e }) (z := z) (z' := z') hvE hs2 hsz hz1 rfl (fun c' base' hB' => Or.inr ⟨0, ?_, Nat.le_refl _, ?_⟩) (fun e => absurd e hnc)
          · have e1 := hB'.buffers; have e2 := hB.buffers
            rw [show ({ s with eof := e } : GzState).buffers = s.buffers from rfl, e2] at e1; cases e1; rfl
          · show 0 + (z.avail_in + lp.hv).toNat ≤ inSize s
            rw [UInt32.toNat_add]; rw [hlen] at hlp; omega
        · exact (gstep_hbuf hsH x1 hcb hownH fs' { s with eof := e } rfl rfl rfl rfl).trans
            (gstep_strm hs2 z' hz1 rfl) ⟨s, hsH⟩ ⟨_, hs2⟩
        · show rdLeft fs' s.fd + (z.avail_in + lp.hv).toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat
          rw [hsum]; omega
        · show (z.avail_in + lp.hv) ≠ 0 ∨ e ≠ 0
          rcases he with he | he
          · exact Or.inr he
          · left; intro e0; have := congrArg UInt32.toNat e0; rw [hsum] at this; simp at this; omega
    apply GSat.ite
    · intro _
      exact GSat.bind (GSat.of_eq (wrG_app hs1 _) (GSat.pure (tail 1 (Or.inl (by decide)))))
    · intro hne0
      have hpos : 0 < z.avail_in.toNat + lp.hv.toNat := by
        rcases hex with hle | hle
        · exfalso
          have a1 : lp.ret.toInt ≤ 0 := by have := Int64.le_iff_toInt_le.mp hle; simpa using this
          have a2 : ¬ lp.ret.toInt < 0 := fun e => hneg (Int64.lt_iff_toInt_lt.mpr (by simpa using e))
          have a3 : lp.ret ≠ 0 := by simpa using hne0
          exact a3 (Int64.toInt_inj.mp (by simp; omega))
        · have h1 : s.size.toNat ≠ 0 := fun e => hsz (UInt32.toNat_inj.mp (by simpa using e))
          rw [hlen] at hle; omega
      have t := tail s.eof (Or.inr hpos)
      have es : ({ s with eof := s.eof } : GzState) = s := rfl
      rw [es, DeflateReset.upd_self w.gzs b s (gzs_of hs)] at t
      exact GSat.pure t

/-- **`gz_avail` with its read measure**: everything `gz_avail_spec` gives (`AvailPost`), and on a return of 0
(`AvailBudget`) only `next_in` and `avail_in` of the stream changed, `rdLeft + avail_in` did not grow, and there is
input in the buffer or `eof` is set. -/
theorem gz_avail_budget {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) (hnc : s.how ≠ ZlibNg.Gz.COPY) {z0 : ZStream} (hz0 : h.streams s.strm = some z0) :
    GSat w h (gz_avail (some b)) (fun r W H => AvailPost w h b s r W H ∧ AvailBudget w b s z0 r W H) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨c, base, z, hB, -, hz, -, hai, -⟩ := (sh.read hr).bufs hsz
  have ez : z = z0 := Option.some.inj (hz.symm.trans hz0)
  subst ez
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  have done0 : (s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR) → s.eof ≠ 0 → AvailPost w h b s 0 w h ∧ AvailBudget w b s z 0 w h :=
    fun hok he => ⟨⟨Or.inr rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩,
      fun _ => ⟨s, z, hs, hz, rfl, Nat.le_refl _, Or.inr he⟩, fun e => absurd e (by decide),
      fun _ => ⟨hok, fun s2 h2 => by rw [hs] at h2; cases h2; rfl⟩⟩
  have tail : ∀ H, HBuf h H c base (base + inSize s) → (s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR) →
      GSat w H (availTail (some b) (some s.strm)) (fun r W H' => AvailPost w h b s r W H' ∧ AvailBudget w b s z r W H') := by
    intro H x hok
    have hsH : w.gz H b = some s := by rw [x.gz hcb]; exact hs
    have g : GStep w h w H b [] := by
      have := gstep_hbuf hs x hcb hown w.fs s rfl rfl rfl rfl
      rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
      exact this
    exact (availTail_budget hv hs h0 hsz hnc hB hz hai x hok).mono fun r W H' p => ⟨AvailPost.pre g hs hsH p.1, p.2⟩
  unfold gz_avail
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨⟨Or.inl rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩, fun e => absurd e (by decide),
      fun _ => hz, fun e => absurd e (by decide)⟩
  · intro hok0
    have hok : s.err = ZlibNg.Inflate.Z_OK ∨ s.err = ZlibNg.Inflate.Z_BUF_ERROR := by
      by_cases e1 : s.err = ZlibNg.Inflate.Z_OK
      · exact Or.inl e1
      · right; simpa [e1] using hok0
    refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
    apply GSat.ite
    · intro _
      refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
      apply GSat.ite
      · intro hne
        have hne' : z.avail_in ≠ 0 := by simpa using hne
        obtain ⟨k, hnx, -, hkn⟩ := hai.resolve_left hne'
        refine GSat.bind (GSat.of_eq (ldGz_app hs) ?_)
        refine GSat.bind (GSat.lm ⟨.ref (.heap c) base, h, (by show Ival.get s.«in» _ = _; rw [hB.inp]; rfl), ?_⟩)
        refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
        apply GSat.ite
        · intro _
          refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz _, ?_⟩)
          rw [hnx]
          refine GSat.bind (GSat.mono (copy_spec hd (base := base) (j := k) z.avail_in hne' (by omega))
            fun _ W H q => ?_)
          obtain ⟨rfl, x⟩ := q
          exact tail H ((HBuf.refl h c base (base + inSize s)).trans x (Nat.le_refl _) (by omega)) hok
        · intro _; exact tail h (HBuf.refl _ _ _ _) hok
      · intro _; exact tail h (HBuf.refl _ _ _ _) hok
    · intro he; exact GSat.pure (done0 hok (by simpa using he))


/-! ## The output target of `gz_decomp` and the buffers of `inflate` -/

/-- The output target of `gz_decomp`: `n` bytes at offset `oo` of heap block `bo`, inside the `out` buffer of the file
(`gz_fetch`) or outside every block of the file (`gz_read`, the caller's buffer). -/
def OutTgt (w : World) (h : Heap) (b : Nat) (s : GzState) (bo oo n : Nat) : Prop :=
  (∃ c base, GzBufs h s c base ∧ bo = c ∧ base + inSize s ≤ oo ∧ oo + n ≤ base + inSize s + outSize s) ∨
  (bo ∉ GzOwned w h (some b) ∧ ∃ d, h.bytes bo = some d ∧ oo + n ≤ d.size)

theorem owned_st {W : World} {H : Heap} {b : Nat} {s : GzState} (hs : W.gz H b = some s) {z : ZStream}
    (hz : H.streams s.strm = some z) {sb : Nat} (hsb : z.state = some sb) : sb ∈ GzOwned W H (some b) := by
  simp [GzOwned, hs, hz, hsb]

theorem owned_buf {W : World} {H : Heap} {b : Nat} {s : GzState} (hs : W.gz H b = some s) {c base : Nat}
    (hB : s.buffers = .val (.ref (.heap c) base)) : c ∈ GzOwned W H (some b) := by
  simp [GzOwned, hs, hB]

/-- The buffers of the stream of a read handle are valid for `inflate` when it has input and its output lies in the
target. -/
theorem streamIO_gz {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (hsz : s.size ≠ 0) {z : ZStream} (hz : H.streams s.strm = some z)
    (hin : z.avail_in ≠ 0) {bo oo n k : Nat} (ht : OutTgt W H b s bo oo n)
    (hno : z.next_out = .ref (.heap bo) (oo + k)) (hk : k + z.avail_out.toNat ≤ n) :
    StreamIO H (some s.strm) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨c, base, z0, hB, hI, hz0, -, hai, hreg, -⟩ := (sh.read hr).bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨i, z1, sb, st, al, e, hz1, hsb, hst1, hal, core⟩ := hI
  cases e
  rw [hz] at hz1; cases hz1
  have hsbS : sb ∈ stBlk H s := stBlk_of hz hsb
  have hsbO : sb ∈ GzOwned W H (some b) := owned_st hs hz hsb
  have hcsb : c ≠ sb := fun e => hst (e ▸ hsbS)
  have hhead : st.head = .val none := by
    rcases core.head with e | ⟨k', g, e, -⟩
    · exact e
    · have := hreg (some k') ⟨sb, st, ⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst1, e⟩; cases this
  obtain ⟨ki, hni, -, hki⟩ := hai.resolve_left hin
  obtain ⟨d, hd, hds⟩ := hB.fits
  -- the output range
  have hout : ∃ dO, H.bytes bo = some dO ∧ oo + n ≤ dO.size ∧ bo ≠ sb ∧
      (bo ≠ c ∨ base + inSize s ≤ oo) := by
    rcases ht with ⟨c', base', hB', e1, h1, h2⟩ | ⟨hno', dO, hdO, hsz'⟩
    · have e2 := hB'.buffers; rw [hB.buffers] at e2; cases e2
      subst e1
      exact ⟨d, hd, by omega, hcsb, Or.inr h1⟩
    · refine ⟨dO, hdO, hsz', fun e => hno' (e ▸ hsbO), Or.inl fun e => hno' (e ▸ owned_buf hs hB.buffers)⟩
  obtain ⟨dO, hdO, hdOs, hbsb, hbc⟩ := hout
  refine ⟨z, sb, none, ⟨_, rfl, hz⟩, hsb, ⟨sb, st, ⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst1, hhead⟩, Or.inl rfl,
    Or.inr ⟨.heap c, base + ki, d, hni, hd, by omega⟩, Or.inr ⟨bo, oo + k, dO, hno, hdO, by omega⟩, ?_, ?_⟩
  · intro x y u v hxy hu hv'
    have hd1 : Disjoint z.next_in z.avail_in.toNat z.next_out z.avail_out.toNat := by
      rw [hni, hno]; simp only [Disjoint]
      rcases hbc with e | e
      · exact Or.inl fun e' => e (by cases e'; rfl)
      · exact Or.inr (Or.inl (by omega))
    have hd2 : Disjoint z.next_out z.avail_out.toNat z.next_in z.avail_in.toNat := by
      rw [hni, hno]; simp only [Disjoint]
      rcases hbc with e | e
      · exact Or.inl fun e' => e (by cases e'; rfl)
      · exact Or.inr (Or.inr (by omega))
    simp only [headerRanges] at hu hv'
    rcases x with _ | _ | x <;> rcases y with _ | _ | y <;> simp at hu hv' hxy
    · subst hu; subst hv'; exact hd1
    · subst hu; subst hv'; exact hd2
  · intro r hr'
    simp only [headerRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · intro off e; rw [hni] at e; cases e; exact hcsb rfl
    · intro off e; rw [hno] at e; cases e; exact hbsb rfl

/-- The inflate state of the stream of `s` is just reset (`inflateReset`): mode `HEAD`, no bits held, not the last
block. -/
def InflFresh (H : Heap) (s : GzState) : Prop :=
  ∃ z sb st, H.streams s.strm = some z ∧ z.state = some sb ∧ H.istate sb = some st ∧
    st.mode = ZlibNg.Inflate.HEAD ∧ st.bits = 0 ∧ st.last = 0

/-! ## One call of `inflate` on a read handle -/

/-- A frame protects fewer bytes when every byte outside `W'` is outside `W`. -/
theorem frame_wcover {h h' : Heap} {S B G : List Nat} {W W' : List (BPtr × Nat)} (f : Frame h h' S B G W)
    (hW : ∀ c j, (∀ w ∈ W', ∀ off, w.1 = .ref (.heap c) off → j < off ∨ off + w.2 ≤ j) →
      ∀ w ∈ W, ∀ off, w.1 = .ref (.heap c) off → j < off ∨ off + w.2 ≤ j) : Frame h h' S B G W' := by
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := f
  refine ⟨s1, g1, i1, fun c hc hn data hd => ?_, n1, c1, r1, x1, a1, k1⟩
  obtain ⟨d2, f2, s2, q2⟩ := b1 c hc hn data hd
  exact ⟨d2, f2, s2, fun j hj hw => q2 j hj (hW c j hw)⟩

/-- A block outside the library blocks and the write ranges keeps its bytes. -/
theorem frame_keep_blk {h h' : Heap} {S L G : List Nat} {W : List (BPtr × Nat)} (f : Frame h h' S L G W) {c : Nat}
    (hc : c < h.nextBlk) (hl : c ∉ L) (hw : ∀ w ∈ W, ∀ off, w.1 ≠ .ref (.heap c) off) {d : Array UInt8}
    (hd : h.bytes c = some d) : h'.bytes c = some d := by
  obtain ⟨d', e, sz, q⟩ := f.2.2.2.1 c hc hl d hd
  rw [e]; congr 1
  apply Array.ext sz
  intro j h1 h2
  have := q j h2 fun w hw' off he => absurd he (hw w hw' off)
  rwa [getElem!_pos d' j h1, getElem!_pos d j h2] at this

/-- A live block outside the library blocks stays live with its size. -/
theorem frame_live {h h' : Heap} {S L G : List Nat} {W : List (BPtr × Nat)} (f : Frame h h' S L G W) {c : Nat}
    (hc : c < h.nextBlk) (hl : c ∉ L) {d : Array UInt8} (hd : h.bytes c = some d) :
    ∃ d', h'.bytes c = some d' ∧ d'.size = d.size := by
  obtain ⟨d', e, sz, -⟩ := f.2.2.2.1 c hc hl d hd
  exact ⟨d', e, sz⟩

open ZlibNg.Inflate in
/-- **`inflate(strm, Z_NO_FLUSH)` on a read handle** with input and its output in the target: the handle stays a
read handle (the state of the file is not touched), the call is a step that writes only the target, and the stream
moved `next_in` and `next_out` by the bytes it consumed and wrote. -/
theorem inflate_gz (G : InflateGz) (M : InflateMsg) {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (hsz : s.size ≠ 0) (h0 : s.«have» = 0) (hhow : s.how = GZIP) {z : ZStream}
    (hz : H.streams s.strm = some z) (hin : z.avail_in ≠ 0) (hout : z.avail_out ≠ 0) {bo oo n k : Nat} (ht : OutTgt W H b s bo oo n)
    (hno : z.next_out = .ref (.heap bo) (oo + k)) (hk : k + z.avail_out.toNat ≤ n) :
    GSat W H (lm (inflate (some s.strm) ZlibNg.Deflate.Z_NO_FLUSH)) (fun r W' H' => W' = W ∧
      GzInvR W H' (some b) ∧ W.gz H' b = some s ∧ GStep W H W H' b [(.ref (.heap bo) oo, n)] ∧
      (r = Z_OK ∨ r = Z_STREAM_END ∨ r = Z_NEED_DICT ∨ r = Z_BUF_ERROR ∨ r = Z_DATA_ERROR ∨ r = Z_STREAM_ERROR) ∧
      (r = Z_OK → ∃ z', H'.streams s.strm = some z' ∧
        z'.avail_in.toNat + z'.avail_out.toNat < z.avail_in.toNat + z.avail_out.toNat) ∧
      (∃ z', H'.streams s.strm = some z' ∧ z'.state = z.state ∧ z'.avail_out ≤ z.avail_out ∧
        z'.next_out = .ref (.heap bo) (oo + k + (z.avail_out - z'.avail_out).toNat) ∧
        z'.avail_in ≤ z.avail_in ∧ (r ≠ Z_BUF_ERROR)) ∧
      (InflateFresh → InflFresh H s → r = Z_STREAM_END → ∀ z', H'.streams s.strm = some z' →
        z'.avail_in < z.avail_in)) := by
  have hio := streamIO_gz hv hs hsz hz hin ht hno hk
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  have R := sh.read hr
  obtain ⟨c, base, z0, hB, hI, hz0, -, hai, hreg, hmsg0⟩ := R.bufs hsz
  rw [hz] at hz0; cases hz0
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  have hI' := hI
  obtain ⟨i, z1, sb, st, al, e, hz1, hsb, hst1, hal, core⟩ := hI'
  cases e
  rw [hz] at hz1; cases hz1
  have hhead : st.head = .val none := by
    rcases core.head with e | ⟨k', g, e, -⟩
    · exact e
    · have := hreg (some k') ⟨sb, st, ⟨z, ⟨_, rfl, hz⟩, hsb⟩, hst1, e⟩; cases this
  have hw := hv.2.2
  have hcrc : H.crcTable = ZlibNg.Crc32Tbl.crc_table := hw.1.1
  have fr : FreshBlocks H := hw.2.1.1
  obtain ⟨r, H', e, hInv', F, -, -, hreg'⟩ := InflateTop.inflate_ok ZlibNg.Deflate.Z_NO_FLUSH hI hio hcrc
  obtain ⟨hdst, hdal, -, hfr', hsaved, -⟩ := GzRead.inflateExtra.ok H s.strm _ r H' hI hio hcrc e
  have hsid : stateIds H (some s.strm) = [sb] := InflateReach.stateIds_of hz hsb
  have hhid : headerIds H (some s.strm) = [] := by
    have := InflateTop.headerIds_eq hz hsb hst1 hhead; simpa using this
  have hor : outputRanges H (some s.strm) = [(z.next_out, z.avail_out.toNat)] := by
    rw [InflateTop.outputRanges_eq hz hsb hst1 hhead]; rfl
  rw [hsid, hhid, hor] at F
  obtain ⟨ki, hni, -, hki⟩ := hai.resolve_left hin
  obtain ⟨z', hz', hzs, hinat, hao, bo', oo', e1, e2⟩ := G.io' H s.strm _ r H' hI hio hcrc e z hz
    (by rw [hno]; exact fun e => by cases e) (Or.inr (by rw [hni]; exact fun e => by cases e))
  rw [hno] at e1; cases e1
  have hres := G.res H s.strm _ r H' hI hio hcrc e
  have hnb : r ≠ Z_BUF_ERROR := InflateExtra.inflate_no_buf_error hI hio hcrc e hz hin hout
  have hprog : r = Z_OK → ∃ z', H'.streams s.strm = some z' ∧
      z'.avail_in.toNat + z'.avail_out.toNat < z.avail_in.toNat + z.avail_out.toNat := by
    intro hr0
    obtain ⟨z2, h1, -, -, h4⟩ := InflateExtra.inflate_ok_progress hI hio hcrc e hz hr0
    exact ⟨z2, h1, h4⟩
  -- the input after the call
  obtain ⟨hain, hnx⟩ := hinat
  rw [hni] at hnx
  simp only at hnx
  -- blocks
  have hlt : ∀ c', (∃ d, H.bytes c' = some d) → c' < H.nextBlk := fun c' hc' => live_lt fr hc'
  have hsbS : sb ∈ stBlk H s := stBlk_of hz hsb
  have hsbO : sb ∈ GzOwned W H (some b) := owned_st hs hz hsb
  have hcsb : c ≠ sb := fun e => hst (e ▸ hsbS)
  obtain ⟨db, hdb⟩ := gz_live hs
  have hbsb : b ≠ sb := by
    intro e'; subst e'
    have hm : b ∈ ownL H b s := by simp [ownL]
    have hm2 : b ∈ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk H s) := by simp [hsz, hsbS]
    have e3 : ownL H b s = ([b] ++ blkOf s.path ++ blkOf s.msg) ++ (if s.size = 0 then [] else blkOf s.buffers ++ stBlk H s) := rfl
    rw [e3] at hn
    exact (List.nodup_append.mp hn).2.2 b (by simp) b hm2 rfl
  -- the target block is not the state block, and a block of the file other than the buffers is not the target
  have hbo : bo ≠ sb ∧ ∀ c', c' ∈ GzOwned W H (some b) → c' ≠ c → c' ≠ bo := by
    rcases ht with ⟨c', base', hB', e1, -, -⟩ | ⟨hno', -⟩
    · have e2 := hB'.buffers; rw [hB.buffers] at e2; cases e2
      subst e1
      exact ⟨hcsb, fun c'' _ hne => hne⟩
    · exact ⟨fun e' => hno' (e' ▸ hsbO), fun c'' hc'' _ e' => hno' (e' ▸ hc'')⟩
  have hwr : ∀ c', c' ≠ bo → ∀ w ∈ [(z.next_out, z.avail_out.toNat)], ∀ off, w.1 ≠ .ref (.heap c') off := by
    intro c' hc' w hw' off e'
    simp only [List.mem_singleton] at hw'; subst hw'
    rw [hno] at e'; cases e'; exact hc' rfl
  have keepB : ∀ c', c' ≠ sb → c' ≠ bo → ∀ d, H.bytes c' = some d → H'.bytes c' = some d := fun c' h1 h2 d hd =>
    frame_keep_blk F (hlt c' ⟨d, hd⟩) (by simp [h1]) (hwr c' h2) hd
  have liveB : ∀ c', c' ≠ sb → ∀ d, H.bytes c' = some d → ∃ d', H'.bytes c' = some d' ∧ d'.size = d.size :=
    fun c' h1 d hd => frame_live F (hlt c' ⟨d, hd⟩) (by simp [h1]) hd
  have hstH' : stBlk H' s = stBlk H s := by simp [stBlk, hz, hz', hzs]
  have hown' : ownL H' b s = ownL H b s := by simp only [ownL, hstH']
  -- the state of the file
  have hsH' : W.gz H' b = some s := by
    obtain ⟨db', hdb', -⟩ := liveB b hbsb db hdb
    unfold World.gz at hs ⊢; rw [hdb']; rw [hdb] at hs; exact hs
  -- the blocks of `path` and `msg` are neither the state block nor the target
  have hpm : ∀ x ∈ blkOf s.path ++ blkOf s.msg, x ≠ sb ∧ x ≠ bo := by
    intro x hx
    have e3 : ownL H b s = ([b] ++ (blkOf s.path ++ blkOf s.msg)) ++ (blkOf s.buffers ++ stBlk H s) := by
      simp [ownL, hsz]
    have hn' := hn; rw [e3] at hn'
    have hd := (List.nodup_append.mp hn').2.2 x (List.mem_append_right _ hx)
    have hxc : x ≠ c := fun e' => hd c (by simp [hB.buffers, blkOf]) e'
    refine ⟨fun e' => hd sb (List.mem_append_right _ hsbS) e', hbo.2 x (ownL_owned hs x ?_) hxc⟩
    rw [e3]; exact List.mem_append_left _ (List.mem_append_right _ hx)
  have hbytesEq : ∀ x, x ≠ sb → x ≠ bo → (∃ d, H.bytes x = some d) → H'.bytes x = H.bytes x := by
    intro x h1 h2 ⟨d, hd⟩; rw [keepB x h1 h2 d hd, hd]
  obtain ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ := F
  have hshape : GzShape H' s := by
    refine ⟨sh.mode, ?_, ⟨z', hz'⟩, sh.want_lo, sh.want_hi, sh.size, sh.pos, ⟨?_, sh.msg.mem⟩, fun _ => ?_,
      fun hw' => absurd (hr.symm.trans hw') read_ne_write, fun hz0 => absurd hz0 hsz⟩
    · refine ownStr_keep sh.path fun x hx => ?_
      obtain ⟨h1, h2⟩ := hpm x (List.mem_append_left _ hx)
      obtain ⟨pc, nn, ep, r0, off0, d0, e0, hd0, -⟩ := sh.path
      rw [ep] at hx; simp [blkOf] at hx; subst hx; cases e0
      exact hbytesEq _ h1 h2 ⟨d0, hd0⟩
    · rcases sh.msg.msg with em | ⟨mc, d, em, hd⟩
      · exact Or.inl em
      · have hx : mc ∈ blkOf s.path ++ blkOf s.msg := by simp [em, blkOf]
        obtain ⟨d', e', -⟩ := liveB mc (hpm mc hx).1 d hd
        exact Or.inr ⟨mc, d', em, e'⟩
    · refine ⟨R.how, fun _ => ?_, R.nobuf, R.skip_have, fun hz0 => absurd hz0 hsz, fun hz0 => absurd hz0 hsz,
        R.pos_have, R.look_pos, R.gzip_direct, fun e => absurd (e.symm.trans hhow) (by decide)⟩
      obtain ⟨d, hd, hds⟩ := hB.fits
      obtain ⟨d', e', sz'⟩ := liveB c hcsb d hd
      have hsv : H'.savedPtrs c = H.savedPtrs c := hsaved c fun z2 hz2 => by
        rw [hz] at hz2; cases hz2; rw [hsb]; exact fun e4 => hcsb (Option.some.inj e4).symm
      refine ⟨c, base, z', ⟨hB.size, hB.buffers, hB.inp, hB.out, ⟨d', e', by rw [sz']; exact hds⟩, hB.hdr.1,
        by rw [hsv]; exact hB.hdr.2⟩, hInv', hz', Or.inl h0, ?_, fun hp hr' => hreg hp (hreg' hp hr'), ?_⟩
      · by_cases ha0 : z'.avail_in = 0
        · exact Or.inl ha0
        · right
          have hsub : (z.avail_in - z'.avail_in).toNat = z.avail_in.toNat - z'.avail_in.toNat :=
            UInt32.toNat_sub_of_le _ _ hain
          have hle : z'.avail_in.toNat ≤ z.avail_in.toNat := UInt32.le_iff_toNat_le.mp hain
          refine ⟨ki + (z.avail_in - z'.avail_in).toNat, by rw [hnx, Nat.add_assoc], Nat.zero_le _, ?_⟩
          rw [hsub]; omega
      · obtain ⟨z3, hz3, hm3⟩ := M.msg H s.strm _ r H' hI hio hcrc e z hz
        rw [hz'] at hz3; cases hz3
        rcases hm3 with hm3 | hm3
        · rw [hm3]; exact hmsg0
        · exact Or.inr hm3
  have hw' : GzWFr W H' := by
    obtain ⟨hc, ⟨hfr, hdf⟩, hgz, hst', hb', hnd, hlk, hL⟩ := hw
    refine ⟨⟨by rw [r1]; exact hc.1, by rw [x1]; exact hc.2⟩, ⟨hfr' hfr, fun c' hc' => by
      rw [hdst, hdal]; exact hdf c' (Nat.le_trans k1 hc')⟩, fun c' hc' => hgz c' (Nat.le_trans k1 hc'),
      fun c' s2 e' => ?_, hb', hnd, hlk, LitOk.ext hL rfl fun k a e4 => by rw [c1]; exact e4⟩
    have hs2 : W.gz H c' = some s2 := by
      have hsbl : ∃ d, H.bytes sb = some d := by
        unfold Heap.istate at hst1; split at hst1
        · next d hd => exact ⟨d, hd⟩
        · cases hst1
      unfold World.gz at e' ⊢
      cases hH' : H'.bytes c' with
      | none => rw [hH'] at e'; cases e'
      | some d' =>
        rw [hH'] at e'
        cases hH : H.bytes c' with
        | some d => exact e'
        | none =>
          by_cases hlt' : c' < H.nextBlk
          · have hne : c' ∉ [sb] := by
              intro m; simp at m; subst m; obtain ⟨d, hd⟩ := hsbl; rw [hH] at hd; cases hd
            rw [n1 c' hlt' hne hH] at hH'; cases hH'
          · rw [hgz c' (by omega)] at e'; cases e'
    obtain ⟨z2, hz2⟩ := hst' c' s2 hs2
    by_cases hi : s2.strm = s.strm
    · rw [hi]; exact ⟨z', hz'⟩
    · exact ⟨z2, by rw [s1 _ (by simp [hi])]; exact hz2⟩
  have hInvR : GzInvR W H' (some b) :=
    ⟨⟨b, s, rfl, hsH', hshape, by rw [hown']; exact hn⟩, ⟨b, s, rfl, hsH', hr⟩, hw'⟩
  have hstep : GStep W H W H' b [(.ref (.heap bo) oo, n)] := by
    refine ⟨⟨⟨?_, fun c' _ _ => ⟨by simp [hdst], by simp [hdal]⟩⟩, fun k a e4 => by rw [c1]; exact e4,
      fun b' _ _ => rfl⟩, fun c' hc' _ => ?_, fun s1' s2' e1' e2' => ?_⟩
    · simp only [hs]
      have F2 : Frame H H' [s.strm] (GzOwned W H (some b)) [] [(.ref (.heap bo) oo, n)] := by
        refine frame_wcover (InflateLoop.Frame.mono ⟨s1, g1, i1, b1, n1, c1, r1, x1, a1, k1⟩ (fun _ m => m)
          (fun x m => by simp at m; subst m; exact hsbO) (fun _ m => m) (fun _ m => m)) ?_
        intro c' j hcov w hw0 off he
        simp only [List.mem_singleton] at hw0; subst hw0
        simp only at he
        rw [hno] at he; cases he
        have := hcov _ (List.mem_singleton_self _) oo rfl
        simp only at this ⊢; omega
      rwa [show ({ H' with consts := H.consts } : Heap) = H' by rw [← c1]]
    · have : GzOwned W H' (some b) = GzOwned W H (some b) := by simp [GzOwned, hsH', hs, hz', hz, hzs]
      rw [this] at hc'; exact hc'
    · rw [hs] at e1'; rw [hsH'] at e2'; cases e1'; cases e2'; rfl
  refine ⟨r, W, H', by simp [e], rfl, hInvR, hsH', hstep, hres, hprog, ⟨z', hz', hzs, hao, e2, hain, hnb⟩, ?_⟩
  intro FF ⟨z5, sb5, st5, hz5, hsb5, hst5, hm5, hb5, hl5⟩ hse z6 hz6
  rw [hz] at hz5; cases hz5
  exact FF.fresh_end H s.strm _ r H' hI hio hcrc e z sb5 st5 hz hsb5 hst5 hm5 hb5 hl5 hse z6 hz6

/-- `gz_error(state, e, msg)` on a read handle, with the stream kept. -/
theorem err_strm {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (e : Int32) (msg : BPtr) (hmsg : msg = .null ∨ CStr h msg)
    (hmk : ∀ c o, msg ≠ .ref (.heap c) o) :
    GSat w h (gz_error (some b) e msg) (fun _ W H => ∃ s', W.gz H b = some s' ∧ ErrOf s e s' ∧
      GzInvR W H (some b) ∧ W.fs = w.fs ∧ GStep w h W H b [] ∧ H.streams = h.streams) :=
  GSat.mono (GSat.and (gz_error_inv hv hs e msg hmsg hmk) (gz_error_strm hv hs e msg hmsg hmk))
    fun _ _ _ q => by
      obtain ⟨⟨s', a1, a2, a3, -, a5, a6⟩, a7⟩ := q
      exact ⟨s', a1, a2, a3, a5, a6, a7⟩

/-- `gz_error(state, e, lit)` with a literal of the table on a read handle, with the stream kept. -/
theorem errlit_strm {W : World} {H : Heap} {b : Nat} {s : GzState} (hv : GzInvR W H (some b))
    (hs : W.gz H b = some s) (e : Int32) (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i)
    (hn : NoNul lit) :
    GSat W H (gzLit lit) (fun p W2 H2 => GSat W2 H2 (gz_error (some b) e p) (fun _ W' H' =>
      ∃ s', W'.gz H' b = some s' ∧ ErrOf s e s' ∧ GzInvR W' H' (some b) ∧ W'.fs = W.fs ∧ GStep W H W' H' b [] ∧
        H'.streams = H.streams)) := by
  refine (GSat.mono (gzLit_spec lit i hi (GzReach.gzLits_of_idx hi) hn hv.2.2.lit) fun p W2 H2 q => ?_)
  obtain ⟨hg, hf, x, hL, hcs, hmk⟩ := q
  obtain ⟨hs2, hv2, g2⟩ := ext_step hv hs hg hf x hL
  refine GSat.mono (err_strm hv2 hs2 e p (Or.inr ⟨_, hcs⟩) hmk) fun _ W' H' q => ?_
  obtain ⟨s', h1, h2, h3, h5, h6, h7⟩ := q
  exact ⟨s', h1, h2, h3, by rw [h5, hf], g2.trans h6 ⟨s, hs⟩ ⟨s, hs2⟩, h7.trans x.streams⟩

/-! ## `gz_decomp` -/

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The body of the loop of `gz_decomp` (copied from the translation). -/
def decompBody (state : GzPtr) (strm : StreamPtr) (s : DecompLoop) : G DecompLoop := do
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    if (← gz_avail state) == -1 then
      return { s with ctl := .ret }
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    gz_error state Z_BUF_ERROR (← (gzLit "unexpected end of file"))
    return { s with ctl := .brk }
  let ret ← lm (inflate strm Z_NO_FLUSH)
  if ret == Z_STREAM_ERROR || ret == Z_NEED_DICT then
    gz_error state Z_STREAM_ERROR (← (gzLit "internal error: inflate stream corrupt"))
    return { s with ret := ret, ctl := .ret }
  if ret == Z_MEM_ERROR then
    gz_error state Z_MEM_ERROR (← (gzLit "out of memory"))
    return { s with ret := ret, ctl := .ret }
  if ret == Z_DATA_ERROR then
    let m ← lm (rdZ strm (·.msg))
    gz_error state Z_DATA_ERROR (← if m == .null then (gzLit "compressed data error") else lm (rdZ strm (·.msg)))
    return { s with ret := ret, ctl := .ret }
  return { s with ret := ret }

open ZlibNg.Inflate in
/-- The condition of the loop of `gz_decomp` (copied from the translation). -/
def decompCond (strm : StreamPtr) (s : DecompLoop) : G (Bool × DecompLoop) := do
  if s.ctl != .go then return (false, s)
  return ((← lm (rdZ strm (·.avail_out))) != 0 && s.ret != Z_STREAM_END, s)

open ZlibNg.Inflate in
/-- The part of `gz_decomp` after the loop (copied from the translation). -/
def decompTail (state : GzPtr) (strm : StreamPtr) (had : UInt32) (lp : DecompLoop) : G Int32 := do
  if lp.ctl == .ret then
    return -1
  let ao ← lm (rdZ strm (·.avail_out))
  wrG state fun s => { s with «have» := had - ao }
  let nx ← lm ((← lm (rdZ strm (·.next_out))).add (-(Int.ofNat (← rdG state (·.«have»)).toNat)))
  wrG state fun s => { s with next := .val nx }
  if lp.ret == Z_STREAM_END then
    wrG state fun s => { s with how := LOOK }
  return 0

open ZlibNg.Inflate in
theorem gz_decomp_eq (state : GzPtr) : gz_decomp state = (do
    let strm ← strmOf state
    let had ← lm (rdZ strm (·.avail_out))
    let lp ← gdoWhile (decompBody state strm) (decompCond strm) ⟨Z_OK, .go⟩
    decompTail state strm had lp) := by
  unfold gz_decomp decompBody decompCond decompTail; rfl

open ZlibNg.Inflate ZlibNg.Deflate in
/-- The part of the loop body of `gz_decomp` after `gz_avail` (copied from the translation). -/
def decompRest (state : GzPtr) (strm : StreamPtr) (s : DecompLoop) : G DecompLoop := do
  if (← lm (rdZ strm (·.avail_in))) == 0 then
    gz_error state Z_BUF_ERROR (← (gzLit "unexpected end of file"))
    return { s with ctl := .brk }
  let ret ← lm (inflate strm Z_NO_FLUSH)
  if ret == Z_STREAM_ERROR || ret == Z_NEED_DICT then
    gz_error state Z_STREAM_ERROR (← (gzLit "internal error: inflate stream corrupt"))
    return { s with ret := ret, ctl := .ret }
  if ret == Z_MEM_ERROR then
    gz_error state Z_MEM_ERROR (← (gzLit "out of memory"))
    return { s with ret := ret, ctl := .ret }
  if ret == Z_DATA_ERROR then
    let m ← lm (rdZ strm (·.msg))
    gz_error state Z_DATA_ERROR (← if m == .null then (gzLit "compressed data error") else lm (rdZ strm (·.msg)))
    return { s with ret := ret, ctl := .ret }
  return { s with ret := ret }

open ZlibNg.Inflate in
theorem decompBody_eq (state : GzPtr) (strm : StreamPtr) (s : DecompLoop) : decompBody state strm s = (do
    let a ← lm (rdZ strm (·.avail_in))
    if a == 0 then do
      let r ← gz_avail state
      if r == -1 then pure { s with ctl := .ret } else decompRest state strm s
    else decompRest state strm s) := rfl

/-- A step that writes nothing writes inside any ranges. -/
theorem GStep.widen {w W : World} {h H : Heap} {b : Nat} (g : GStep w h W H b []) (wr : List (BPtr × Nat)) :
    GStep w h W H b wr := by
  obtain ⟨⟨⟨f1, f2⟩, c, gz⟩, o, t⟩ := g
  exact ⟨⟨⟨frame_wcover f1 (fun _ _ _ _ hw => nomatch hw), f2⟩, c, gz⟩, o, t⟩

/-- The output target stays one over a step of the file. -/
theorem OutTgt.step {W W' : World} {H H' : Heap} {b : Nat} {s s' : GzState} {bo oo n : Nat} {wr : List (BPtr × Nat)}
    (ht : OutTgt W H b s bo oo n) (g : GStep W H W' H' b wr) (hv' : GzInvR W' H' (some b))
    (hs' : W'.gz H' b = some s') (hbuf : s'.buffers = s.buffers) (hin : inSize s' = inSize s)
    (hout : outSize s' = outSize s) (fr : FreshBlocks H) (hsz : s'.size ≠ 0) : OutTgt W' H' b s' bo oo n := by
  rcases ht with ⟨c, base, hB, e1, h1, h2⟩ | ⟨hno, d, hd, hds⟩
  · obtain ⟨sh, -⟩ := inv_of hs' hv'.1
    obtain ⟨c', base', -, hB', -⟩ := (sh.read (modeOf hs' hv'.2.1)).bufs hsz
    have e2 := hB'.buffers; rw [hbuf, hB.buffers] at e2; cases e2
    exact Or.inl ⟨c, base, hB', e1, by rw [hin]; exact h1, by rw [hin, hout]; exact h2⟩
  · have hlt : bo < H.nextBlk := live_lt fr ⟨d, hd⟩
    obtain ⟨⟨⟨f1, -⟩, -, -⟩, own, -⟩ := g
    obtain ⟨d', e', sz', -⟩ := f1.2.2.2.1 bo hlt hno d hd
    exact Or.inr ⟨fun m => hno (own bo m hlt), d', e', by rw [sz']; exact hds⟩

/-- The read measure of `gz_decomp`: what reads may still deliver, the input in the buffer, and the room left. -/
def dmu (s : GzState) (W : World) (H : Heap) : Nat :=
  rdLeft W.fs s.fd + match H.streams s.strm with
    | some z => z.avail_in.toNat + z.avail_out.toNat
    | none => 0

theorem dmu_of {s : GzState} {W : World} {H : Heap} {z : ZStream} (hz : H.streams s.strm = some z) :
    dmu s W H = rdLeft W.fs s.fd + z.avail_in.toNat + z.avail_out.toNat := by
  simp only [dmu, hz, Nat.add_assoc]

/-- The state of `gz_decomp` between two calls of `inflate`: a read handle whose state differs from `s` at most in
`eof`, `err` and `msg`, a step that wrote only the output target, the stream's output position `had - avail_out`
bytes into the target. -/
def DMid (w : World) (h : Heap) (b : Nat) (s : GzState) (bo oo had : Nat) (W : World) (H : Heap) (s' : GzState)
    (z : ZStream) : Prop :=
  GzInvR W H (some b) ∧ GStep w h W H b [(.ref (.heap bo) oo, had)] ∧ FsRd w.fs W.fs ∧
  W.gz H b = some s' ∧ s' = { s with eof := s'.eof, err := s'.err, msg := s'.msg } ∧
  H.streams s.strm = some z ∧ z.avail_out.toNat ≤ had ∧
  z.next_out = .ref (.heap bo) (oo + (had - z.avail_out.toNat)) ∧ OutTgt W H b s' bo oo had

/-- The invariant of the loop of `gz_decomp`. `P0`: the stream had input and a just reset state at the call. -/
def DInv (w : World) (h : Heap) (b : Nat) (s : GzState) (bo oo had : Nat) (P0 : Prop) (st : DecompLoop)
    (W : World) (H : Heap) : Prop :=
  st.ctl = .go ∧ st.ret ≠ ZlibNg.Inflate.Z_STREAM_END ∧ ∃ s' z, DMid w h b s bo oo had W H s' z ∧
    z.avail_out ≠ 0 ∧ dmu s W H ≤ dmu s w h ∧ (P0 → dmu s W H < dmu s w h ∨ (W = w ∧ H = h))

/-- An error return of the loop: a read handle whose state differs from `s` at most in `eof`, `err` and `msg`. -/
def DErr (w : World) (h : Heap) (b : Nat) (s : GzState) (bo oo had : Nat) (W : World) (H : Heap) : Prop :=
  GStep w h W H b [(.ref (.heap bo) oo, had)] ∧ FsRd w.fs W.fs ∧
  ∃ s', W.gz H b = some s' ∧ GzInvR W H (some b) ∧ s' = { s with eof := s'.eof, err := s'.err, msg := s'.msg }

/-- The exit of the loop of `gz_decomp`. -/
def DExit (w : World) (h : Heap) (b : Nat) (s : GzState) (bo oo had : Nat) (P0 : Prop) (lp : DecompLoop)
    (W : World) (H : Heap) : Prop :=
  (lp.ctl = .ret ∧ DErr w h b s bo oo had W H) ∨
  (lp.ctl ≠ .ret ∧ ∃ s' z, DMid w h b s bo oo had W H s' z ∧ dmu s W H ≤ dmu s w h ∧
    (lp.ret = ZlibNg.Inflate.Z_STREAM_END → InflateFresh → P0 → dmu s W H < dmu s w h) ∧
    (lp.ret ≠ ZlibNg.Inflate.Z_STREAM_END → z.avail_out = 0 ∨ (s'.eof ≠ 0 ∧ z.avail_in = 0)))

theorem shape_trans {s s1 s2 : GzState} (h1 : s1 = { s with eof := s1.eof, err := s1.err, msg := s1.msg })
    (h2 : s2 = { s1 with eof := s2.eof, err := s2.err, msg := s2.msg }) :
    s2 = { s with eof := s2.eof, err := s2.err, msg := s2.msg } := by
  cases s; cases s1; cases s2; simp only [GzState.mk.injEq] at h1 h2 ⊢; simp_all

theorem lit_eof : gzLits.findIdx? (· == "unexpected end of file") = some 2 := by simp [gzLits, List.findIdx?_cons]
theorem lit_corrupt : gzLits.findIdx? (· == "internal error: inflate stream corrupt") = some 3 := by
  simp [gzLits, List.findIdx?_cons]
theorem lit_data : gzLits.findIdx? (· == "compressed data error") = some 4 := by simp [gzLits, List.findIdx?_cons]

/-- A string literal of inflate is a string, not in a heap block. -/
theorem msg_cstr {H : Heap} {p : BPtr} (hp : p = .null ∨ ∃ k, p = .ref (.str k) 0 ∧ k < strTable.size) :
    (p = .null ∨ CStr H p) ∧ ∀ c o, p ≠ .ref (.heap c) o := by
  rcases hp with rfl | ⟨k, rfl, hk⟩
  · exact ⟨Or.inl rfl, fun _ _ e => by cases e⟩
  · refine ⟨Or.inr (cstr_push0 (a := (strTable[k]).toUTF8.data) ?_), fun _ _ e => by cases e⟩
    show Heap.getBytes H (.str k) = _
    simp [Heap.getBytes, Heap.litBytes, hk]

/-- An error return of the loop body after a step from `(W, H)`. -/
theorem derr_of {w : World} {h : Heap} {b : Nat} {s : GzState} {bo oo had : Nat} {W W2 : World} {H H2 : Heap}
    {s1 : GzState} {e : Int32} (hw0 : ∃ s0, w.gz h b = some s0) (g : GStep w h W H b [(.ref (.heap bo) oo, had)])
    (hfs : FsRd w.fs W.fs)
    (hs1 : W.gz H b = some s1) (hsh : s1 = { s with eof := s1.eof, err := s1.err, msg := s1.msg }) (h0 : s.«have» = 0)
    (q : ∃ s2, W2.gz H2 b = some s2 ∧ ErrOf s1 e s2 ∧ GzInvR W2 H2 (some b) ∧ W2.fs = W.fs ∧
      GStep W H W2 H2 b [] ∧ H2.streams = H.streams) : DErr w h b s bo oo had W2 H2 := by
  obtain ⟨s2, q1, q2, q3, q4, q5, -⟩ := q
  have h0' : s1.«have» = 0 := by rw [hsh]; exact h0
  exact ⟨g.trans (GStep.widen q5 _) hw0 ⟨s1, hs1⟩, by rw [q4]; exact hfs, s2, q1, q3,
    shape_trans hsh (errOf_shape q2 h0')⟩

open ZlibNg.Inflate in
/-- The loop body of `gz_decomp` after `gz_avail`, and the loop condition. -/
theorem rest_spec (G : InflateGz) (M : InflateMsg) {w : World} {h : Heap} {b : Nat} {s : GzState} {bo oo had : Nat}
    {P0 : Prop} (hP0 : P0 → InflFresh h s) (hw0 : ∃ s0, w.gz h b = some s0) (hsz : s.size ≠ 0) (h0 : s.«have» = 0)
    (hhow : s.how = GZIP) {st : DecompLoop} (hgo : st.ctl = .go) (hret : st.ret ≠ Z_STREAM_END)
    {W : World} {H : Heap} {s' : GzState} {z : ZStream} (m : DMid w h b s bo oo had W H s' z)
    (hout : z.avail_out ≠ 0) (heof : z.avail_in = 0 → s'.eof ≠ 0) {μ1 : Nat} (hμ1 : dmu s W H ≤ μ1)
    (hμ0 : dmu s W H ≤ dmu s w h) (hfr : P0 → dmu s W H < dmu s w h ∨ (W = w ∧ H = h)) :
    GSat W H (decompRest (some b) (some s.strm) st) (fun st1 W1 H1 => GSat W1 H1 (decompCond (some s.strm) st1)
      (fun cs W2 H2 => (cs.1 = true → DInv w h b s bo oo had P0 cs.2 W2 H2 ∧ dmu s W2 H2 < μ1) ∧
        (cs.1 = false → DExit w h b s bo oo had P0 cs.2 W2 H2))) := by
  obtain ⟨hv, g, hfs, hs', hsh, hz, hle, hno, ht⟩ := m
  have hsz' : s'.size ≠ 0 := by rw [hsh]; exact hsz
  have h0' : s'.«have» = 0 := by rw [hsh]; exact h0
  have hstrm : s'.strm = s.strm := by rw [hsh]
  have fr : FreshBlocks H := hv.2.2.2.1.1
  -- an error exit after the call of `inflate` (or before it)
  have exitErr : ∀ (r : Int32) (W1 : World) (H1 : Heap) (W2 : World) (H2 : Heap), DErr w h b s bo oo had W2 H2 →
      GSat W2 H2 (decompCond (some s.strm) { ret := r, ctl := .ret })
        (fun cs W3 H3 => (cs.1 = true → DInv w h b s bo oo had P0 cs.2 W3 H3 ∧ dmu s W3 H3 < μ1) ∧
          (cs.1 = false → DExit w h b s bo oo had P0 cs.2 W3 H3)) := by
    intro r _ _ W2 H2 d
    unfold decompCond
    refine GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ => Or.inl ⟨rfl, d⟩⟩) (fun hc => ?_)
    exact absurd rfl hc
  have hdm : ∀ (W' : World) (H' : Heap) (z' : ZStream), H'.streams s.strm = some z' →
      dmu s W' H' = rdLeft W'.fs s.fd + z'.avail_in.toNat + z'.avail_out.toNat := fun _ _ _ e => dmu_of e
  unfold decompRest
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
  apply GSat.ite
  · intro hai0
    have hai0' : z.avail_in = 0 := by simpa using hai0
    refine GSat.bind (GSat.mono (errlit_strm hv hs' Z_BUF_ERROR "unexpected end of file" 2 lit_eof (by decide))
      fun p W2 H2 q => GSat.bind (GSat.mono q fun _ W3 H3 q3 => ?_))
    obtain ⟨s2, q1, q2, q3', q4, q5, q6⟩ := q3
    have e2 := errOf_shape q2 h0'
    have heof2 : s2.eof = s'.eof := by rw [q2.1]; rfl
    have hz3 : H3.streams s.strm = some z := by rw [q6]; exact hz
    refine GSat.pure ?_
    unfold decompCond
    refine GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ => ?_⟩) (fun hc => absurd rfl hc)
    refine Or.inr ⟨by simp, s2, z, ⟨q3', g.trans (GStep.widen q5 _) hw0 ⟨s', hs'⟩, by rw [q4]; exact hfs, q1,
      shape_trans hsh e2, hz3, hle, hno, OutTgt.step ht q5 q3' q1 (by rw [e2]) (by rw [e2]; rfl) (by rw [e2]; rfl) fr
      (by rw [e2]; exact hsz')⟩, ?_, fun e => absurd e hret, fun _ => Or.inr ⟨by rw [heof2]; exact heof hai0', hai0'⟩⟩
    rw [hdm W3 H3 z hz3, q4]; rw [hdm W H z hz] at hμ0; exact hμ0
  · intro hai0
    have hin : z.avail_in ≠ 0 := by simpa using hai0
    have I := inflate_gz G M hv hs' hsz' h0' (by rw [hsh]; exact hhow) (by rw [hstrm]; exact hz) hin hout ht (k := had - z.avail_out.toNat)
      hno (by omega)
    rw [hstrm] at I
    refine GSat.bind (GSat.mono I fun r W1 H1 q => ?_)
    obtain ⟨hW1, hv1, hs1, gI, hres, hprog, ⟨z1, hz1, hzs1, hao1, hno1, hai1, hnb⟩, hfresh⟩ := q
    subst W1
    have g1 : GStep w h W H1 b [(.ref (.heap bo) oo, had)] := g.trans gI hw0 ⟨s', hs'⟩
    have errExit : ∀ (lit : String) (i : Nat) (hi : gzLits.findIdx? (· == lit) = some i) (hn : NoNul lit)
        (e : Int32) (r' : Int32), GSat W H1 (do
          let p ← gzLit lit
          gz_error (some b) e p
          pure ({ ret := r', ctl := .ret } : DecompLoop)) (fun st1 W1 H1 => GSat W1 H1 (decompCond (some s.strm) st1)
            (fun cs W2 H2 => (cs.1 = true → DInv w h b s bo oo had P0 cs.2 W2 H2 ∧ dmu s W2 H2 < μ1) ∧
              (cs.1 = false → DExit w h b s bo oo had P0 cs.2 W2 H2))) := by
      intro lit i hi hn e r'
      refine GSat.bind (GSat.mono (errlit_strm hv1 hs1 e lit i hi hn) fun p W2 H2 q => GSat.bind (GSat.mono q
        fun _ W3 H3 q3 => GSat.pure (exitErr r' W H W3 H3 (derr_of hw0 g1 hfs hs1 hsh h0 q3))))
    apply GSat.ite
    · intro _; exact errExit _ 3 lit_corrupt (by decide) _ _
    · intro hc1
      apply GSat.ite
      · intro _; exact errExit _ 0 GzReach.lit_oom (by decide) _ _
      · intro hc2
        apply GSat.ite
        · intro _
          obtain ⟨sh1, -⟩ := inv_of hs1 hv1.1
          obtain ⟨c5, base5, z5, -, -, hz5, -, -, -, hm5⟩ := (sh1.read (modeOf hs1 hv1.2.1)).bufs hsz'
          rw [hstrm, hz1] at hz5; cases hz5
          obtain ⟨hmc, hmk⟩ := msg_cstr (H := H1) hm5
          refine GSat.bind (GSat.lm ⟨_, H1, rdZ_app hz1 _, ?_⟩)
          apply GSat.ite
          · intro _
            refine GSat.bind (GSat.mono (errlit_strm hv1 hs1 Z_DATA_ERROR _ 4 lit_data (by decide)) fun p W2 H2 q =>
              GSat.bind (GSat.mono q fun _ W3 H3 q3 => GSat.pure (exitErr _ W H W3 H3 (derr_of hw0 g1 hfs hs1 hsh h0 q3))))
          · intro _
            refine GSat.bind (GSat.lm ⟨_, H1, rdZ_app hz1 _, ?_⟩)
            refine GSat.bind (GSat.mono (err_strm hv1 hs1 Z_DATA_ERROR _ hmc hmk) fun _ W3 H3 q3 =>
              GSat.pure (exitErr _ W H W3 H3 (derr_of hw0 g1 hfs hs1 hsh h0 q3)))
        · intro hc3
          have hr : r = Z_OK ∨ r = Z_STREAM_END := by
            simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc1 hc3
            rcases hres with e | e | e | e | e | e
            · exact Or.inl e
            · exact Or.inr e
            · exact absurd e hc1.2
            · exact absurd e hnb
            · exact absurd e hc3
            · exact absurd e hc1.1
          have hd1 := hdm W H1 z1 hz1
          have hd0 := hdm W H z hz
          have hai1' : z1.avail_in.toNat ≤ z.avail_in.toNat := UInt32.le_iff_toNat_le.mp hai1
          have hao1' : z1.avail_out.toNat ≤ z.avail_out.toNat := UInt32.le_iff_toNat_le.mp hao1
          have mid : DMid w h b s bo oo had W H1 s' z1 := by
            refine ⟨hv1, g1, hfs, hs1, hsh, hz1, by omega, ?_, OutTgt.step ht gI hv1 hs1 rfl rfl rfl fr hsz'⟩
            rw [hno1, UInt32.toNat_sub_of_le _ _ hao1]; congr 1; omega
          refine GSat.pure ?_
          unfold decompCond
          refine GSat.ite (fun hc => absurd hc (by simp [hgo])) (fun _ => ?_)
          refine GSat.bind (GSat.lm ⟨_, H1, rdZ_app hz1 _, GSat.pure ⟨fun hc => ?_, fun hc => ?_⟩⟩)
          · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
            obtain ⟨hc4, hc5⟩ := hc
            have hok : r = Z_OK := hr.resolve_right hc5
            obtain ⟨z2, hz2, hlt⟩ := hprog hok
            rw [hz1] at hz2; cases hz2
            have hlt' : dmu s W H1 < dmu s W H := by rw [hd1, hd0]; omega
            exact ⟨⟨hgo, hc5, s', z1, mid, hc4, by omega, fun _ => Or.inl (by omega)⟩, by omega⟩
          · refine Or.inr ⟨by simp [hgo], s', z1, mid, by rw [hd1]; rw [hd0] at hμ0; omega, fun hse FF hp => ?_,
              fun hne => Or.inl ?_⟩
            · rcases hfr hp with hlt | ⟨hWw, hHh⟩
              · rw [hd1]; rw [hd0] at hlt; omega
              · have hf : InflFresh H s' := by
                  obtain ⟨z7, sb7, st7, h7⟩ := hP0 hp
                  rw [← hHh, ← hstrm] at h7; exact ⟨z7, sb7, st7, h7⟩
                have := UInt32.lt_iff_toNat_lt.mp (hfresh FF hf hse z1 hz1)
                rw [← hWw, ← hHh, hd1, hd0]; omega
            · simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hc
              rcases hc with hc | hc
              · simpa using hc
              · exact absurd hc hne

open ZlibNg.Inflate in
/-- One trip of the loop of `gz_decomp`. -/
theorem body_spec (G : InflateGz) (M : InflateMsg) {w : World} {h : Heap} {b : Nat} {s : GzState} {bo oo had : Nat}
    {P0 : Prop} (hP0 : P0 → InflFresh h s) (hP1 : P0 → ∀ z0, h.streams s.strm = some z0 → z0.avail_in ≠ 0)
    (hw0 : ∃ s0, w.gz h b = some s0) (hsz : s.size ≠ 0) (h0 : s.«have» = 0) (hhow : s.how = GZIP)
    {st : DecompLoop} {W : World} {H : Heap} (hI : DInv w h b s bo oo had P0 st W H) :
    GSat W H (decompBody (some b) (some s.strm) st) (fun st1 W1 H1 => GSat W1 H1 (decompCond (some s.strm) st1)
      (fun cs W2 H2 => (cs.1 = true → DInv w h b s bo oo had P0 cs.2 W2 H2 ∧ dmu s W2 H2 < dmu s W H) ∧
        (cs.1 = false → DExit w h b s bo oo had P0 cs.2 W2 H2))) := by
  obtain ⟨hgo, hret, s', z, m, hout, hμ0, hfr⟩ := hI
  have m' := m
  obtain ⟨hv, g, hfs, hs', hsh, hz, hle, hno, ht⟩ := m'
  have hsz' : s'.size ≠ 0 := by rw [hsh]; exact hsz
  have h0' : s'.«have» = 0 := by rw [hsh]; exact h0
  have hstrm : s'.strm = s.strm := by rw [hsh]
  have hfd : s'.fd = s.fd := by rw [hsh]
  have fr : FreshBlocks H := hv.2.2.2.1.1
  rw [decompBody_eq]
  refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
  apply GSat.ite
  · intro hai0
    have hai0' : z.avail_in = 0 := by simpa using hai0
    have A := gz_avail_budget hv hs' h0' hsz' (by rw [hsh]; show s.how ≠ _; rw [hhow]; decide) (z0 := z) (by rw [hstrm]; exact hz)
    refine GSat.bind (GSat.mono A fun r W1 H1 q => ?_)
    obtain ⟨⟨hr, hv1, g1, hfs1, s1, hs1, hsh1⟩, hB⟩ := q
    have g' : GStep w h W1 H1 b [(.ref (.heap bo) oo, had)] := g.trans (GStep.widen g1 _) hw0 ⟨s', hs'⟩
    have hsh1' := shape_trans hsh hsh1
    apply GSat.ite
    · intro _
      refine GSat.pure ?_
      unfold decompCond
      exact GSat.ite (fun _ => GSat.pure ⟨fun e => absurd e (by simp), fun _ => Or.inl ⟨rfl, g', hfs.trans hfs1, s1,
        hs1, hv1, hsh1'⟩⟩) (fun hc => absurd rfl hc)
    · intro hr0
      have hr0' : r = 0 := by
        rcases hr with e | e
        · exact absurd (by rw [e]; rfl) hr0
        · exact e
      obtain ⟨s2, z1, hs2, hz1, ez1, hbud, hie⟩ := hB.1 hr0'
      rw [hstrm] at hz1; rw [hfd] at hbud
      rw [hs1] at hs2; cases hs2
      have hd1 := dmu_of (W := W1) hz1
      have hd0 := dmu_of (W := W) hz
      have mid : DMid w h b s bo oo had W1 H1 s1 z1 := by
        refine ⟨hv1, g', hfs.trans hfs1, hs1, hsh1', hz1, by rw [ez1]; exact hle, by rw [ez1]; exact hno,
          OutTgt.step ht g1 hv1 hs1 (by rw [hsh1]) (by rw [hsh1]; rfl) (by rw [hsh1]; rfl) fr (by rw [hsh1]; exact hsz')⟩
      have hle1 : dmu s W1 H1 ≤ dmu s W H := by
        rw [hd1, hd0]; rw [ez1] at hbud ⊢; simp only at hbud ⊢; omega
      refine rest_spec G M hP0 hw0 hsz h0 hhow hgo hret mid (by rw [ez1]; exact hout)
        (fun e => by rcases hie with h1 | h1; exact absurd e h1; exact h1) hle1 (Nat.le_trans hle1 hμ0) ?_
      intro hp
      rcases hfr hp with hlt | ⟨rfl, rfl⟩
      · exact Or.inl (by omega)
      · exact absurd hai0' (hP1 hp z hz)
  · intro hai0
    have hin : z.avail_in ≠ 0 := by simpa using hai0
    exact rest_spec G M hP0 hw0 hsz h0 hhow hgo hret m hout (fun e => absurd e hin) (Nat.le_refl _) hμ0 hfr

/-- `p - j` for `j` bytes before `p` inside a live heap block. -/
theorem addNeg {h : Heap} {c off j : Nat} {a : Array UInt8} (ha : h.bytes c = some a) (hoff : off ≤ a.size)
    (hj : j ≤ off) : (Ptr.ref (BRef.heap c) off : BPtr).add (-(Int.ofNat j)) h = .ok (.ref (.heap c) (off - j), h) := by
  have hg : Space.get h (BRef.heap c) = some a := ha
  simp only [Ptr.add, hg, Int.ofNat_eq_natCast]
  split
  · congr; omega
  · next hc => exact absurd ⟨hoff, by omega, by omega⟩ hc

theorem rdLeft_lt {w : World} {h : Heap} (hw : GzWFr w h) (fd : Int32) : rdLeft w.fs fd < 2 ^ 62 := by
  obtain ⟨-, -, -, -, hb, hn, -, -⟩ := hw
  unfold rdLeft
  split
  · next o _ =>
    have : (w.fs.nodes[o.node]?.getD #[]).size < 2 ^ 61 := by
      cases e : w.fs.nodes[o.node]? with
      | none => simp
      | some d => simp only [Option.getD_some]; exact hn d (Array.mem_of_getElem? e)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.sub_le _ _) _) (by omega)
  · omega

theorem shape_wide {s s1 : GzState} (h1 : s1 = { s with eof := s1.eof, err := s1.err, msg := s1.msg }) :
    s1 = { s with «have» := s1.«have», next := s1.next, how := s1.how, eof := s1.eof, err := s1.err, msg := s1.msg } := by
  cases s; cases s1; simp only [GzState.mk.injEq] at h1 ⊢; simp_all

open ZlibNg.Inflate in
/-- What `gz_decomp` leaves (see `gz_decomp_spec`). -/
def DecompPost (w : World) (h : Heap) (b : Nat) (s : GzState) (z0 : ZStream) (bo oo : Nat) (r : Int32) (W : World)
    (H : Heap) : Prop :=
  (r = -1 ∨ r = 0) ∧ GStep w h W H b [(.ref (.heap bo) oo, z0.avail_out.toNat)] ∧ FsRd w.fs W.fs ∧
  ∃ s', W.gz H b = some s' ∧ GzInvR { W with gzs := upd W.gzs b (some { s' with «have» := 0 }) } H (some b) ∧
    s' = { s with «have» := s'.«have», next := s'.next, how := s'.how, eof := s'.eof, err := s'.err, msg := s'.msg } ∧
    (r = -1 → s'.«have» = 0 ∧ s'.next = s.next ∧ s'.how = s.how) ∧
    (r = 0 → ∃ z, H.streams s.strm = some z ∧ z.avail_out.toNat ≤ z0.avail_out.toNat ∧
      s'.«have».toNat = z0.avail_out.toNat - z.avail_out.toNat ∧ s'.next = .val (.ref (.heap bo) oo) ∧
      OutTgt W H b s' bo oo z0.avail_out.toNat ∧ dmu s W H ≤ dmu s w h ∧
      (s'.how = LOOK ∨ s'.how = s.how) ∧
      (s'.how = LOOK → InflateFresh → z0.avail_in ≠ 0 → InflFresh h s → dmu s W H < dmu s w h) ∧
      (s'.how = s.how → s'.«have» ≠ 0 ∨ (s'.eof ≠ 0 ∧ z.avail_in = 0)))

/-- The state at the end of `gz_decomp`. -/
def decompSt (s1 : GzState) (hv : UInt32) (bo oo : Nat) (hw : Int32) : GzState :=
  { s1 with «have» := hv, next := .val (.ref (.heap bo) oo), how := hw }

theorem decompSt_shape {s s1 : GzState} (h1 : s1 = { s with eof := s1.eof, err := s1.err, msg := s1.msg })
    (hv : UInt32) (bo oo : Nat) (hw : Int32) :
    decompSt s1 hv bo oo hw = { s with «have» := hv, next := .val (.ref (.heap bo) oo), how := hw, eof := s1.eof, err := s1.err, msg := s1.msg } := by
  cases s; cases s1; simp only [GzState.mk.injEq, decompSt] at h1 ⊢; simp_all

open ZlibNg.Inflate in
/-- The part of `gz_decomp` after the loop. -/
theorem tail_spec {w : World} {h : Heap} {b : Nat} {s : GzState} {z0 : ZStream} {bo oo : Nat} (hhow : s.how = GZIP)
    (h0 : s.«have» = 0) (hsz : s.size ≠ 0) (hw0 : ∃ s0, w.gz h b = some s0) (hout : z0.avail_out ≠ 0) {lp : DecompLoop} {W : World}
    {H : Heap} (q : DExit w h b s bo oo z0.avail_out.toNat (z0.avail_in ≠ 0 ∧ InflFresh h s) lp W H) :
    GSat W H (decompTail (some b) (some s.strm) z0.avail_out lp) (DecompPost w h b s z0 bo oo) := by
  unfold decompTail
  rcases q with ⟨hc, gD, fD, s1, hs1, hv1, hsh1⟩ | ⟨hc, s1, z, ⟨hv, g, hfs, hs1, hsh1, hz, hle, hno, ht⟩, hμ, hse, hnse⟩
  · refine GSat.ite (fun _ => GSat.pure ?_) (fun hc' => absurd (by simp [hc]) hc')
    have h01 : s1.«have» = 0 := by rw [hsh1]; exact h0
    refine ⟨Or.inl rfl, gD, fD, s1, hs1, ?_, shape_wide hsh1, fun _ => ⟨h01, by rw [hsh1], by rw [hsh1]⟩,
      fun e => absurd e (by decide)⟩
    rw [have0_self h01, DeflateReset.upd_self W.gzs b s1 (gzs_of hs1)]; exact hv1
  · refine GSat.ite (fun hc' => absurd (by simpa using hc') hc) (fun _ => ?_)
    have hle' : z.avail_out ≤ z0.avail_out := UInt32.le_iff_toNat_le.mpr hle
    have hsub : (z0.avail_out - z.avail_out).toNat = z0.avail_out.toNat - z.avail_out.toNat :=
      UInt32.toNat_sub_of_le _ _ hle'
    obtain ⟨d, hd, hds⟩ : ∃ d, H.bytes bo = some d ∧ oo + z0.avail_out.toNat ≤ d.size := by
      rcases ht with ⟨c, base, hB, rfl, h1, h2⟩ | ⟨-, d, hd, hds⟩
      · obtain ⟨d, hd, hds⟩ := hB.fits; exact ⟨d, hd, by omega⟩
      · exact ⟨d, hd, hds⟩
    obtain ⟨sh, -⟩ := inv_of hs1 hv.1
    have P := sh.pos
    have hhow1 : s1.how = GZIP := by rw [hsh1]; exact hhow
    have sh1R := sh.read (modeOf hs1 hv.2.1)
    have hsh1' := shape_wide hsh1
    -- the end: the state `sF` with the output count, its start and the new `how`
    have fin : ∀ hw' : Int32, (hw' = LOOK ∨ hw' = s1.how) → (hw' = LOOK → lp.ret = Z_STREAM_END) →
        (hw' = s1.how → lp.ret ≠ Z_STREAM_END) →
        DecompPost w h b s z0 bo oo 0 { W with gzs := upd W.gzs b (some (decompSt s1 (z0.avail_out - z.avail_out) bo oo hw')) } H := by
      intro hw' hw1 hw2 hw3
      let sF : GzState := decompSt s1 (z0.avail_out - z.avail_out) bo oo hw'
      have hsF := gz_upd_same hs1 sF
      have hown : GzOwned { W with gzs := upd W.gzs b (some sF) } H (some b) = GzOwned W H (some b) := by
        simp only [GzOwned, hsF, hs1]; rfl
      refine ⟨Or.inr rfl, g.trans (GStep.widen (gstep_st (s' := sF) hs1 W.fs rfl rfl rfl rfl) _) hw0 ⟨s1, hs1⟩, hfs, sF, hsF,
        ?_, ?_, fun e => absurd e (by decide), fun _ => ⟨z, hz, hle, hsub, rfl, ?_, hμ, ?_, ?_, ?_⟩⟩
      · have hv2 := invR_seek hv hs1 0 (.val (.ref (.heap bo) oo)) s1.pos s1.skip hw'
          (by rcases hw1 with e | e
              · exact Or.inl e
              · rw [e, hhow1]; exact Or.inr (Or.inr rfl)) P.1 P.2 P.3 (Or.inl rfl) (fun _ => rfl) (fun e => absurd (by rw [hsh1] at e; exact e) hsz)
          (by have := P.1; have := P.2; simp; omega)
          (fun _ hd => absurd ((sh1R.gzip_direct hhow1)) hd)
          (fun _ => sh1R.gzip_direct hhow1)
          (fun e => absurd e (by rcases hw1 with e1 | e1 <;> rw [e1] <;> (try rw [hhow1]) <;> decide))
        simp only [InflateInv.upd_upd]
        exact hv2
      · exact decompSt_shape hsh1 _ _ _ _
      · rcases ht with ⟨c, base, hB, e1, h1, h2⟩ | ⟨hno', d', hd', hds'⟩
        · exact Or.inl ⟨c, base, ⟨hB.size, hB.buffers, hB.inp, hB.out, hB.fits, hB.hdr⟩, e1, h1, h2⟩
        · exact Or.inr ⟨by rw [hown]; exact hno', d', hd', hds'⟩
      · rcases hw1 with e | e
        · exact Or.inl e
        · exact Or.inr (by show hw' = s.how; rw [e]; rw [hsh1])
      · intro hl FF ha hf
        exact hse (hw2 hl) FF ⟨ha, hf⟩
      · intro hs2
        have hw4 : hw' = s1.how := by rw [show s1.how = s.how by rw [hsh1]]; exact hs2
        rcases hnse (hw3 hw4) with e | ⟨e1, e2⟩
        · left; intro e'
          change (z0.avail_out - z.avail_out) = 0 at e'
          have := congrArg UInt32.toNat e'
          have h5 : z0.avail_out.toNat ≠ 0 := fun e5 => hout (UInt32.toNat_inj.mp (by simpa using e5))
          have h6 : z.avail_out.toNat = 0 := by rw [e]; rfl
          rw [hsub] at this; simp only [UInt32.toNat_zero] at this; omega
        · exact Or.inr ⟨e1, e2⟩
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
    refine GSat.bind (GSat.of_eq (wrG_app hs1 _) ?_)
    have hs2 := gz_upd_same hs1 { s1 with «have» := z0.avail_out - z.avail_out }
    refine GSat.bind (GSat.lm ⟨_, H, rdZ_app hz _, ?_⟩)
    refine GSat.bind (GSat.of_eq (rdG_app' hs2 _) ?_)
    refine GSat.bind (GSat.lm ⟨.ref (.heap bo) oo, H, ?_, ?_⟩)
    · rw [hno]; show (Ptr.ref _ _ : BPtr).add (-(Int.ofNat (z0.avail_out - z.avail_out).toNat)) H = _
      rw [hsub]
      have := addNeg (j := z0.avail_out.toNat - z.avail_out.toNat) hd (off := oo + (z0.avail_out.toNat - z.avail_out.toNat))
        (by omega) (by omega)
      rw [this]; congr 3; omega
    refine GSat.bind (GSat.of_eq (wrG_app hs2 _) ?_)
    have hs3 := gz_upd_same hs2 { ({ s1 with «have» := z0.avail_out - z.avail_out } : GzState) with
      next := .val (.ref (.heap bo) oo) }
    apply GSat.ite
    · intro hse'
      refine GSat.bind (GSat.of_eq (wrG_app hs3 _) (GSat.pure ?_))
      simp only [InflateInv.upd_upd]
      exact fin LOOK (Or.inl rfl) (fun _ => by simpa using hse') (fun e => by rw [hhow1] at e; exact absurd e (by decide))
    · intro hse'
      refine GSat.pure ?_
      simp only [InflateInv.upd_upd]
      exact fin s1.how (Or.inr rfl) (fun e => by rw [hhow1] at e; exact absurd e (by decide))
        (fun _ e => hse' (by simp [e]))

open ZlibNg.Inflate in
/-- **`gz_decomp`** on a read handle with `x.have == 0` and `how == GZIP` whose stream has `avail_out` (not 0) bytes of
room at `next_out`, inside the `out` buffer of the file (`gz_fetch`) or outside every block of the file (`gz_read`, the
caller's buffer): it returns `-1` or `0`, writes only that range, only reads the file system, and leaves a read handle
once `x.have` is cleared; on `0`, `x.have` is the number of bytes written at `x.next`, the start of the range, and
`how` is `LOOK` after the end of the gzip member, else `GZIP` with output or with `eof` and no input. It terminates:
every trip of its loop but the last lowers the read measure (`dmu`), which never grows (`DecompPost`). -/
theorem gz_decomp_spec {w : World} {h : Heap} {b : Nat} {s : GzState}
    (hv : GzInvR w h (some b)) (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) (hhow : s.how = GZIP)
    {z0 : ZStream} (hz0 : h.streams s.strm = some z0) (hout : z0.avail_out ≠ 0) {bo oo : Nat}
    (hno : z0.next_out = .ref (.heap bo) oo) (ht : OutTgt w h b s bo oo z0.avail_out.toNat) :
    GSat w h (gz_decomp (some b)) (DecompPost w h b s z0 bo oo) := by
  have hw0 : ∃ s0, w.gz h b = some s0 := ⟨s, hs⟩
  rw [gz_decomp_eq]
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.lm ⟨_, h, rdZ_app hz0 _, ?_⟩)
  have hI : DInv w h b s bo oo z0.avail_out.toNat (z0.avail_in ≠ 0 ∧ InflFresh h s) ⟨Z_OK, .go⟩ w h := by
    refine ⟨rfl, by decide, s, z0, ⟨hv, GStep.refl _ _ _ _, FsRd.refl _, hs, rfl, hz0, Nat.le_refl _, ?_, ht⟩, hout,
      Nat.le_refl _, fun _ => Or.inr ⟨rfl, rfl⟩⟩
    rw [hno]; simp
  have hfuel : dmu s w h < fuel := by
    rw [dmu_of hz0]
    have := rdLeft_lt hv.2.2 s.fd
    have := z0.avail_in.toNat_lt
    have := z0.avail_out.toNat_lt
    simp [fuel]; omega
  refine GSat.bind (GSat.mono (gsat_gdoWhile (DInv w h b s bo oo z0.avail_out.toNat (z0.avail_in ≠ 0 ∧ InflFresh h s))
    (fun _ W H => dmu s W H) (DExit w h b s bo oo z0.avail_out.toNat (z0.avail_in ≠ 0 ∧ InflFresh h s))
    (fun st W H hI' => body_spec inflateGz inflateMsg (fun p => p.2) (fun p z1 hz1 => by rw [hz0] at hz1; cases hz1; exact p.1) hw0 hsz
      h0 hhow hI') hI hfuel) fun lp W H q => ?_)
  exact tail_spec hhow h0 hsz hw0 hout q

end ZlibNgF.Proof.GzDecomp
