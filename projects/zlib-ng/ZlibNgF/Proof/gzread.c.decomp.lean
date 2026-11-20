import ZlibNgF.Proof.«gzread.c.load»
import ZlibNgF.Proof.«gzread.c.facts»

/-!
# `gz_avail` with its read measure, and `gz_decomp` (`ZlibNgF`)

`gz_decomp` loops while `inflate` makes progress and the caller's output has room. Its measure is the input still
to come: the bytes the read oracle may still deliver (`Fs.budget`), the bytes of the file of the descriptor after its
offset (`rdLeft`), and the input `avail_in` already in the buffer, plus the room `avail_out`. `gz_avail` does not raise
`rdLeft + avail_in` (`gz_avail_budget`), and a trip of the loop that does not end it lowers `avail_in + avail_out`
(`inflate` returned `Z_OK`).

`InflateGz` is what `gz_decomp` needs of `inflate` beyond `inflate_ok`: the set of its results, and that it moves
`next_in` and `next_out` exactly by the bytes it consumed and wrote.
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

/-! ## `gz_avail` with its read measure -/

/-- What `gz_decomp` needs of a `gz_avail` that returned 0, beyond `AvailPost`: only `next_in` and `avail_in` of the
stream `z` changed, the input in the buffer grew by at most what came out of the read measure, and there is input or
`eof` is set. -/
def AvailBudget (w : World) (b : Nat) (s : GzState) (z : ZStream) (r : Int32) (W : World) (H : Heap) : Prop :=
  r = 0 → ∃ s' z', W.gz H b = some s' ∧ H.streams s.strm = some z' ∧
    z' = { z with next_in := z'.next_in, avail_in := z'.avail_in } ∧
    rdLeft W.fs s.fd + z'.avail_in.toNat ≤ rdLeft w.fs s.fd + z.avail_in.toNat ∧ (z'.avail_in ≠ 0 ∨ s'.eof ≠ 0)

theorem availTail_budget {w : World} {h : Heap} {b : Nat} {s : GzState} (hv : GzInvR w h (some b))
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {c base : Nat} {z : ZStream}
    (hB : GzBufs h s c base) (hz : h.streams s.strm = some z)
    (hai : z.avail_in = 0 ∨ Inside c base 0 (inSize s) z.next_in z.avail_in.toNat)
    {H : Heap} (x : HBuf h H c base (base + inSize s)) :
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
    refine GSat.bind (GSat.mono (gz_error_inv (invR_lit hv1 am) hs1 Z_ERRNO pm (Or.inr hcs) hmk) fun _ W H2 q => ?_)
    obtain ⟨s', hsW, herr, hvW, -, hfsW, hstep⟩ := q
    refine GSat.pure (GSat.pure ⟨⟨Or.inl rfl, hvW, ?_, by rw [hfsW]; exact hfs, s', hsW, errOf_shape herr h0⟩,
      fun e => absurd e (by decide)⟩)
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
        refine GSat.pure ⟨⟨Or.inr rfl, ?_, ?_, hfs, _, hs2, rfl⟩, fun _ => ⟨_, z', hs2, by simp, rfl, ?_, ?_⟩⟩
        · obtain ⟨sh1, hn1⟩ := inv_of hs1 hv1.1
          have sh1' := shape_msg sh1 e s.past s.err s.msg ⟨sh1.msg.1, sh1.msg.2⟩
          have hvE : GzInvR { w with fs := fs', gzs := upd w.gzs b (some { s with eof := e }) } H1 (some b) :=
            (keeps_store hs1 (HLess.refl H1) (fun _ e => e) sh1' hn1 rfl rfl).1 hv1
          refine invR_strm (s := { s with eof := e }) (z := z) (z' := z') hvE hs2 hsz hz1 rfl fun c' base' hB' => Or.inr ⟨0, ?_, Nat.le_refl _, ?_⟩
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
    (hs : w.gz h b = some s) (h0 : s.«have» = 0) (hsz : s.size ≠ 0) {z0 : ZStream} (hz0 : h.streams s.strm = some z0) :
    GSat w h (gz_avail (some b)) (fun r W H => AvailPost w h b s r W H ∧ AvailBudget w b s z0 r W H) := by
  obtain ⟨sh, hn⟩ := inv_of hs hv.1
  have hr := modeOf hs hv.2.1
  obtain ⟨c, base, z, hB, -, hz, -, hai, -⟩ := (sh.read hr).bufs hsz
  have ez : z = z0 := Option.some.inj (hz.symm.trans hz0)
  subst ez
  obtain ⟨hcb, hpath, hst, hown⟩ := buf_facts hs hn hsz hB
  obtain ⟨d, hd, hds⟩ := hB.fits
  have done0 : s.eof ≠ 0 → AvailPost w h b s 0 w h ∧ AvailBudget w b s z 0 w h := fun he =>
    ⟨⟨Or.inr rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩,
      fun _ => ⟨s, z, hs, hz, rfl, Nat.le_refl _, Or.inr he⟩⟩
  have tail : ∀ H, HBuf h H c base (base + inSize s) →
      GSat w H (availTail (some b) (some s.strm)) (fun r W H' => AvailPost w h b s r W H' ∧ AvailBudget w b s z r W H') := by
    intro H x
    have hsH : w.gz H b = some s := by rw [x.gz hcb]; exact hs
    have g : GStep w h w H b [] := by
      have := gstep_hbuf hs x hcb hown w.fs s rfl rfl rfl rfl
      rw [DeflateReset.upd_self w.gzs b s (gzs_of hs)] at this
      exact this
    exact (availTail_budget hv hs h0 hsz hB hz hai x).mono fun r W H' p => ⟨AvailPost.pre g hs hsH p.1, p.2⟩
  unfold gz_avail
  refine GSat.bind (GSat.of_eq (strmOf_app hs) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  refine GSat.bind (GSat.of_eq (rdG_app' hs _) ?_)
  apply GSat.ite
  · intro _; exact GSat.pure ⟨⟨Or.inl rfl, hv, GStep.refl w h b [], FsRd.refl _, s, hs, rfl⟩, fun e => absurd e (by decide)⟩
  · intro _
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
          exact tail H ((HBuf.refl h c base (base + inSize s)).trans x (Nat.le_refl _) (by omega))
        · intro _; exact tail h (HBuf.refl _ _ _ _)
      · intro _; exact tail h (HBuf.refl _ _ _ _)
    · intro he; exact GSat.pure (done0 (by simpa using he))


end ZlibNgF.Proof.GzDecomp
