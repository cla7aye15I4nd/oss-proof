import ZlibNgF.Proof.«deflate.c.reset»
import ZlibNgF.Proof.«inflate.c.gzextra-modes»

/-!
# `deflateCopy` (`ZlibNgF`)

`deflateCopy(dest, source)` on an invariant source and a distinct destination ready for initialisation: the
destination record gets a copy of the source record, `alloc_deflate` gets a fresh block for `W_BITS(ss)` (the
`windowBits` of the source, from `w_size = 2^k`) and the source's `lit_bufsize` (or fails: `Z_MEM_ERROR`, and then
`dest->state` still points at the source's state), the state is copied as a record, its pointers are set into the new
block, the window, `prev`, `head` and `pending_buf` bytes are copied, `pending_out` is rebased through
`pending_out - pending_buf`, `sym_buf` is set after `pending_buf` and the tree descriptors point at the copy's trees.
The source keeps its invariant, a successful copy has it (the tallied symbols are copied with `pending_buf`, so
`SymOk` holds at the new offset), and only the destination record and the fresh block change.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.DeflateCopy
open C ZlibNgF.Spec ZlibNg.Inflate ZlibNg.Deflate ZlibNgF.Proof.DeflateInv
open ZlibNgF.Proof.DeflateAlloc (AH dAllocRec dWS gState alloc_ok alloc_fail alloc_fault Fl Fl.bind_now
  u32_toInt32_toInt)
open ZlibNgF.Proof.DeflateInit (SH SH_streams SH_dstates SH_bytes SH_dstate SH_dallocs wrD_SH ldDState_SH wrZ_SH
  ldDAllocs_SH add_SH AH_SH dframe_of wbuf_toNat)
open ZlibNgF.Proof.InflateInv (ldStream_app upd_upd)
open ZlibNgF.Proof.InflateAlloc (space_get_heap)
open ZlibNgF.Proof.InflateDict (memcpy_heap copyFold copyFold_size copyFold_get)
open ZlibNgF.Proof.InflateSync (Sat Sat.bind Sat.pure Sat.of_eq Sat.mono)

/-! ## Arithmetic and arrays -/

/-- `zng_ctz32` of `w_size = 2^k`. -/
theorem ctz_pow {w : UInt32} {k : Nat} (hk1 : 9 ≤ k) (hk2 : k ≤ 15) (hw : w.toNat = 2 ^ k) :
    zng_ctz32 w = pure (UInt32.ofNat k) := by
  have e : w = UInt32.ofNat (2 ^ k) := by
    apply UInt32.toNat_inj.mp
    rw [hw, UInt32.toNat_ofNat_of_lt' (by
      have : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hk2
      simp only [UInt32.size]; omega)]
  subst e
  have : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold zng_ctz32; simp; rfl)

/-- The copy of `n` bytes from `os` to `od` holds the source bytes. -/
theorem copyFold_in (src : Array UInt8) (od os n : Nat) (a : Array UInt8) (k : Nat) (hk : k < n)
    (hs : od + n ≤ a.size) : (copyFold src od os (List.range' 0 n) a)[od + k]! = src[os + k]! := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range'_concat]
    simp only [copyFold, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    have hsz : (List.foldl (fun out i => out.set! (od + i) src[os + i]!) a (List.range' 0 n)).size = a.size :=
      copyFold_size src od os _ a
    simp only [Nat.zero_add, Nat.one_mul]
    by_cases e : k = n
    · subst e
      generalize List.foldl (fun out i => out.set! (od + i) src[os + i]!) a (List.range' 0 k) = X at hsz ⊢
      simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds]
      simp [show od + k < X.size by omega]
    · simp only [Array.set!_eq_setIfInBounds, getElem!_def, Array.getElem?_setIfInBounds] at ih ⊢
      simp only [show ¬ od + n = od + k by omega, ↓reduceIte]
      exact ih (by omega) (by omega)

theorem i64_small (n : Nat) (h : n < 2 ^ 62) : (Int64.ofInt (n : Int)).toInt = n :=
  Int64.toInt_ofInt_of_le (by omega) (by omega)

/-- `SymOk` at a new offset, for bytes that agree on the symbols. -/
theorem SymOk.shift {d d' : Array UInt8} {sbo sbo' : Nat} {n : UInt32} {lt dt : Array Ct}
    (hs : SymOk d sbo n lt dt) (he : ∀ k, k < n.toNat → d'[sbo' + k]! = d[sbo + k]!) : SymOk d' sbo' n lt dt := by
  have hj : ∀ j, j < n.toNat / 3 → symDist d' sbo' j = symDist d sbo j ∧ symLCode d' sbo' j = symLCode d sbo j := by
    intro j hj
    have e0 := he (3 * j) (by omega)
    have e1 := he (3 * j + 1) (by omega)
    have e2 := he (3 * j + 2) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e1 e2
    have hd : symDist d' sbo' j = symDist d sbo j := by simp only [symDist, e0, e1]
    exact ⟨hd, by simp only [symLCode, hd, e2]⟩
  refine ⟨fun j h3 => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · rw [(hj j h3).1]; exact hs.dist j h3
  · rw [hs.lfreq c hc]; congr 1
    exact List.countP_congr fun j hm => by
      rw [(hj j (List.mem_range.mp hm)).2]
  · rw [hs.dfreq c hc]
    exact List.countP_congr fun j hm => by
      rw [(hj j (List.mem_range.mp hm)).1]

/-! ## The heap during the copy: `SH B j z nb g d` with the fresh block `nb` -/

section
variable {B : Heap} {j nb : Nat} {z : ZStream} {g : DeflateState} {d : Array UInt8}

theorem SH_dstate_ne {c : Nat} (hc : c ≠ nb) : (SH B j z nb g d).dstate c = B.dstate c := by
  simp [Heap.dstate, SH, upd_ne _ _ _ _ hc]

theorem SH_bytes_ne {c : Nat} (hc : c ≠ nb) : (SH B j z nb g d).bytes c = B.bytes c := by
  simp [SH, upd_ne _ _ _ _ hc]

theorem ldDState_ne {b : Nat} {st : DeflateState} (hb : b ≠ nb) (hs : B.dstate b = some st) :
    ldDState (some b) (SH B j z nb g d) = .ok (st, SH B j z nb g d) := by
  simp [ldDState, SH_dstate_ne hb, hs]

theorem copyDState_SH {b : Nat} {st : DeflateState} (hb : b ≠ nb) (hs : B.dstate b = some st) :
    copyDState (some nb) (some b) (SH B j z nb g d) = .ok ((), SH B j z nb st d) := by
  have hne : (some nb == some b) = false := by simp [Ne.symm hb]
  simp only [copyDState, hne, Bool.false_eq_true, ↓reduceIte, bind_app, ldDState_ne hb hs, ldDState_SH]
  simp only [stDState, SH_dstate]
  simp [SH, upd_upd]

theorem memcpy_SH {od os n b : Nat} {src : Array UInt8} (hb : b ≠ nb) (hs : B.bytes b = some src)
    (h1 : od + n ≤ d.size) (h2 : os + n ≤ src.size) :
    Ptr.memcpy (Ptr.ref (BRef.heap nb) od) (Ptr.ref (BRef.heap b) os) n (SH B j z nb g d) =
      .ok ((), SH B j z nb g (copyFold src od os (List.range' 0 n) d)) := by
  have hs' : Space.get (SH B j z nb g d) (BRef.heap b) = some src := by
    rw [space_get_heap, SH_bytes_ne hb]; exact hs
  rw [memcpy_heap (SH_bytes _ _ _ _ _ _) hs' (fun e => hb (BRef.heap.inj e)) h1 h2]
  simp [SH, upd_upd]

theorem diff_SH {b o1 o2 : Nat} {src : Array UInt8} (hb : b ≠ nb) (hs : B.bytes b = some src)
    (h1 : o1 ≤ src.size) (h2 : o2 ≤ o1) (h4 : o1 - o2 < 2 ^ 62) :
    Ptr.diff (Ptr.ref (BRef.heap b) o1) (Ptr.ref (BRef.heap b) o2) (SH B j z nb g d) =
      .ok (Int64.ofInt ((o1 - o2 : Nat) : Int), SH B j z nb g d) := by
  have hs' : Space.get (SH B j z nb g d) (BRef.heap b) = some src := by
    rw [space_get_heap, SH_bytes_ne hb]; exact hs
  simp only [Ptr.diff, hs', ↓reduceIte]
  rw [DeflateAlloc.ite_t ⟨h1, by omega⟩, DeflateAlloc.ite_t ⟨by omega, by omega⟩]
  congr 3; omega

end

/-! ## The run -/

/-- The hash chains move with the copy: state `st'` (bytes `dF` of block `nb`) has the `w_size` of `st` (bytes `d`
of block `b`), and its `head` and `prev` arrays hold the bytes of those of `st`. -/
def ChainCopy (b nb : Nat) (d dF : Array UInt8) (st st' : DeflateState) : Prop :=
  st'.w_size = st.w_size ∧ 0 < st.w_size.toNat ∧ ∀ ho po, st.head = .val (.ref (.heap b) ho) → st.prev = .val (.ref (.heap b) po) →
    ∃ nho npo, st'.head = .val (.ref (.heap nb) nho) ∧ st'.prev = .val (.ref (.heap nb) npo) ∧
      (∀ q, q < 131072 → dF[nho + q]! = d[ho + q]!) ∧ (∀ q, q < 2 * st.w_size.toNat → dF[npo + q]! = d[po + q]!)

/-- What `deflateCopy` guarantees: only the destination record and fresh blocks change, the source keeps its
invariant, and a successful copy has it, with the hash chains copied (`ChainCopy`). -/
def CopyPost (h : Heap) (i j : Nat) (st : DeflateState) (r : Int32) (h' : Heap) : Prop :=
  DFrame h h' [j] [] [] [] ∧ DInv h' (some i) ∧ (r = Z_OK → DInv h' (some j) ∧
    ∃ z' nb st', h'.streams j = some z' ∧ z'.state = some nb ∧ h.nextBlk ≤ nb ∧ h'.dstate nb = some st' ∧
      SideEq st st' ∧ ∀ b d dF, h.bytes b = some d → h'.bytes nb = some dF → ChainCopy b nb d dF st st')

theorem copy_run {h : Heap} {i j : Nat} {z zd : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (L : DLive h i z b st) (hal : h.dallocsOf b = some al) (c : DCore h (some i) z b (dview st) al)
    (hzd : h.streams j = some zd) (hji : j ≠ i)
    (hfr : h.allocOk h.nalloc = true → h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) :
    Sat h (deflateCopy (some j) (some i)) (fun r h' => CopyPost h i j st r h') := by
  have hne : (some j == some i) = false := by simp [hji]
  let H1 : Heap := { h with streams := upd h.streams j (some z) }
  have ecs : copyStream (some j) (some i) h = .ok ((), H1) := by
    simp [copyStream, bind_app, hne, ldStream_app L.hz, ldStream_app hzd, stStream, hzd, H1]
  have hst1 : H1.dstate b = some st := L.dstate
  obtain ⟨k, hk1, hk2, hwk⟩ := c.wpow
  have hctz : W_BITS st H1 = .ok (UInt32.ofNat k, H1) := by
    have hwk' : st.w_size.toNat = 2 ^ k := hwk
    simp only [W_BITS, ctz_pow hk1 hk2 hwk']; rfl
  unfold deflateCopy
  refine Sat.bind (Sat.of_eq L.check ?_)
  simp only [Bool.false_or, show (some j == (none : StreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Sat.bind (Sat.of_eq L.stateOf ?_)
  refine Sat.bind (Sat.of_eq ecs ?_)
  refine Sat.bind (Sat.of_eq (ldDState_app hst1) ?_)
  refine Sat.bind (Sat.of_eq hctz ?_)
  have hza1 : H1.streams j = some z := by simp [H1]
  have hn : (UInt32.ofNat k).toInt32.toInt = k := by
    have : k < 2 ^ 31 := by omega
    rw [u32_toInt32_toInt _ (by rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]; omega),
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
  obtain ⟨_, _, _, hl1, hl2, _, _⟩ := c.sizes
  have hl3 : st.lit_bufsize.toNat % 16 = 0 := c.lmod
  simp only [dview] at hl1 hl2 hl3
  have hl : st.lit_bufsize.toInt32.toInt = st.lit_bufsize.toNat := u32_toInt32_toInt _ (by omega)
  have hsrc : ∀ H' : Heap, H'.streams i = h.streams i → H'.bytes b = h.bytes b → H'.dstates b = h.dstates b →
      H'.dallocs b = h.dallocs b → DInv H' (some i) := by
    intro H' e1 e2 e3 e4
    refine ⟨i, z, b, st, al, rfl, by rw [e1]; exact L.hz, L.hb, ?_, ?_, DCore.of_heap e2 c⟩
    · simp only [Heap.dstate, e2, e3]; exact L.dstate
    · simp only [Heap.dallocsOf, e2, e4]; exact hal
  have hi1 : H1.streams i = h.streams i := by simp [H1, Ne.symm hji]
  cases hok : h.allocOk h.nalloc
  · refine Sat.bind (Sat.of_eq (alloc_fail (h := H1) hza1 c.zalloc hok _ _ k st.lit_bufsize.toNat hn hk1 hk2 hl
      hl1 hl2 hl3) ?_)
    simp only [beq_self_eq_true, ↓reduceIte]
    refine Sat.pure ⟨dframe_of (fun k hk => by simp [H1, upd_ne _ _ _ _ hk]) rfl
      (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl rfl rfl rfl (Nat.le_refl _), hsrc _ hi1 rfl rfl rfl,
      fun e => absurd e (by decide)⟩
  obtain ⟨hfs, hfa⟩ := hfr hok
  refine Sat.bind (Sat.mono (alloc_ok (h := H1) hza1 c.zalloc hfs hfa hok _ _ k st.lit_bufsize.toNat hn hk1 hk2 hl
    hl1 hl2 hl3) ?_)
  rintro _ _ ⟨rfl, d, rfl, hdsz, -⟩
  have eSH : ∀ Y g, AH H1 d Y (upd H1.dstates H1.nextBlk (some g)) = SH (AH H1 d Y H1.dstates) j z H1.nextBlk g d :=
    fun Y g => AH_SH h j z d Y g
  rw [eSH]
  simp only [show (some H1.nextBlk == none) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hnb : H1.nextBlk = h.nextBlk := rfl
  have hbn : b ≠ h.nextBlk := by
    intro e; have := L.hst; rw [e, hfs] at this; cases this
  generalize hB : AH H1 d (upd H1.dallocs H1.nextBlk (some (dAllocRec H1.nextBlk
    (PADSZ (H1.baseAddr (BRef.heap H1.nextBlk)) 64).toNat (dWS (2 ^ k)) (2 ^ k) z.zfree))) H1.dstates = B
  have hY : B.dallocs H1.nextBlk = some (dAllocRec H1.nextBlk (PADSZ (H1.baseAddr (BRef.heap H1.nextBlk)) 64).toNat
      (dWS (2 ^ k)) (2 ^ k) z.zfree) := by rw [← hB]; simp
  have hBst : B.dstate b = some st := by
    have hbn1 : b ≠ H1.nextBlk := hbn
    rw [← hB]; simp only [Heap.dstate, AH, upd_ne _ _ _ _ hbn1]; exact hst1
  have hBb : B.bytes b = h.bytes b := by
    have hbn1 : b ≠ H1.nextBlk := hbn
    rw [← hB]; simp only [AH, upd_ne _ _ _ _ hbn1]; rfl
  have hBo : ∀ c', c' ≠ h.nextBlk → B.bytes c' = h.bytes c' ∧ B.istates c' = h.istates c' ∧
      B.iallocs c' = h.iallocs c' ∧ B.dstates c' = h.dstates c' ∧ B.dallocs c' = h.dallocs c' := by
    intro c' hc; have hc1 : c' ≠ H1.nextBlk := hc
    rw [← hB]; simp only [AH, upd_ne _ _ _ _ hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hBs : B.streams = upd h.streams j (some z) := by rw [← hB]; rfl
  have hBg : B.gzheaders = h.gzheaders ∧ B.consts = h.consts ∧ B.crcTable = h.crcTable ∧
      B.x2nTable = h.x2nTable ∧ B.baseAddr = h.baseAddr ∧ h.nextBlk ≤ B.nextBlk := by
    rw [← hB]; exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [AH, H1]⟩
  rw [hnb] at hY hdsz ⊢
  generalize (PADSZ (H1.baseAddr (BRef.heap h.nextBlk)) 64).toNat = p at hY hdsz ⊢
  generalize gState H1 = g
  generalize hnbv : h.nextBlk = nb at hY hdsz hbn hBo ⊢
  refine Sat.bind (Sat.of_eq (ldDAllocs_SH hY) ?_)
  simp only [dAllocRec, Ival.get, DeflateAlloc.pure_bind_M]
  sstep wrZ_SH _
  sstep copyDState_SH hbn hBst
  sstep wrD_SH _
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, DeflateAlloc.pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, DeflateAlloc.pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, DeflateAlloc.pure_bind_M]
  sstep wrD_SH _
  sstep ldDAllocs_SH hY
  simp only [dAllocRec, DeflateAlloc.pure_bind_M]
  sstep wrD_SH _
  sstep ldDState_SH
  simp only [DeflateAlloc.pure_bind_M, show ∀ o : Nat, (Ptr.ref (BRef.heap nb) o == Ptr.null) = false from
    fun _ => rfl, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  sstep ldDState_ne hbn hBst
  obtain ⟨d0, wo, po, ho, pbo, hd0, hwo, hpo, hho, hpbo, l1, l2, l3, l4, hsb, poo, hpoo, hpp, hpe⟩ := c.lay
  obtain ⟨hw1, hw2, hwsz, -, -, hpbs, hse⟩ := c.sizes
  simp only [dview] at hwo hpo hho hpbo l1 l2 l3 l4 hsb hpoo hpe hw1 hw2 hwsz hpbs hse
  have hwk' : st.w_size.toNat = 2 ^ k := hwk
  have hwb : (W_BUF_SIZE st.w_size).toNat = dWS (2 ^ k) := by rw [wbuf_toNat _ hw2, hwk']
  rw [hwsz, hwb] at l1
  rw [hwk'] at l2 hw1 hw2
  have hBd : B.bytes b = some d0 := by rw [hBb]; exact hd0
  have p15 : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hk2
  have hD : dWS (2 ^ k) ≤ 65536 := by unfold dWS; split <;> omega
  rw [hwo]
  sstep rfl
  simp only [hwb]
  sstep memcpy_SH hbn hBd (by omega) (by omega)
  rw [hpo]
  sstep rfl
  rw [hwk']
  sstep memcpy_SH hbn hBd (by simp only [copyFold_size]; omega) (by omega)
  rw [hho]
  sstep rfl
  rw [show HASH_SIZE.toNat * 2 = 131072 from rfl]
  sstep memcpy_SH hbn hBd (by simp only [copyFold_size]; omega) (by omega)
  rw [hpbo]
  sstep rfl
  have hl4 : (st.lit_bufsize * 4 + 1 + 8).toNat = 4 * st.lit_bufsize.toNat + 9 := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul]; simp; omega
  rw [hl4]
  sstep memcpy_SH hbn hBd (by simp only [copyFold_size]; omega) (by omega)
  rw [hpoo]
  sstep rfl
  sstep rfl
  sstep diff_SH hbn hBd (by omega) hpp (by omega)
  rw [i64_small (poo - pbo) (by omega)]
  sstep add_SH (poo - pbo) (by simp only [copyFold_size]; omega)
  sstep wrD_SH _
  sstep ldDState_SH
  simp only [DeflateAlloc.pure_bind_M]
  sstep add_SH st.lit_bufsize.toNat (by simp only [copyFold_size]; omega)
  rw [show PENDING_BUF_PAD.toInt = ((8 : Nat) : Int) from rfl]
  sstep add_SH 8 (by simp only [copyFold_size]; omega)
  sstep wrD_SH _
  sstep rfl
  sstep rfl
  sstep rfl
  sstep wrD_SH _
  sstep wrD_SH _
  sstep wrD_SH _
  obtain ⟨d2, sbo, hd2, hsb2, hsym⟩ := c.symv
  simp only [dview] at hsb2 hsym
  obtain rfl : d0 = d2 := Option.some.inj (hd0.symm.trans hd2)
  rw [hsb] at hsb2
  obtain rfl : pbo + st.lit_bufsize.toNat + 8 = sbo := by injection hsb2 with e; injection e
  have hsyms := c.syms
  simp only [dview] at hsyms
  have hsn : st.sym_next.toNat ≤ 3 * (st.lit_bufsize.toNat - 1) := by
    rw [← hse]; exact UInt32.le_iff_toNat_le.mp hsyms.1
  generalize hF : copyFold d0 (p + dWS (2 ^ k) + 2 * 2 ^ k + 131072) pbo
    (List.range' 0 (4 * st.lit_bufsize.toNat + 9)) (copyFold d0 (p + dWS (2 ^ k) + 2 * 2 ^ k) ho
      (List.range' 0 131072) (copyFold d0 (p + dWS (2 ^ k)) po (List.range' 0 (2 ^ k * 2))
        (copyFold d0 p wo (List.range' 0 (dWS (2 ^ k))) d))) = dF
  have hFs : dF.size = d.size := by rw [← hF]; simp only [copyFold_size]
  have hFin : ∀ q, q < 4 * st.lit_bufsize.toNat + 9 →
      dF[p + dWS (2 ^ k) + 2 * 2 ^ k + 131072 + q]! = d0[pbo + q]! := by
    intro q hq; rw [← hF]; exact copyFold_in _ _ _ _ _ q hq (by simp only [copyFold_size]; omega)
  have hHd : ∀ q, q < 131072 → dF[p + dWS (2 ^ k) + 2 * 2 ^ k + q]! = d0[ho + q]! := by
    intro q hq; rw [← hF]
    rw [copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)]
    exact copyFold_in _ _ _ _ _ q hq (by simp only [copyFold_size]; omega)
  have hPv : ∀ q, q < 2 * 2 ^ k → dF[p + dWS (2 ^ k) + q]! = d0[po + q]! := by
    intro q hq; rw [← hF]
    rw [copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)]
    rw [copyFold_get _ _ _ _ _ _ (fun x hx => by simp only [List.mem_range'_1] at hx; omega)]
    exact copyFold_in _ _ _ _ _ q (by omega) (by simp only [copyFold_size]; omega)
  have hpbz := c.pout
  have hpsym := c.psym
  have hdescs := c.descs
  simp only [dview] at hpbz hpsym hdescs
  refine Sat.pure ⟨?_, ?_, fun _ => ⟨?_, _, nb, _, SH_streams _ _ _ _ _ _, rfl, by omega, SH_dstate _ _ _ _ _ _,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, id⟩, fun b1 d1 d2 hb1 hb2 =>
      ⟨rfl, by rw [hwk']; omega, fun ho1 po1 hh1 hp1 => ?_⟩⟩⟩
  · refine dframe_of (fun k' hk => ?_) hBg.1 (fun c' hc => ?_) hBg.2.1 hBg.2.2.1 hBg.2.2.2.1 hBg.2.2.2.2.1
      hBg.2.2.2.2.2
    · simp only [SH, upd_ne _ _ _ _ hk, hBs]
    · have hc' : c' ≠ nb := by omega
      simp only [SH, upd_ne _ _ _ _ hc']
      exact hBo c' hc'
  · refine hsrc _ ?_ ?_ ?_ ?_
    · simp only [SH, upd_ne _ _ _ _ (Ne.symm hji), hBs]
    · simp only [SH, upd_ne _ _ _ _ hbn]; exact (hBo b hbn).1
    · simp only [SH, upd_ne _ _ _ _ hbn]; exact (hBo b hbn).2.2.2.1
    · simp only [SH]; exact (hBo b hbn).2.2.2.2
  · refine ⟨j, _, nb, _, _, rfl, SH_streams _ _ _ _ _ _, rfl, SH_dstate _ _ _ _ _ _,
      by simp only [Heap.dallocsOf, SH_bytes, SH_dallocs]; exact hY, ?_⟩
    exact {
      zalloc := c.zalloc
      zfree := c.zfree
      strm := rfl
      alloc_bufs := rfl
      al_state := rfl
      al_zfree := by show Ival.val z.zfree = _; rw [c.zfree]
      al_buf := rfl
      status_lo := c.status_lo
      status_hi := c.status_hi
      wrap := c.wrap
      gzhead := c.gzhead
      w_size := c.w_size
      pbuf := ⟨_, rfl⟩
      head := ⟨_, dF, SH_bytes _ _ _ _ _ _, rfl, by omega⟩
      level := c.level
      trees := c.trees
      sizes := c.sizes
      lay := ⟨dF, _, _, _, _, SH_bytes _ _ _ _ _ _, rfl, rfl, rfl, rfl, by simp only [dview, hwsz, hwb]; omega,
        by simp only [dview, hwk']; omega, by omega, by simp only [dview]; omega, rfl, _, rfl, by omega,
        by simp only [dview]; omega⟩
      pout := fun e => by
        have := hpbz e
        rw [hpoo, hpbo] at this
        obtain rfl : poo = pbo := by injection this with e; injection e
        simp only [dview, Nat.sub_self, Nat.add_zero]
      syms := c.syms
      bits := c.bits
      look := c.look
      strategy := c.strategy
      fns := c.fns
      symv := ⟨dF, _, SH_bytes _ _ _ _ _ _, rfl, DeflateCopy.SymOk.shift hsym fun q (hq : q < st.sym_next.toNat) => by
        have e := hFin (st.lit_bufsize.toNat + 8 + q) (by omega)
        simp only [← Nat.add_assoc] at e ⊢
        exact e⟩
      psym := fun hn => by
        obtain ⟨pbo1, poo1, e1, e2, e3⟩ := hpsym hn
        rw [hpbo] at e1; rw [hpoo] at e2
        obtain rfl : pbo = pbo1 := by injection e1 with e; injection e
        obtain rfl : poo = poo1 := by injection e2 with e; injection e
        exact ⟨_, _, rfl, rfl, by simp only [dview]; omega⟩
      hdr := c.hdr
      bstart := c.bstart
      ins := c.ins
      wpow := c.wpow
      lmod := c.lmod
      lpow := c.lpow
      scratch := c.scratch
      blk := c.blk
      fe_mod := c.fe_mod
      fe_hi := c.fe_hi
      bs_lo := c.bs_lo
      descs := ⟨rfl, hdescs.2.1, rfl, hdescs.2.2.2.1, rfl, hdescs.2.2.2.2.2⟩ }
  · rw [hho] at hh1; rw [hpo] at hp1
    simp only [Ival.val.injEq, Ptr.ref.injEq, BRef.heap.injEq] at hh1 hp1
    obtain ⟨rfl, rfl⟩ := hh1
    obtain ⟨-, rfl⟩ := hp1
    obtain rfl := Option.some.inj (hd0.symm.trans hb1)
    rw [SH_bytes] at hb2; obtain rfl := Option.some.inj hb2
    exact ⟨_, _, rfl, rfl, hHd, fun q hq => hPv q (by rw [hwk'] at hq; omega)⟩

/-- On a heap that records a deflate object in the block the allocator hands out next, the copy faults. -/
theorem copy_fault {h : Heap} {i j : Nat} {z zd : ZStream} {b : Nat} {st : DeflateState} {al : DeflateAllocs}
    (L : DLive h i z b st) (c : DCore h (some i) z b (dview st) al) (hzd : h.streams j = some zd) (hji : j ≠ i)
    (hok : h.allocOk h.nalloc = true) (hx : ¬ (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none)) :
    Fl h (deflateCopy (some j) (some i)) := by
  have hne : (some j == some i) = false := by simp [hji]
  let H1 : Heap := { h with streams := upd h.streams j (some z) }
  have ecs : copyStream (some j) (some i) h = .ok ((), H1) := by
    simp [copyStream, bind_app, hne, ldStream_app L.hz, ldStream_app hzd, stStream, hzd, H1]
  have hst1 : H1.dstate b = some st := L.dstate
  obtain ⟨k, hk1, hk2, hwk⟩ := c.wpow
  have hctz : W_BITS st H1 = .ok (UInt32.ofNat k, H1) := by
    have hwk' : st.w_size.toNat = 2 ^ k := hwk
    simp only [W_BITS, ctz_pow hk1 hk2 hwk']; rfl
  have hza1 : H1.streams j = some z := by simp [H1]
  have hn : (UInt32.ofNat k).toInt32.toInt = k := by
    have : k < 2 ^ 31 := by omega
    rw [u32_toInt32_toInt _ (by rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]; omega),
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
  obtain ⟨_, _, _, hl1, hl2, _, _⟩ := c.sizes
  have hl3 : st.lit_bufsize.toNat % 16 = 0 := c.lmod
  simp only [dview] at hl1 hl2 hl3
  have hl : st.lit_bufsize.toInt32.toInt = st.lit_bufsize.toNat := u32_toInt32_toInt _ (by omega)
  have hx' : H1.dstates H1.nextBlk ≠ none ∨ H1.dallocs H1.nextBlk ≠ none := by
    by_cases a : h.dstates h.nextBlk = none
    · exact Or.inr fun e => hx ⟨a, e⟩
    · exact Or.inl a
  unfold deflateCopy
  refine Fl.bind_sat (Sat.of_eq L.check ?_)
  simp only [Bool.false_or, show (some j == (none : StreamPtr)) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine Fl.bind_sat (Sat.of_eq L.stateOf ?_)
  refine Fl.bind_sat (Sat.of_eq ecs ?_)
  refine Fl.bind_sat (Sat.of_eq (ldDState_app hst1) ?_)
  refine Fl.bind_sat (Sat.of_eq hctz ?_)
  exact Fl.bind_now (alloc_fault (h := H1) hza1 c.zalloc hok hx' _ _ k st.lit_bufsize.toNat hn hk1 hk2 hl hl1 hl2
    hl3)

theorem copy_none {h : Heap} {src : StreamPtr} {v : Bool} (hc : deflateStateCheck src h = .ok (v, h)) :
    C.run (deflateCopy none src) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, deflateCopy, bind_app, hc]

theorem copy_noState {h : Heap} {src : StreamPtr} (hn : DNoState h src) (dst : StreamPtr) :
    C.run (deflateCopy dst src) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, deflateCopy, bind_app, show deflateStateCheck src h = .ok (true, h) from stateCheck_noState hn]

/-- The destination of a successful copy holds, in a block from `h.nextBlk` on, a state that agrees with the
source's on the fields of `SideEq`, with the source's hash chains (`ChainCopy`). -/
def CopySide (h h' : Heap) (src dst : StreamPtr) : Prop :=
  ∃ i j z b st z' nb st', src = some i ∧ dst = some j ∧ h.streams i = some z ∧ z.state = some b ∧
    h.dstate b = some st ∧ h'.streams j = some z' ∧ z'.state = some nb ∧ h.nextBlk ≤ nb ∧ h'.dstate nb = some st' ∧
    SideEq st st' ∧ ∀ d dF, h.bytes b = some d → h'.bytes nb = some dF → ChainCopy b nb d dF st st'

/-- `deflateCopy` on an invariant source and a distinct destination ready for initialisation: when it returns, the
source keeps its invariant and a successful copy has it. -/
theorem copy_inv {h h' : Heap} {src dst : StreamPtr} {r : Int32} (hv : DInv h src) (hdst : InitReady h dst)
    (hne : dst ≠ src) (e : C.run (deflateCopy dst src) h = .ok (r, h')) :
    DInv h' src ∧ (r = Z_OK → DInv h' dst ∧ CopySide h h' src dst) := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  rcases hdst with rfl | ⟨zd, ⟨j, rfl, hzd⟩, -, -⟩
  · rw [copy_none L.check] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact ⟨hv, fun e => absurd e (by decide)⟩
  have hji : j ≠ i := fun e => hne (by rw [e])
  by_cases hfr : h.allocOk h.nalloc = true → h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none
  · obtain ⟨r', h'', e', -, hi, hj⟩ := copy_run L hal c hzd hji hfr
    have : C.run (deflateCopy (some j) (some i)) h = .ok (r', h'') := e'
    rw [this] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    refine ⟨hi, fun e => ⟨(hj e).1, ?_⟩⟩
    obtain ⟨z', nb, st', h1, h2, h3, h4, h5, h6⟩ := (hj e).2
    exact ⟨i, j, z, b, st, z', nb, st', rfl, rfl, L.hz, L.hb, L.dstate, h1, h2, h3, h4, h5, fun d dF => h6 b d dF⟩
  · have hok : h.allocOk h.nalloc = true :=
      Classical.byContradiction fun hc => hfr (fun hh => absurd hh hc)
    have hx : ¬ (h.dstates h.nextBlk = none ∧ h.dallocs h.nextBlk = none) := fun hh => hfr (fun _ => hh)
    obtain ⟨err, he⟩ := copy_fault L c hzd hji hok hx
    have : C.run (deflateCopy (some j) (some i)) h = .error err := he
    rw [this] at e; cases e

/-- `deflateCopy` on a well-formed heap: no fault, only the destination record and the fresh block change. -/
theorem copy_safe {h : Heap} {src dst : StreamPtr} (hv : DInv h src) (hfr : DFreshBlocks h) (hdst : InitReady h dst)
    (hne : dst ≠ src) :
    ∃ r h', C.run (deflateCopy dst src) h = .ok (r, h') ∧ DFrame h h' (streamIds dst) [] [] [] := by
  obtain ⟨i, z, b, st, al, rfl, L, hal, c⟩ := live hv
  rcases hdst with rfl | ⟨zd, ⟨j, rfl, hzd⟩, -, -⟩
  · exact ⟨_, _, copy_none L.check, ⟨InflateInit.frame_refl h _ _ _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩⟩
  have hji : j ≠ i := fun e => hne (by rw [e])
  obtain ⟨r, h', e, f, -, -⟩ := copy_run L hal c hzd hji
    (fun _ => hfr.2 _ (Nat.le_refl _))
  exact ⟨r, h', e, f⟩

end ZlibNgF.Proof.DeflateCopy
