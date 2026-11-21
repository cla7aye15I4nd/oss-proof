import ZlibNgF.Proof.«public-inflate»
import ZlibNgF.Proof.«public-inflate-init»

/-!
# Non-vacuity of `inflate_safety` (`ZlibNgF`)

A heap with the CRC tables, one zero `z_stream` and two caller byte blocks (input and output). `inflateInit_` makes
the stream reachable, the caller points its buffers at the two blocks (a caller step), and the premises of
`inflate_safety` then hold, so one `inflate(Z_FINISH)` returns.
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.InflateNonvacuous
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Inflate ZlibNgF.Proof.InflateAlloc

/-- The caller's input: the zlib stream of the empty string. -/
def inBytes : Array UInt8 := #[0x78, 0x9c, 0x03, 0x00, 0x00, 0x00, 0x00, 0x01]

/-- The caller's output buffer. -/
def outBytes : Array UInt8 := #[0, 0, 0, 0, 0, 0, 0, 0]

/-- The CRC tables, one zero `z_stream`, and the input and output blocks `0` and `1`. -/
def callerHeap : Heap :=
  { crcTable := ZlibNg.Crc32Tbl.crc_table, x2nTable := ZlibNg.Crc32Tbl.x2n_table,
    streams := upd .empty 0 (some {}),
    bytes := upd (upd .empty 0 (some inBytes)) 1 (some outBytes), nextBlk := 2 }

theorem callerHeap_fresh : FreshBlocks callerHeap := by
  intro b hb
  have h0 : b ≠ 0 := by simp [callerHeap] at hb; omega
  have h1 : b ≠ 1 := by simp [callerHeap] at hb; omega
  refine ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b, ?_⟩
  show upd (upd .empty 0 (some inBytes)) 1 (some outBytes) b = none
  rw [upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h0]
  exact Tbl.get_empty_opt b

theorem callerHeap_bytes0 : callerHeap.bytes 0 = some inBytes := by
  show upd (upd .empty 0 (some inBytes)) 1 (some outBytes) 0 = some inBytes
  rw [upd_ne _ _ _ _ (by decide), upd_same]

theorem callerHeap_bytes1 : callerHeap.bytes 1 = some outBytes := by
  show upd (upd .empty 0 (some inBytes)) 1 (some outBytes) 1 = some outBytes
  rw [upd_same]

theorem callerHeap_crc : CrcGlobals callerHeap := ⟨rfl, rfl⟩

/-- `inflateInit_` with the library's version string and size runs `inflateInit2` with the default window bits
(on every heap, so that the concrete heap below is never unfolded). -/
theorem init_run {h h1 : Heap} (e : inflateInit2 (some 0) DEF_WBITS h = .ok (Z_OK, h1)) :
    C.run (inflateInit_ (some 0) (.ref (.str 0) 0) 112) h = .ok (Z_OK, h1) := by
  have hc : CHECK_VER_STSIZE (.ref (.str 0) 0) 112 h = .ok (false, h) := rfl
  simp only [C.run, inflateInit_, bind_app, hc, Bool.false_eq_true, ↓reduceIte]
  exact e

theorem inflate_nonvacuous : Goal.inflate_nonvacuous := by
  have hz : callerHeap.streams 0 = some {} := upd_same _ _ _
  obtain ⟨r0, h1, e, f, -, hr15, hst, -⟩ := init2_ok hz (Or.inl rfl) (Or.inl rfl)
    (Tbl.get_empty_opt _) (Tbl.get_empty_opt _) DEF_WBITS
  have hr : r0 = Z_OK := hr15 rfl rfl
  subst hr
  obtain ⟨z1, st1, hz1, hzs, hist, hhead, -, -⟩ := hst rfl
  have hrun := init_run e
  have hreach1 : InflateReachable h1 (some 0) := by
    refine InflateReachable.init callerHeap h1 (some 0) (.ref (.str 0) 0) 112
      (Or.inr ⟨{}, ⟨0, rfl, hz⟩, Or.inl rfl, Or.inl rfl⟩) (Or.inr ⟨.str 0, 0, _, rfl, rfl, ?_⟩) hrun
    simp [Heap.litBytes]
  -- the caller step: point the buffers at the two blocks
  let z2 : ZStream :=
    { z1 with
      next_in := .ref (.heap 0) 0
      avail_in := 8
      next_out := .ref (.heap 1) 0
      avail_out := 8 }
  let h2 : Heap := { h1 with streams := upd h1.streams 0 (some z2) }
  have hz2 : h2.streams 0 = some z2 := upd_same _ _ _
  have hreach2 : InflateReachable h2 (some 0) :=
    InflateReachable.caller h1 h2 (some 0) hreach1
      ⟨0, z1, z2, callerHeap.nextBlk, rfl, hz1, hz2, hzs, rfl, rfl, rfl, rfl,
        fun _ g _ hg => ⟨g, hg⟩, rfl, Nat.le_refl _⟩
  have hb0 : h2.bytes 0 = some inBytes := (f.old 0 (by show 0 < 2; decide)).2.2.trans callerHeap_bytes0
  have hb1 : h2.bytes 1 = some outBytes := (f.old 1 (by show 1 < 2; decide)).2.2.trans callerHeap_bytes1
  have hio : StreamIO h2 (some 0) := by
    refine ⟨z2, callerHeap.nextBlk, none, ⟨0, rfl, hz2⟩, hzs,
      ⟨callerHeap.nextBlk, st1, ⟨z2, ⟨0, rfl, hz2⟩, hzs⟩, hist, hhead⟩, Or.inl rfl,
      Or.inr ⟨.heap 0, 0, inBytes, rfl, hb0, by show 0 + (8 : UInt32).toNat ≤ 8; decide⟩,
      Or.inr ⟨1, 0, outBytes, rfl, hb1, by show 0 + (8 : UInt32).toNat ≤ 8; decide⟩,
      ?_, ?_⟩
    · intro i j a b hij ha hb
      have hl : ((z2.next_in, z2.avail_in.toNat) :: (z2.next_out, z2.avail_out.toNat) :: headerRanges h2 none) =
          [(.ref (.heap 0) 0, 8), (.ref (.heap 1) 0, 8)] := rfl
      rw [hl] at ha hb
      rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp at ha hb hij <;> subst ha <;> subst hb <;>
        simp [Disjoint]
    · intro r hr off
      have hl : ((z2.next_in, z2.avail_in.toNat) :: (z2.next_out, z2.avail_out.toNat) :: headerRanges h2 none) =
          [(.ref (.heap 0) 0, 8), (.ref (.heap 1) 0, 8)] := rfl
      rw [hl] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [callerHeap]
  have hcg : CrcGlobals h2 := ⟨f.crc.trans callerHeap_crc.1, f.x2n.trans callerHeap_crc.2⟩
  obtain ⟨r, h', hrun2, -⟩ := InflateTop.inflate_safety h2 (some 0) 4 hcg (Or.inr (Or.inr hreach2)) fun _ => hio
  exact ⟨h2, some 0, h', r, z2, hcg, hreach2, hio, ⟨0, rfl, hz2⟩, nofun, nofun,
    by show (0 : UInt32) < 8; decide, by show (0 : UInt32) < 8; decide, hrun2⟩

end ZlibNgF.Proof.InflateNonvacuous
