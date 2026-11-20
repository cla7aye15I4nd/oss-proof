import ZlibNgF.Proof.«public-gzopen»

/-!
# Non-vacuity of `GzReachable` (`ZlibNgF`)

A well-formed world whose file system holds the file `"f"`, and a heap with the CRC tables and the strings `"f"`,
`"rb"` and `"wb"`. `gzopen("f", "rb")` returns a file in mode `GZ_READ`, and `gzopen("f", "wb")` one in mode
`GZ_WRITE`; both are reachable (`GzReachable.gzopen`).

The two runs are computed: the mode loop of `gz_open` (a `gwhile` with fuel `2^64`) is unrolled for the three
characters it reads, and the rest of the run, on the concrete world and heap, is evaluated by the kernel
(`decide +kernel`).
-/

set_option autoImplicit false

namespace ZlibNgF.Proof.GzOpenNonvacuous
open C ZlibNgF.Spec ZlibNgF.Spec.Safety ZlibNg.Gz

/-- The heap: the CRC tables, `"f"` in block 0, `"rb"` in block 1, `"wb"` in block 2. -/
def nvHeap : Heap :=
  { crcTable := ZlibNg.Crc32Tbl.crc_table, x2nTable := ZlibNg.Crc32Tbl.x2n_table,
    bytes := upd (upd (upd .empty 0 (some #[102, 0])) 1 (some #[114, 98, 0])) 2 (some #[119, 98, 0]), nextBlk := 3 }

theorem nv_bytes : nvHeap.bytes =
    upd (upd (upd .empty 0 (some #[102, 0])) 1 (some #[114, 98, 0])) 2 (some #[119, 98, 0]) := rfl

theorem nv_b0 : nvHeap.bytes 0 = some #[102, 0] := by rw [nv_bytes]; simp [upd_ne]
theorem nv_b1 : nvHeap.bytes 1 = some #[114, 98, 0] := by rw [nv_bytes]; simp [upd_ne]
theorem nv_b2 : nvHeap.bytes 2 = some #[119, 98, 0] := by rw [nv_bytes]; simp

/-- The world: one regular file `"f"` of three bytes, every oracle regular. -/
def nvWorld : World := { fs := { names := #[(#[102], 0)], nodes := #[#[1, 2, 3]] } }

theorem go_succ {σ : Type} (cond : σ → G (Bool × σ)) (body : σ → G σ) (n : Nat) (s : σ) :
    gwhile.go cond body (n + 1) s =
      (do let (c, s) ← cond s; if c then gwhile.go cond body n (← body s) else pure s) := rfl

/-- The fuel less the three trips of the mode loop, kept folded. -/
def fuel3 : Nat := 2 ^ 64 - 3

theorem fuel_eq : fuel = fuel3 + 1 + 1 + 1 := by decide

/-- The result of `gzopen("f", mode)` with the mode string in block `k`. -/
def nvRun (k : Nat) := gzopen (.ref (.heap 0) 0) (.ref (.heap k) 0) nvWorld nvHeap

theorem run_read : ((nvRun 1).toOption.map fun x => (x.1.1, x.1.2.gz x.2 3 |>.map (·.mode))) =
    some (some 3, some GZ_READ) := by
  unfold nvRun gzopen gz_open gwhile
  simp only [fuel_eq]
  simp only [go_succ]
  decide +kernel

theorem run_write : ((nvRun 2).toOption.map fun x => (x.1.1, x.1.2.gz x.2 3 |>.map (·.mode))) =
    some (some 3, some GZ_WRITE) := by
  unfold nvRun gzopen gz_open gwhile
  simp only [fuel_eq]
  simp only [go_succ]
  decide +kernel

theorem str_bound : ∀ (i : Nat) (d : Array UInt8), strTable[i]?.map Heap.litBytes = some d → d.size < 2 ^ 63 := by
  intro i d hd
  cases hs : strTable[i]? with
  | none => rw [hs] at hd; cases hd
  | some s =>
    rw [hs] at hd; cases hd
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hs
    have : ∀ j, j < strTable.size → ∀ hj : j < strTable.size, (Heap.litBytes strTable[j]).size < 2 ^ 63 := by
      decide +kernel
    exact this i hi hi

theorem nv_wf : GzWF nvWorld nvHeap := by
  refine ⟨⟨rfl, rfl⟩, ⟨fun b hb => ?_, fun b _ => ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b⟩⟩, fun r d hd => ?_,
    fun b _ => Tbl.get_empty_opt b, fun b s hs => ?_, by decide, fun d hd => ?_, fun n v hv => ?_⟩
  · have h3 : 3 ≤ b := hb
    refine ⟨Tbl.get_empty_opt b, Tbl.get_empty_opt b, ?_⟩
    show upd (upd (upd .empty 0 (some #[102, 0])) 1 (some #[114, 98, 0])) 2 (some #[119, 98, 0]) b = none
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega)]
    exact Tbl.get_empty_opt b
  · cases r with
    | heap c =>
      have hd' : upd (upd (upd .empty 0 (some #[102, 0])) 1 (some #[114, 98, 0])) 2 (some #[119, 98, 0]) c = some d := hd
      by_cases e2 : c = 2
      · subst e2; rw [upd_same] at hd'; cases hd'; decide
      · rw [upd_ne _ _ _ _ e2] at hd'
        by_cases e1 : c = 1
        · subst e1; rw [upd_same] at hd'; cases hd'; decide
        · rw [upd_ne _ _ _ _ e1] at hd'
          by_cases e0 : c = 0
          · subst e0; rw [upd_same] at hd'; cases hd'; decide
          · rw [upd_ne _ _ _ _ e0, Tbl.get_empty_opt] at hd'; cases hd'
    | const c =>
      have hd' : (Tbl.empty : Tbl (Option (Array UInt8))) c = some d := hd
      rw [Tbl.get_empty_opt] at hd'; cases hd'
    | str k => exact str_bound k d hd
  · unfold World.gz at hs
    have : (Tbl.empty : Tbl (Option GzState)) b = none := Tbl.get_empty_opt b
    split at hs
    · simp [nvWorld, this] at hs
    · cases hs
  · have : d = #[1, 2, 3] := by simpa [nvWorld] using hd
    subst this; decide
  · simp [nvWorld] at hv

theorem nv_path : CStringLen nvHeap (.ref (.heap 0) 0) 1 :=
  ⟨.heap 0, 0, #[102, 0], rfl, nv_b0, by decide, by decide,
    fun i hi => by have : i = 0 := by omega
                   subst this; decide⟩

theorem nv_mode (k : Nat) (hk : k = 1 ∨ k = 2) :
    CStringLen nvHeap (.ref (.heap k) 0) 2 := by
  rcases hk with rfl | rfl
  · refine ⟨.heap 1, 0, #[114, 98, 0], rfl, nv_b1, by decide,
      by decide, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide
  · refine ⟨.heap 2, 0, #[119, 98, 0], rfl, nv_b2, by decide,
      by decide, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide

/-- A run with the computed result. -/
theorem nv_reach (k : Nat) (hk : k = 1 ∨ k = 2) (m : Int32)
    (hr : ((nvRun k).toOption.map fun x => (x.1.1, x.1.2.gz x.2 3 |>.map (·.mode))) = some (some 3, some m)) :
    ∃ (w' : World) (h' : Heap) (f : GzPtr),
      GzRun (gzopen (.ref (.heap 0) 0) (.ref (.heap k) 0)) nvWorld nvHeap f w' h' ∧ f ≠ none ∧ GzReachable w' h' f ∧
      (∃ b s, f = some b ∧ w'.gz h' b = some s ∧ s.mode = m) := by
  cases e : nvRun k with
  | error x => rw [e] at hr; simp [Except.toOption] at hr
  | ok v =>
    obtain ⟨⟨f, w'⟩, h'⟩ := v
    rw [e] at hr
    simp [Except.toOption] at hr
    obtain ⟨rfl, hm⟩ := hr
    obtain ⟨s, hs, rfl⟩ := hm
    have run : GzRun (gzopen (.ref (.heap 0) 0) (.ref (.heap k) 0)) nvWorld nvHeap (some 3) w' h' := e
    exact ⟨w', h', some 3, run, by simp,
      GzReachable.gzopen _ _ _ _ _ _ _ nv_wf ⟨1, nv_path⟩ ⟨2, nv_mode k hk⟩ run (by simp), 3, s, rfl, hs, rfl⟩

theorem gzopen_read_nonvacuous : Goal.gzopen_read_nonvacuous := by
  obtain ⟨w', h', f, e, hne, hr, hm⟩ := nv_reach 1 (Or.inl rfl) GZ_READ run_read
  exact ⟨nvWorld, nvHeap, _, _, w', h', f, nv_wf, nv_path, nv_mode 1 (Or.inl rfl), e, hne, hr, hm⟩

theorem gzopen_write_nonvacuous : Goal.gzopen_write_nonvacuous := by
  obtain ⟨w', h', f, e, hne, hr, hm⟩ := nv_reach 2 (Or.inr rfl) GZ_WRITE run_write
  exact ⟨nvWorld, nvHeap, _, _, w', h', f, nv_wf, nv_path, nv_mode 2 (Or.inr rfl), e, hne, hr, hm⟩

end ZlibNgF.Proof.GzOpenNonvacuous
