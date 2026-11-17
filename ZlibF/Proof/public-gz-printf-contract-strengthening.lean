import ZlibF.Spec.Safety.GzCalls

/-!
# The gz safety goals with the contract model of vsnprintf imply their former statements

The caller-format `vsnprintf` of `gzvprintf` is an external call modelled by its C contract, and `GzArguments` asks
for a `gzprintf` format only past the mode test of `gzvprintf`, where it is read: a string, and pointer arguments
into live blocks. `GzArguments` is weaker than before for every format, so every `GzHistory` of before is a
history now, and each per-call gz safety goal, `Goal.gz_sequence_safety` among them, now covers more calls.

Each former statement is restated here as `Old.<goal>` over `OldGzArguments` and `OldGzHistory`, with one
clause added to the former `gzprintf` arguments: every pointer argument points into a live block. Without it the
former statement is false for the corrected model, which faults on a pointer argument into a freed block (an
indeterminate value, C17 6.2.4p2) where the former model ignored an argument that the format did not consume.
Each new goal implies its `Old` statement.
-/

namespace ZlibF.Spec.Public.PrintfContractStrengthening
open C Zlib.GzFs ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `GzArguments` as stated before, with live pointer arguments of `gzprintf`. -/
def OldGzArguments (h : Heap) (i : Nat) (s : GzState) : Call → Prop
  | .gzread _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat true
  | .gzwrite _ p n =>
      if n.toNat ≥ 2 ^ 31 then True else GzRange h i s p n.toNat false
  | .gzfread p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) true
  | .gzfwrite p size n _ =>
      if size.toNat * n.toNat ≥ 2 ^ 64 then True else GzRange h i s p (size.toNat * n.toNat) false
  | .gzgets _ p n => if n.toInt < 1 ∨ p = .null then True else GzRange h i s p n.toInt.toNat true
  | .gzputs _ p => ∃ xs, CString h p xs ∧ GzRange h i s p (xs.length + 1) false
  | .gzprintf _ p args | .gzvprintf _ p args => (∃ xs, Formatted h p args xs) ∧
      -- added: every pointer argument points into a live block (passing a dangling one is undefined)
      (∀ q, VaArg.str q ∈ args → ∀ b o, q = .ref (.blk b) o → ∃ a, h.bytes b = some a) ∧
      (∀ b, ByteRoot p b → ¬ GzOwned h i s b) ∧
      ∀ q, VaArg.str q ∈ args → ∀ b, ByteRoot q b → ¬ GzOwned h i s b
  | .gzerror _ p => p = .null ∨ GzRange h i s p 4 true
  | _ => True

/-- `GzHistory` as stated before, over `OldGzArguments`. -/
inductive OldGzHistory : Heap → Fs → Nat → Prop
  | open {h after fs fs' path mode i name flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h path name → CString h mode flags →
      Zlib.Gzlib.gzopen path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      OldGzHistory after fs' i
  | open64 {h after fs fs' path mode i name flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h path name → CString h mode flags →
      Zlib.Gzlib.gzopen64 path mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      OldGzHistory after fs' i
  | dopen {h after fs fs' fd mode i flags} :
      Fresh h → Zlib.Gzlib.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
      FileSystem fs → CString h mode flags →
      Zlib.Gzlib.gzdopen fd mode fs h = .ok ((some (.in_gzstate_x i), fs'), after) →
      OldGzHistory after fs' i
  | step {h after fs fs' i s call value} : OldGzHistory h fs i → h.gzstates i = some s →
      GzOperation i call → OldGzArguments h i s call →
      call.execute fs h = .ok ((value, fs'), after) → OldGzHistory after fs' i
  | getcMacro {h after fs fs' i s value} : OldGzHistory h fs i → h.gzstates i = some s →
      Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) → OldGzHistory after fs' i
  | caller {h after fs i s} : OldGzHistory h fs i → h.gzstates i = some s →
      GzCallerFrame h after i s → ZlibF.PlatformMemory.ByteObjectsFit after → OldGzHistory after fs i
  | world {h fs fs' i s} : OldGzHistory h fs i → h.gzstates i = some s → GzWorldStep fs fs' s.fd →
      OldGzHistory h fs' i

/-- `Goal.gz_sequence_safety` as stated before. -/
def Old.gz_sequence_safety : Prop :=
  (∀ h fs i, OldGzHistory h fs i → FileSystem fs ∧ ∃ s, GzInv h i s) ∧
  (∀ h fs i s call, OldGzHistory h fs i → h.gzstates i = some s → GzOperation i call → OldGzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)) ∧
  (∀ h fs i s, OldGzHistory h fs i → h.gzstates i = some s →
    (∀ e, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .error e → e = .outOfFuel) ∧
    ((s.x.have = 0 → NeedsReadBound (.gzgetc (some (.in_gzstate_x i))) → ReadsFinite fs s.fd) →
      ∃ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after)) ∧
  (∀ h fs i s errnum, OldGzHistory h fs i → h.gzstates i = some s →
    OldGzArguments h i s (.gzerror (some (.in_gzstate_x i)) errnum) →
    ∀ (value : BPtr) fs' after,
      (Call.gzerror (some (.in_gzstate_x i)) errnum).execute fs h = .ok ((value, fs'), after) →
      ∃ t, CString after value t) ∧
  (∀ h fs i s call, OldGzHistory h fs i → h.gzstates i = some s → GzCloseCall i call →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))) ∧
  GzOpenSafe Zlib.Gzlib.gzopen ∧ GzOpenSafe Zlib.Gzlib.gzopen64 ∧ GzDopenSafe

def OldGzCallSafety (selects : Call → Prop) : Prop :=
  ∀ h fs i s call, OldGzHistory h fs i → h.gzstates i = some s → selects call → GzOperation i call →
    OldGzArguments h i s call →
    (∀ e, call.execute fs h = .error e → e = .outOfFuel) ∧
    ((NeedsReadBound call → ReadsFinite fs s.fd) →
      ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, call.execute fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s call fs' after)

def OldGzCloseCallSafety (selects : Call → Prop) : Prop :=
  ∀ h fs i s call, OldGzHistory h fs i → h.gzstates i = some s → selects call → GzCloseCall i call →
    ∃ value fs' after, call.execute fs h = .ok ((value, fs'), after) ∧
      ((CloseRefuses s call ∧ after = h ∧ fs' = fs) ∨ (¬ CloseRefuses s call ∧ GzReleased h after fs fs' i s))

def Old.gzbuffer_safety : Prop :=
  (∀ (h : Heap) size, Zlib.Gzlib.gzbuffer none size h = .ok (-1, h)) ∧
  OldGzCallSafety (fun | .gzbuffer .. => True | _ => False)

def Old.gzclearerr_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gzclearerr none h = .ok ((), h)) ∧
  OldGzCallSafety (fun | .gzclearerr .. => True | _ => False)

def Old.gzdirect_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzdirect none fs h = .ok ((0, fs), h)) ∧
  OldGzCallSafety (fun | .gzdirect .. => True | _ => False)

def Old.gzeof_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gzeof none h = .ok (0, h)) ∧
  OldGzCallSafety (fun | .gzeof .. => True | _ => False)

def Old.gzflush_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) flush,
    Zlib.Gzwrite.gzflush none flush fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCallSafety (fun | .gzflush .. => True | _ => False)

def Old.gzfread_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzread.gzfread buf size nitems none fs h = .ok ((0, fs), h)) ∧
  OldGzCallSafety (fun | .gzfread .. => True | _ => False)

def Old.gzfwrite_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf size nitems,
    Zlib.Gzwrite.gzfwrite buf size nitems none fs h = .ok ((0, fs), h)) ∧
  OldGzCallSafety (fun | .gzfwrite .. => True | _ => False)

def Old.gzgetc__safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc_ none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzgetc_ .. => True | _ => False)

def Old.gzgets_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzgets none buf len fs h = .ok ((.null, fs), h)) ∧
  OldGzCallSafety (fun | .gzgets .. => True | _ => False)

def Old.gzoffset_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzoffset .. => True | _ => False)

def Old.gzoffset64_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzoffset64 none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzoffset64 .. => True | _ => False)

def Old.gzprintf_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCallSafety (fun | .gzprintf .. => True | _ => False)

def Old.gzvprintf_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) format (va : List VaArg),
    Zlib.Gzwrite.gzvprintf none format va fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCallSafety (fun | .gzvprintf .. => True | _ => False)

def Old.gzputc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzwrite.gzputc none c fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzputc .. => True | _ => False)

def Old.gzputs_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) str, Zlib.Gzwrite.gzputs none str fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzputs .. => True | _ => False)

def Old.gzread_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzread.gzread none buf len fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzread .. => True | _ => False)

def Old.gzrewind_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzlib.gzrewind none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzrewind .. => True | _ => False)

def Old.gzseek_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek none offset whence fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzseek .. => True | _ => False)

def Old.gzseek64_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) offset whence,
    Zlib.Gzlib.gzseek64 none offset whence fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzseek64 .. => True | _ => False)

def Old.gzsetparams_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) level strategy,
    Zlib.Gzwrite.gzsetparams none level strategy fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCallSafety (fun | .gzsetparams .. => True | _ => False)

def Old.gztell_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gztell none h = .ok (-1, h)) ∧
  OldGzCallSafety (fun | .gztell .. => True | _ => False)

def Old.gztell64_safety : Prop :=
  (∀ h : Heap, Zlib.Gzlib.gztell64 none h = .ok (-1, h)) ∧
  OldGzCallSafety (fun | .gztell64 .. => True | _ => False)

def Old.gzungetc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) c, Zlib.Gzread.gzungetc c none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzungetc .. => True | _ => False)

def Old.gzwrite_safety : Prop :=
  (∀ (fs : Fs) (h : Heap) buf len, Zlib.Gzwrite.gzwrite none buf len fs h = .ok ((0, fs), h)) ∧
  OldGzCallSafety (fun | .gzwrite .. => True | _ => False)

def Old.gzgetc_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzgetc none fs h = .ok ((-1, fs), h)) ∧
  OldGzCallSafety (fun | .gzgetc .. => True | _ => False) ∧
  (∀ h fs i s, OldGzHistory h fs i → h.gzstates i = some s →
    (∀ e, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .error e → e = .outOfFuel) ∧
    ((s.x.have = 0 → NeedsReadBound (.gzgetc (some (.in_gzstate_x i))) → ReadsFinite fs s.fd) →
      ∃ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after)) ∧
    (∀ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after))

def Old.gzerror_safety : Prop :=
  (∀ (h : Heap) errnum, Zlib.Gzlib.gzerror none errnum h = .ok (.null, h)) ∧
  OldGzCallSafety (fun | .gzerror .. => True | _ => False) ∧
  (∀ h fs i s errnum, OldGzHistory h fs i → h.gzstates i = some s →
    OldGzArguments h i s (.gzerror (some (.in_gzstate_x i)) errnum) →
    ∀ (value : BPtr) fs' after,
      (Call.gzerror (some (.in_gzstate_x i)) errnum).execute fs h = .ok ((value, fs'), after) →
      ∃ t, CString after value t)

def Old.gzclose_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzclose.gzclose none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCloseCallSafety (fun | .gzclose .. => True | _ => False)

def Old.gzclose_r_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzread.gzclose_r none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCloseCallSafety (fun | .gzclose_r .. => True | _ => False)

def Old.gzclose_w_safety : Prop :=
  (∀ (fs : Fs) (h : Heap), Zlib.Gzwrite.gzclose_w none fs h = .ok ((Z_STREAM_ERROR, fs), h)) ∧
  OldGzCloseCallSafety (fun | .gzclose_w .. => True | _ => False)

theorem args_of_old {h : Heap} {i : Nat} {s : GzState} : ∀ c, OldGzArguments h i s c → GzArguments h i s c := by
  intro c
  cases c <;> first
    | (rintro ⟨⟨xs, fmt, hc, -⟩, live, a, b⟩; exact ⟨fun _ => ⟨⟨fmt, hc⟩, live⟩, a, b⟩)
    | exact id

theorem history_of_old {h : Heap} {fs : Fs} {i : Nat} (hh : OldGzHistory h fs i) : GzHistory h fs i := by
  induction hh with
  | «open» a b c d e f g r => exact .open a b c d e f g r
  | open64 a b c d e f g r => exact .open64 a b c d e f g r
  | dopen a b c d e f r => exact .dopen a b c d e f r
  | step _ hs ho ha hr ih => exact .step ih hs ho (args_of_old _ ha) hr
  | getcMacro _ hs hr ih => exact .getcMacro ih hs hr
  | caller _ hs hf hb ih => exact .caller ih hs hf hb
  | world _ hs hw ih => exact .world ih hs hw

theorem call_of_new {sel : Call → Prop} (g : GzCallSafety sel) : OldGzCallSafety sel :=
  fun h fs i s call hh hs hsel ho ha => g h fs i s call (history_of_old hh) hs hsel ho (args_of_old _ ha)

theorem close_of_new {sel : Call → Prop} (g : GzCloseCallSafety sel) : OldGzCloseCallSafety sel :=
  fun h fs i s call hh hs hsel hc => g h fs i s call (history_of_old hh) hs hsel hc

/-- The new `Goal.gz_sequence_safety` implies the former one. -/
theorem gz_sequence_safety_strengthens : Goal.gz_sequence_safety → Old.gz_sequence_safety :=
  fun ⟨c1, c2, c3, c4, c5, c6⟩ =>
    ⟨fun h fs i hh => c1 h fs i (history_of_old hh),
     fun h fs i s call hh hs ho ha => c2 h fs i s call (history_of_old hh) hs ho (args_of_old _ ha),
     fun h fs i s hh hs => c3 h fs i s (history_of_old hh) hs,
     fun h fs i s e hh hs ha => c4 h fs i s e (history_of_old hh) hs (args_of_old _ ha),
     fun h fs i s call hh hs hc => c5 h fs i s call (history_of_old hh) hs hc, c6⟩

/-- The new `Goal.gzbuffer_safety` implies the former one. -/
theorem gzbuffer_safety_strengthens : Goal.gzbuffer_safety → Old.gzbuffer_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzclearerr_safety` implies the former one. -/
theorem gzclearerr_safety_strengthens : Goal.gzclearerr_safety → Old.gzclearerr_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzdirect_safety` implies the former one. -/
theorem gzdirect_safety_strengthens : Goal.gzdirect_safety → Old.gzdirect_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzeof_safety` implies the former one. -/
theorem gzeof_safety_strengthens : Goal.gzeof_safety → Old.gzeof_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzflush_safety` implies the former one. -/
theorem gzflush_safety_strengthens : Goal.gzflush_safety → Old.gzflush_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzfread_safety` implies the former one. -/
theorem gzfread_safety_strengthens : Goal.gzfread_safety → Old.gzfread_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzfwrite_safety` implies the former one. -/
theorem gzfwrite_safety_strengthens : Goal.gzfwrite_safety → Old.gzfwrite_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzgetc__safety` implies the former one. -/
theorem gzgetc__safety_strengthens : Goal.gzgetc__safety → Old.gzgetc__safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzgets_safety` implies the former one. -/
theorem gzgets_safety_strengthens : Goal.gzgets_safety → Old.gzgets_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzoffset_safety` implies the former one. -/
theorem gzoffset_safety_strengthens : Goal.gzoffset_safety → Old.gzoffset_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzoffset64_safety` implies the former one. -/
theorem gzoffset64_safety_strengthens : Goal.gzoffset64_safety → Old.gzoffset64_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzprintf_safety` implies the former one. -/
theorem gzprintf_safety_strengthens : Goal.gzprintf_safety → Old.gzprintf_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzvprintf_safety` implies the former one. -/
theorem gzvprintf_safety_strengthens : Goal.gzvprintf_safety → Old.gzvprintf_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzputc_safety` implies the former one. -/
theorem gzputc_safety_strengthens : Goal.gzputc_safety → Old.gzputc_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzputs_safety` implies the former one. -/
theorem gzputs_safety_strengthens : Goal.gzputs_safety → Old.gzputs_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzread_safety` implies the former one. -/
theorem gzread_safety_strengthens : Goal.gzread_safety → Old.gzread_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzrewind_safety` implies the former one. -/
theorem gzrewind_safety_strengthens : Goal.gzrewind_safety → Old.gzrewind_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzseek_safety` implies the former one. -/
theorem gzseek_safety_strengthens : Goal.gzseek_safety → Old.gzseek_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzseek64_safety` implies the former one. -/
theorem gzseek64_safety_strengthens : Goal.gzseek64_safety → Old.gzseek64_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzsetparams_safety` implies the former one. -/
theorem gzsetparams_safety_strengthens : Goal.gzsetparams_safety → Old.gzsetparams_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gztell_safety` implies the former one. -/
theorem gztell_safety_strengthens : Goal.gztell_safety → Old.gztell_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gztell64_safety` implies the former one. -/
theorem gztell64_safety_strengthens : Goal.gztell64_safety → Old.gztell64_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzungetc_safety` implies the former one. -/
theorem gzungetc_safety_strengthens : Goal.gzungetc_safety → Old.gzungetc_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzwrite_safety` implies the former one. -/
theorem gzwrite_safety_strengthens : Goal.gzwrite_safety → Old.gzwrite_safety := fun ⟨r, g⟩ => ⟨r, call_of_new g⟩

/-- The new `Goal.gzgetc_safety` implies the former one. -/
theorem gzgetc_safety_strengthens : Goal.gzgetc_safety → Old.gzgetc_safety :=
  fun ⟨r, g, m⟩ => ⟨r, call_of_new g, fun h fs i s hh hs => m h fs i s (history_of_old hh) hs⟩

/-- The new `Goal.gzerror_safety` implies the former one. -/
theorem gzerror_safety_strengthens : Goal.gzerror_safety → Old.gzerror_safety :=
  fun ⟨r, g, m⟩ => ⟨r, call_of_new g, fun h fs i s e hh hs ha => m h fs i s e (history_of_old hh) hs (args_of_old _ ha)⟩

/-- The new `Goal.gzclose_safety` implies the former one. -/
theorem gzclose_safety_strengthens : Goal.gzclose_safety → Old.gzclose_safety := fun ⟨r, g⟩ => ⟨r, close_of_new g⟩

/-- The new `Goal.gzclose_r_safety` implies the former one. -/
theorem gzclose_r_safety_strengthens : Goal.gzclose_r_safety → Old.gzclose_r_safety := fun ⟨r, g⟩ => ⟨r, close_of_new g⟩

/-- The new `Goal.gzclose_w_safety` implies the former one. -/
theorem gzclose_w_safety_strengthens : Goal.gzclose_w_safety → Old.gzclose_w_safety := fun ⟨r, g⟩ => ⟨r, close_of_new g⟩

end ZlibF.Spec.Public.PrintfContractStrengthening
