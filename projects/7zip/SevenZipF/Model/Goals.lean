import SevenZipF.Model.TopDown

/-!
# Top-down model invariant goals (`SevenZipF.Model`)

Proved mathematical and state-machine invariants over the top-down models of `.7z` folder DAGs,
solid extraction caches, BCJ2 4-stream decoding, the PPMd7 arena sub-allocator, and LZMA/LZMA2.
-/

namespace SevenZipF.Model
open _root_.SevenZipF.Model.Runtime Archive Bcj2 Ppmd7 Lzma

def Goal.model_folder_dag_acyclic : Prop :=
  ∀ (f : SzFolder), CheckSupportedFolderTopology f → FolderDAGInv f

def Goal.model_extract_cache_coherence : Prop :=
  ∀ (ar : ArchiveModel) (fileIndex : Nat) (cache : ExtractCache)
    (allocOk decodeOk crcMatches : Bool),
    (∀ fi, ar.fileToFolder fileIndex = some fi → fi < ar.numFolders) →
    CacheCoherentInv ar cache →
    let (cache', res) := szArExExtractFixed ar fileIndex cache allocOk decodeOk crcMatches
    CacheCoherentInv ar cache' ∧ (∀ validFlag, res = .ok validFlag → validFlag = true)

def Goal.model_bcj2_overlap_init : Prop :=
  ∀ (outSize tempSize3 tempSizes0 tempSizes1 s3Size : Nat),
    tempSizes0 % 4 = 0 →
    tempSizes1 % 4 = 0 →
    tempSize3 + tempSizes0 + tempSizes1 = outSize →
    Bcj2OverlapInv
      { bufMain := outSize - tempSize3
        limMain := outSize
        bufCall := 0
        limCall := tempSizes0
        bufJump := 0
        limJump := tempSizes1
        bufRc := 0
        limRc := s3Size
        dest := 0
        destLim := outSize
        pendingTemp := 0 }

def Goal.model_ppmd7_arena_init : Prop :=
  ∀ (size : Nat), PPMD7_MIN_MEM_SIZE ≤ size → ArenaInv (restartModelArena size)

def Goal.model_ppmd7_splitBlock_conservation : Prop :=
  ∀ (oldIndx newIndx : Nat),
    newIndx < oldIndx →
    oldIndx < PPMD_NUM_INDEXES →
    let nu := indx2Units oldIndx - indx2Units newIndx
    let i0 := units2Indx nu
    1 ≤ nu ∧ nu ≤ 127 ∧ i0 < PPMD_NUM_INDEXES ∧
    (if indx2Units i0 = nu then
      indx2Units newIndx + indx2Units i0 = indx2Units oldIndx
     else
      1 ≤ i0 ∧
      let k := indx2Units (i0 - 1)
      k < nu ∧
      let remIdx := nu - k - 1
      remIdx < PPMD_NUM_INDEXES ∧
      indx2Units newIndx + k + indx2Units remIdx = indx2Units oldIndx)

def Goal.model_lzma_fast_lookahead_bounds : Prop :=
  ∀ (inSize buf stepBytes : Nat),
    LZMA_REQUIRED_INPUT_MAX ≤ inSize →
    buf < inSize - LZMA_REQUIRED_INPUT_MAX →
    stepBytes ≤ LZMA_REQUIRED_INPUT_MAX →
    buf + stepBytes < inSize

def Goal.model_lzma2_control_guards : Prop :=
  ∀ (s : Lzma2HeaderState) (b : UInt8),
    s.phase = .control → Lzma2StateInv s →
    let s' := lzma2StepControl s b
    Lzma2StateInv s' ∧
    (s'.phase = .unpack0 ∧ (b &&& 0x80) = 0 →
      s'.unpackSize = 0 ∧ s'.dicInitialized = true) ∧
    (s'.phase = .unpack0 ∧ (b &&& 0x80) ≠ 0 →
      s'.dicInitialized = true ∧ s'.stateAndPropsInitialized = true)

theorem model_folder_dag_acyclic_proved : Goal.model_folder_dag_acyclic :=
  checkSupportedFolder_implies_DAG

theorem model_extract_cache_coherence_proved : Goal.model_extract_cache_coherence :=
  fixed_extract_preserves_cache_coherence

theorem model_bcj2_overlap_init_proved : Goal.model_bcj2_overlap_init :=
  szFolderDecode2_establishes_bcj2OverlapInv

theorem model_ppmd7_arena_init_proved : Goal.model_ppmd7_arena_init :=
  restartModel_establishes_arenaInv

theorem model_ppmd7_splitBlock_conservation_proved : Goal.model_ppmd7_splitBlock_conservation :=
  ppmd7_splitBlock_conserves_units_and_bounds

theorem model_lzma_fast_lookahead_bounds_proved : Goal.model_lzma_fast_lookahead_bounds :=
  lzma_fast_loop_lookahead_in_bounds

theorem model_lzma2_control_guards_proved : Goal.model_lzma2_control_guards :=
  lzma2StepControl_preserves_and_guards

end SevenZipF.Model
