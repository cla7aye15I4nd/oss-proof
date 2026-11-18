import LibarchiveF.Model.Rar5TopDown
import LibarchiveF.Model.SevenZipTopDown

/-!
# Top-down model invariant goals (`LibarchiveF.Model`)

Proved state-machine, filter-queue, bitreader, folder-DAG, and PPMd7 invariants for `libarchive`'s
RAR5 and 7-Zip format decoders.
-/

namespace LibarchiveF.Model

def Goal.model_rar5_init_inv : Prop :=
  Rar5TopDown.Rar5RepInv Rar5TopDown.initState

def Goal.model_rar5_cleanup_preserves_inv : Prop :=
  ∀ (s : Rar5TopDown.Rar5State), Rar5TopDown.Rar5RepInv (Rar5TopDown.safeCleanupStep s).2

def Goal.model_rar5_skip_preserves_inv : Prop :=
  ∀ (s : Rar5TopDown.Rar5State),
    Rar5TopDown.Rar5RepInv s → Rar5TopDown.Rar5RepInv (Rar5TopDown.read_data_skip s).2

def Goal.model_rar5_throttle_no_deadlock : Prop :=
  ∀ (windowSize writePtr lastWritePtr : Int) (flt : Rar5TopDown.FilterInfo),
    windowSize > 0 →
    flt.blockLength ≤ windowSize / 2 →
    lastWritePtr ≤ flt.blockStart →
    lastWritePtr < writePtr →
    writePtr < flt.blockStart + flt.blockLength →
    min flt.blockStart writePtr = lastWritePtr →
    writePtr - lastWritePtr < windowSize / 2

def Goal.model_rar5_bitreader_progress : Prop :=
  ∀ (b : Rar5TopDown.BitReader) (n : Nat),
    b.bitAddr < 8 → 0 ≤ b.inAddr → 1 ≤ n →
    let b' := Rar5TopDown.skipBits b n
    b'.bitAddr < 8 ∧ 0 ≤ b'.inAddr ∧ b'.bitPos = b.bitPos + (n : Int) ∧ b.bitPos < b'.bitPos

def Goal.model_7zip_folder_port_conservation : Prop :=
  ∀ (f : SevenZipTopDown.FolderDAG),
    f.FolderDAGInv → f.bindPairs.length < f.totalOutStreams ∧ 1 ≤ f.totalInStreams

def Goal.model_7zip_substream_le_folder : Prop :=
  ∀ (folders : List SevenZipTopDown.FolderDAG) (ss : SevenZipTopDown.SubStreamsLedger),
    SevenZipTopDown.SubStreamSumInv folders ss →
    ∀ (i : Nat) (hi : i < folders.length) (sz : Nat),
      sz ∈ ss.perFolderSizes.getD i [] →
      sz ≤ folders[i].cFolderUncompressedSize

def Goal.model_7zip_ppmd_restart_safe : Prop :=
  ∀ (size : Nat), 1824 ≤ size →
    129 * SevenZipTopDown.PPMD_UNIT_SIZE ≤ SevenZipTopDown.ppmdRestartCarveBytes size

theorem model_rar5_init_inv_proved : Goal.model_rar5_init_inv :=
  Rar5TopDown.initState_satisfies_inv

theorem model_rar5_cleanup_preserves_inv_proved : Goal.model_rar5_cleanup_preserves_inv :=
  Rar5TopDown.safeCleanupStep_preserves_inv

theorem model_rar5_skip_preserves_inv_proved : Goal.model_rar5_skip_preserves_inv :=
  Rar5TopDown.read_data_skip_preserves_inv

theorem model_rar5_throttle_no_deadlock_proved : Goal.model_rar5_throttle_no_deadlock :=
  Rar5TopDown.throttle_filter_no_deadlock

theorem model_rar5_bitreader_progress_proved : Goal.model_rar5_bitreader_progress :=
  Rar5TopDown.bitReader_skipBits_strict_progress

theorem model_7zip_folder_port_conservation_proved : Goal.model_7zip_folder_port_conservation :=
  SevenZipTopDown.folderDAG_port_conservation

theorem model_7zip_substream_le_folder_proved : Goal.model_7zip_substream_le_folder :=
  SevenZipTopDown.substream_size_le_folder_size

theorem model_7zip_ppmd_restart_safe_proved : Goal.model_7zip_ppmd_restart_safe :=
  SevenZipTopDown.ppmd_restart_safe_of_ge_1824

end LibarchiveF.Model
