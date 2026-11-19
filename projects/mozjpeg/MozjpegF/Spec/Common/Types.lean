import MozjpegF.Runtime.Libc
import MozjpegF.Mozjpeg.«jmorecfg.h»
import MozjpegF.Mozjpeg.«jerror.h»
import MozjpegF.Mozjpeg.«jpeglib.h»
import MozjpegF.Mozjpeg.«jutils.c»
import MozjpegF.Mozjpeg.«jerror.c»
import MozjpegF.Mozjpeg.«jcomapi.c»
import MozjpegF.Mozjpeg.«jdmaster.c»
import MozjpegF.Mozjpeg.«jdmarker.c»
import MozjpegF.Mozjpeg.«jdapimin.c»

/-!
# Shared specification vocabulary (`MozjpegF`)

Common heap predicates and object-graph invariants shared by `MozjpegF.Spec.Safety` and
`MozjpegF.Spec.Functional`. No `Goal.*` definitions live here.
-/

set_option autoImplicit false

namespace MozjpegF.Spec
open C Mozjpeg.MoreCfg Mozjpeg.JpeglibH

/-- `m` faults on `h` with `Fault.ub` (not `outOfFuel` and not `.ok`). -/
def FaultsWithUb {α : Type} (m : C.M α) (h : C.Heap) : Prop :=
  ∃ msg : String, C.run m h = .error (.ub msg)

/-- `p` points to `length` live bytes inside one allocated or static byte object. -/
def LiveBytes (h : C.Heap) (pointer : C.BPtr) (length : Nat) : Prop :=
  ∃ r off data,
    pointer = .ref r off ∧
    C.Space.get h r = some data ∧
    off + length ≤ data.size

/-- `p` points to `length` live writable bytes in one heap block. -/
def WritableBytes (h : C.Heap) (pointer : C.BPtr) (length : Nat) : Prop :=
  ∃ b off data,
    pointer = .ref (.heap b) off ∧
    h.bytes b = some data ∧
    off + length ≤ data.size

/-- `err` points to a live writable single `struct jpeg_error_mgr` object at offset 0. -/
def ValidErrMgr (h : C.Heap) (err : C.ErrPtr) : Prop :=
  ∃ r a, err = .ref r 0 ∧ C.Space.get h r = some a ∧ 0 < a.size

/-- Live component array `compInfo` with `n` initialized entries satisfying `initial_setup` bounds. -/
def ValidCompArray (h : C.Heap) (compInfo : C.CompPtr) (n : Nat) : Prop :=
  ∃ r comps,
    compInfo = .ref r 0 ∧
    C.Space.get h r = some comps ∧
    n ≤ comps.size ∧
    ∀ i, i < n →
      1 ≤ (comps[i]!).hSampFactor.toInt ∧ (comps[i]!).hSampFactor.toInt ≤ 4 ∧
      1 ≤ (comps[i]!).vSampFactor.toInt ∧ (comps[i]!).vSampFactor.toInt ≤ 4

/-- Core live object graph for a `jpeg_decompress_struct` and its subobjects (`err`, `mem`, `master`,
`inputctl`, `marker`). -/
def ValidDecompCore (h : C.Heap) (cinfo : C.DecompPtr) : Prop :=
  ∃ rc dcs dc rm mems rmas masters ric ics rmrk mrks,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧
    dc = dcs[0]! ∧
    ValidErrMgr h dc.err ∧
    dc.mem = .ref rm 0 ∧ C.Space.get h rm = some mems ∧ 0 < mems.size ∧
    dc.master = .ref rmas 0 ∧ C.Space.get h rmas = some masters ∧ 0 < masters.size ∧
    dc.inputctl = .ref ric 0 ∧ C.Space.get h ric = some ics ∧ 0 < ics.size ∧
    dc.marker = .ref rmrk 0 ∧ C.Space.get h rmrk = some mrks ∧ 0 < mrks.size

/-- Decompressor object satisfies `ValidDecompCore` plus valid `initial_setup` header bounds
(`DSTATE_READY` or general state check, `1 ≤ numComponents ≤ 10`, sampling factors in `1..4`,
`imageWidth/imageHeight ≤ 65500`). -/
def ValidDecompDimsInput (h : C.Heap) (cinfo : C.DecompPtr) (requireReady : Bool) : Prop :=
  ValidDecompCore h cinfo ∧
  ∃ rc dcs dc rmas masters mst,
    cinfo = .ref rc 0 ∧
    C.Space.get h rc = some dcs ∧ 0 < dcs.size ∧ dc = dcs[0]! ∧
    dc.master = .ref rmas 0 ∧ C.Space.get h rmas = some masters ∧ 0 < masters.size ∧
    mst = masters[0]! ∧
    (!requireReady || dc.globalState = DSTATE_READY) ∧
    (0 ≤ dc.numComponents.toInt ∧ dc.numComponents.toInt ≤ 10) ∧
    (dc.imageWidth.toNat ≤ 65500 ∧ dc.imageHeight.toNat ≤ 65500) ∧
    (1 ≤ dc.maxHSampFactor.toInt ∧ dc.maxHSampFactor.toInt ≤ 4) ∧
    (1 ≤ dc.maxVSampFactor.toInt ∧ dc.maxVSampFactor.toInt ≤ 4) ∧
    ValidCompArray h dc.compInfo dc.numComponents.toInt.toNat

end MozjpegF.Spec
