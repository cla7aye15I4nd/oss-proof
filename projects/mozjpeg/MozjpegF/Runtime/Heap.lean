import MozjpegF.Runtime.Space

/-!
# Runtime heap (`MozjpegF`)

Byte-addressed, static-table, and typed struct object heap for LP64 Linux translations of
`mozjpeg` 5.0.0 under strict ISO C17 pointer rules.
-/

set_option autoImplicit false

namespace C

/-- Source string literals compiled into `jpeg_std_message_table` (`jerror.c` / `jerror.h`, `JMSG_LASTMSGCODE = 132`). -/
def strTable : Array String := #[
  "Bogus message code %d",
  "ALIGN_TYPE is wrong, please fix",
  "MAX_ALLOC_CHUNK is wrong, please fix",
  "Bogus buffer control mode",
  "Invalid component ID %d in SOS",
  "Invalid crop request",
  "DCT coefficient (lossy) or spatial difference (lossless) out of range",
  "IDCT output block size %d not supported",
  "Component index %d: mismatching sampling ratio %d:%d, %d:%d, %c",
  "Bogus Huffman table definition",
  "Bogus input colorspace",
  "Bogus JPEG colorspace",
  "Bogus marker length",
  "Wrong JPEG library version: library is %d, caller expects %d",
  "Sampling factors too large for interleaved scan",
  "Invalid memory pool code %d",
  "Unsupported JPEG data precision %d",
  "Invalid progressive/lossless parameters Ss=%d Se=%d Ah=%d Al=%d",
  "Invalid progressive/lossless parameters at scan script entry %d",
  "Bogus sampling factors",
  "Invalid scan script at entry %d",
  "Improper call to JPEG library in state %d",
  "JPEG parameter struct mismatch: library thinks size is %u, caller expects %u",
  "Bogus virtual array access",
  "Buffer passed to JPEG library is too small",
  "Suspension not allowed here",
  "CCIR601 sampling not implemented yet",
  "Too many color components: %d, max %d",
  "Unsupported color conversion request",
  "Bogus DAC index %d",
  "Bogus DAC value 0x%x",
  "Bogus DHT index %d",
  "Bogus DQT index %d",
  "Empty JPEG image (DNL not supported)",
  "Read from EMS failed",
  "Write to EMS failed",
  "Didn't expect more than one scan",
  "Input file read error",
  "Output file write error --- out of disk space?",
  "Fractional sampling not implemented yet",
  "Huffman code size table overflow",
  "Missing Huffman code table entry",
  "Maximum supported image dimension is %u pixels",
  "Empty input file",
  "Premature end of input file",
  "Cannot transcode due to multiple use of quantization table %d",
  "Scan script does not transmit all data",
  "Invalid color quantization mode change",
  "Requested features are incompatible",
  "Requested feature was omitted at compile time",
  "Arithmetic table 0x%02x was not defined",
  "Memory limit exceeded",
  "Huffman table 0x%02x was not defined",
  "JPEG datastream contains no image",
  "Quantization table 0x%02x was not defined",
  "Not a JPEG file: starts with 0x%02x 0x%02x",
  "Insufficient memory (case %d)",
  "Cannot quantize more than %d color components",
  "Cannot quantize to fewer than %d colors",
  "Cannot quantize to more than %d colors",
  "Invalid JPEG file structure: two SOF markers",
  "Invalid JPEG file structure: missing SOS marker",
  "Unsupported JPEG process: SOF type 0x%02x",
  "Invalid JPEG file structure: two SOI markers",
  "Invalid JPEG file structure: SOS before SOF",
  "Failed to create temporary file %s",
  "Read failed on temporary file",
  "Seek failed on temporary file",
  "Write failed on temporary file --- out of disk space?",
  "Application transferred too few scanlines",
  "Unsupported marker type 0x%02x",
  "Virtual array controller messed up",
  "Image too wide for this implementation",
  "Read from XMS failed",
  "Write to XMS failed",
  "Copyright (C) 1991-2024 The libjpeg-turbo Project and many others",
  "8d  15-Jan-2012",
  "Caution: quantization tables are too coarse for baseline JPEG",
  "Adobe APP14 marker: version %d, flags 0x%04x 0x%04x, transform %d",
  "Unknown APP0 marker (not JFIF), length %u",
  "Unknown APP14 marker (not Adobe), length %u",
  "Define Arithmetic Table 0x%02x: 0x%02x",
  "Define Huffman Table 0x%02x",
  "Define Quantization Table %d  precision %d",
  "Define Restart Interval %u",
  "Freed EMS handle %u",
  "Obtained EMS handle %u",
  "End Of Image",
  "        %3d %3d %3d %3d %3d %3d %3d %3d",
  "JFIF APP0 marker: version %d.%02d, density %dx%d  %d",
  "Warning: thumbnail image size does not match data length %u",
  "JFIF extension marker: type 0x%02x, length %u",
  "    with %d x %d thumbnail image",
  "Miscellaneous marker 0x%02x, length %u",
  "Unexpected marker 0x%02x",
  "        %4u %4u %4u %4u %4u %4u %4u %4u",
  "Quantizing to %d = %d*%d*%d colors",
  "Quantizing to %d colors",
  "Selected %d colors for quantization",
  "At marker 0x%02x, recovery action %d",
  "RST%d",
  "Smoothing not supported with nonstandard sampling ratios",
  "Start Of Frame 0x%02x: width=%u, height=%u, components=%d",
  "    Component %d: %dhx%dv q=%d",
  "Start of Image",
  "Start Of Scan: %d components",
  "    Component %d: dc=%d ac=%d",
  "  Ss=%d, Se=%d, Ah=%d, Al=%d",
  "Closed temporary file %s",
  "Opened temporary file %s",
  "JFIF extension marker: JPEG-compressed thumbnail image, length %u",
  "JFIF extension marker: palette thumbnail image, length %u",
  "JFIF extension marker: RGB thumbnail image, length %u",
  "Unrecognized component IDs %d %d %d, assuming YCbCr (lossy) or RGB (lossless)",
  "Freed XMS handle %u",
  "Obtained XMS handle %u",
  "Unknown Adobe color transform code %d",
  "Corrupt JPEG data: bad arithmetic code",
  "Inconsistent progression sequence for component %d coefficient %d",
  "Corrupt JPEG data: %u extraneous bytes before marker 0x%02x",
  "Corrupt JPEG data: premature end of data segment",
  "Corrupt JPEG data: bad Huffman code",
  "Warning: unknown JFIF revision number %d.%02d",
  "Premature end of JPEG file",
  "Corrupt JPEG data: found marker 0x%02x instead of RST%d",
  "Invalid SOS parameters for sequential JPEG",
  "Application transferred too many scanlines",
  "Bogus parameter",
  "Bogus parameter value",
  "I/O suspension not supported in scan optimization",
  "Corrupt JPEG data: bad ICC marker",
  "Invalid restart interval %d; must be an integer multiple of the number of MCUs in an MCU row (%d)"
]

/-- Reference to a byte array (`malloc`, read-only static bytes, source EOF buffer, or source string literal). -/
inductive BRef where
  | heap (b : Nat)
  | const (b : Nat)
  | const_eof
  | str (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to an `int` (`Int32`) array (static `rgb_pixelsize` / `jpeg_natural_order` or heap array). -/
inductive IRef where
  | st_rgb_pixelsize
  | st_natural_order
  | heap (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to the read-only `const char * const *` error message table (`jpeg_std_message_table`). -/
inductive MsgTblRef where
  | stdTable
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_error_mgr` object. -/
inductive ErrRef where
  | err (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_decompress_struct` object. -/
inductive DecompRef where
  | decomp (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `jpeg_component_info` array (`cinfo->comp_info`). -/
inductive CompRef where
  | comp (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `my_decomp_master` / `struct jpeg_decomp_master` object. -/
inductive MasterRef where
  | master (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_input_controller` object. -/
inductive InputCtlRef where
  | inputctl (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `my_marker_reader` / `struct jpeg_marker_reader` object. -/
inductive MarkerRef where
  | marker (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_memory_mgr` object. -/
inductive MemRef where
  | mem (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_source_mgr` object. -/
inductive SrcRef where
  | src (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `JQUANT_TBL` object. -/
inductive QuantRef where
  | quant (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `JHUFF_TBL` object. -/
inductive HuffRef where
  | huff (b : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a `struct jpeg_marker_struct` object (`jpeg_saved_marker_ptr`). -/
inductive SavedMarkerRef where
  | savedMarker (b : Nat)
  deriving DecidableEq, Repr, Inhabited

abbrev BPtr := Ptr BRef
abbrev IPtr := Ptr IRef
abbrev MsgTblPtr := Ptr MsgTblRef
abbrev ErrPtr := Ptr ErrRef
abbrev DecompPtr := Ptr DecompRef
abbrev CompPtr := Ptr CompRef
abbrev MasterPtr := Ptr MasterRef
abbrev InputCtlPtr := Ptr InputCtlRef
abbrev MarkerPtr := Ptr MarkerRef
abbrev MemPtr := Ptr MemRef
abbrev SrcPtr := Ptr SrcRef
abbrev QuantPtr := Ptr QuantRef
abbrev HuffPtr := Ptr HuffRef
abbrev SavedMarkerPtr := Ptr SavedMarkerRef

/-- `struct jpeg_error_mgr` (`jpeglib.h:827-880`). -/
structure JpegErrorMgr where
  errorExit : FnPtr := .null
  emitMessage : FnPtr := .null
  outputMessage : FnPtr := .null
  formatMessage : FnPtr := .null
  resetErrorMgr : FnPtr := .null
  msgCode : Int32 := 0
  msgParmI : Array Int32 := Array.replicate 8 0
  traceLevel : Int32 := 0
  numWarnings : Int64 := 0
  jpegMessageTable : MsgTblPtr := .null
  lastJpegMessage : Int32 := 0
  addonMessageTable : MsgTblPtr := .null
  firstAddonMessage : Int32 := 0
  lastAddonMessage : Int32 := 0
  deriving Repr, Inhabited, DecidableEq

/-- `JQUANT_TBL` (`jpeglib.h:118-127`). -/
structure JQuantTbl where
  quantval : Array UInt16 := Array.replicate 64 0
  sentTable : Int32 := 0
  deriving Repr, Inhabited, DecidableEq

/-- `JHUFF_TBL` (`jpeglib.h:132-142`). -/
structure JHuffTbl where
  bits : Array UInt8 := Array.replicate 17 0
  huffval : Array UInt8 := Array.replicate 256 0
  sentTable : Int32 := 0
  deriving Repr, Inhabited, DecidableEq

/-- `struct jpeg_marker_struct` (`jpeglib.h:248-255`). -/
structure JpegSavedMarker where
  next : SavedMarkerPtr := .null
  marker : UInt8 := 0
  originalLength : UInt32 := 0
  dataLength : UInt32 := 0
  data : BPtr := .null
  deriving Repr, Inhabited, DecidableEq

/-- `jpeg_component_info` (`jpeglib.h:154-227`). -/
structure JpegCompInfo where
  componentId : Int32 := 0
  componentIndex : Int32 := 0
  hSampFactor : Int32 := 0
  vSampFactor : Int32 := 0
  quantTblNo : Int32 := 0
  dcTblNo : Int32 := 0
  acTblNo : Int32 := 0
  widthInBlocks : UInt32 := 0
  heightInBlocks : UInt32 := 0
  dctHScaledSize : Int32 := 0
  dctVScaledSize : Int32 := 0
  downsampledWidth : UInt32 := 0
  downsampledHeight : UInt32 := 0
  componentNeeded : Int32 := 0
  mcuWidth : Int32 := 0
  mcuHeight : Int32 := 0
  mcuBlocks : Int32 := 0
  mcuSampleWidth : Int32 := 0
  lastColWidth : Int32 := 0
  lastRowHeight : Int32 := 0
  quantTable : QuantPtr := .null
  deriving Repr, Inhabited, DecidableEq

/-- `my_decomp_master` / `struct jpeg_decomp_master` (`jpegint.h`, `jdmaster.h`). -/
structure JpegDecompMaster where
  finishOutputPass : FnPtr := .null
  lossless : Int32 := 0
  usingMergedUpsample : Int32 := 0
  passNumber : Int32 := 0
  firstMcuCol : Array UInt32 := Array.replicate 10 0
  lastMcuCol : Array UInt32 := Array.replicate 10 0
  markerListEnd : SavedMarkerPtr := .null
  deriving Repr, Inhabited, DecidableEq

/-- `struct jpeg_source_mgr` (`jpeglib.h:883-913`). -/
structure JpegSourceMgr where
  nextInputByte : BPtr := .null
  bytesInBuffer : UInt64 := 0
  initSource : FnPtr := .null
  fillInputBuffer : FnPtr := .null
  skipInputData : FnPtr := .null
  resyncToRestart : FnPtr := .null
  termSource : FnPtr := .null
  deriving Repr, Inhabited, DecidableEq

/-- `struct jpeg_input_controller` (`jpegint.h:319-329`, `jdinput.c:29-33`). -/
structure JpegInputController where
  consumeInput : FnPtr := .null
  resetInputController : FnPtr := .null
  startInputPass : FnPtr := .null
  finishInputPass : FnPtr := .null
  hasMultipleScans : Int32 := 0
  eoiReached : Int32 := 0
  inheaders : Int32 := 1
  deriving Repr, Inhabited, DecidableEq

/-- `my_marker_reader` (`jdmarker.c:95-110`, `jpegint.h`). -/
structure JpegMarkerReader where
  resetMarkerReader : FnPtr := .null
  readMarkers : FnPtr := .null
  readRestartMarker : FnPtr := .null
  processCOM : FnPtr := .null
  lengthLimitCOM : UInt32 := 0
  processAPPn : Array FnPtr := Array.replicate 16 .null
  lengthLimitAPPn : Array UInt32 := Array.replicate 16 0
  sawSOI : Int32 := 0
  sawSOF : Int32 := 0
  nextRestartNum : Int32 := 0
  discardedBytes : UInt32 := 0
  curMarker : SavedMarkerPtr := .null
  bytesRead : UInt32 := 0
  deriving Repr, Inhabited, DecidableEq

/-- Objects tracked per lifetime pool (`JPOOL_PERMANENT = 0`, `JPOOL_IMAGE = 1`). -/
structure PoolAllocs where
  bytes : Array Nat := #[]
  i32s : Array Nat := #[]
  masters : Array Nat := #[]
  inputctls : Array Nat := #[]
  markers : Array Nat := #[]
  srcs : Array Nat := #[]
  comps : Array Nat := #[]
  quants : Array Nat := #[]
  huffs : Array Nat := #[]
  savedMarkers : Array Nat := #[]
  deriving Repr, Inhabited, DecidableEq

/-- `struct jpeg_memory_mgr` / `my_memory_mgr` (`jpeglib.h:937-990`, `jmemmgr.c:123-145`). -/
structure JpegMemMgr where
  allocSmall : FnPtr := .null
  freePool : FnPtr := .null
  selfDestruct : FnPtr := .null
  maxAllocChunk : Int64 := 1000000000
  maxMemoryToUse : Int64 := 0
  totalSpaceAllocated : UInt64 := 0
  livePools : Array Bool := #[true, true]
  poolAllocs : Array PoolAllocs := #[{}, {}]
  deriving Repr, Inhabited, DecidableEq

/-- `struct jpeg_decompress_struct` (`jpeglib.h:568-814`). -/
structure JpegDecompressStruct where
  err : ErrPtr := .null
  mem : MemPtr := .null
  progress : BPtr := .null
  clientData : BPtr := .null
  isDecompressor : Int32 := 1
  globalState : Int32 := 0
  src : SrcPtr := .null
  imageWidth : UInt32 := 0
  imageHeight : UInt32 := 0
  numComponents : Int32 := 0
  jpegColorSpace : Int32 := 0
  outColorSpace : Int32 := 0
  scaleNum : UInt32 := 1
  scaleDenom : UInt32 := 1
  outputGamma : UInt64 := 0
  bufferedImage : Int32 := 0
  rawDataOut : Int32 := 0
  dctMethod : Int32 := 0
  doFancyUpsampling : Int32 := 1
  doBlockSmoothing : Int32 := 1
  quantizeColors : Int32 := 0
  ditherMode : Int32 := 0
  twoPassQuantize : Int32 := 0
  desiredNumberOfColors : Int32 := 0
  colormap : BPtr := .null
  enable1passQuant : Int32 := 0
  enableExternalQuant : Int32 := 0
  enable2passQuant : Int32 := 0
  outputWidth : UInt32 := 0
  outputHeight : UInt32 := 0
  outColorComponents : Int32 := 0
  outputComponents : Int32 := 0
  recOutbufHeight : Int32 := 0
  outputScanline : UInt32 := 0
  inputScanNumber : Int32 := 0
  outputScanNumber : Int32 := 0
  coefBits : BPtr := .null
  quantTblPtrs : Array QuantPtr := Array.replicate 4 .null
  dcHuffTblPtrs : Array HuffPtr := Array.replicate 4 .null
  acHuffTblPtrs : Array HuffPtr := Array.replicate 4 .null
  dataPrecision : Int32 := 8
  compInfo : CompPtr := .null
  progressiveMode : Int32 := 0
  arithCode : Int32 := 0
  arithDcL : Array UInt8 := Array.replicate 16 0
  arithDcU : Array UInt8 := Array.replicate 16 0
  arithAcK : Array UInt8 := Array.replicate 16 0
  restartInterval : UInt32 := 0
  sawJFIFMarker : Int32 := 0
  jfifMajorVersion : UInt8 := 0
  jfifMinorVersion : UInt8 := 0
  densityUnit : UInt8 := 0
  xDensity : UInt16 := 0
  yDensity : UInt16 := 0
  sawAdobeMarker : Int32 := 0
  adobeTransform : UInt8 := 0
  ccir601Sampling : Int32 := 0
  markerList : SavedMarkerPtr := .null
  maxHSampFactor : Int32 := 1
  maxVSampFactor : Int32 := 1
  minDctHScaledSize : Int32 := 8
  minDctVScaledSize : Int32 := 8
  totalIMcuRows : UInt32 := 0
  compsInScan : Int32 := 0
  curCompInfo : Array CompPtr := Array.replicate 4 .null
  mcusPerRow : UInt32 := 0
  mcuRowsInScan : UInt32 := 0
  blocksInMcu : Int32 := 0
  mcuMembership : Array Int32 := Array.replicate 10 0
  ss : Int32 := 0
  se : Int32 := 0
  ah : Int32 := 0
  al : Int32 := 0
  blockSize : Int32 := 8
  naturalOrder : IPtr := .null
  limSe : Int32 := 63
  unreadMarker : Int32 := 0
  master : MasterPtr := .null
  inputctl : InputCtlPtr := .null
  marker : MarkerPtr := .null
  entropyStartPass : FnPtr := .null
  coefStartInputPass : FnPtr := .null
  coefConsumeData : FnPtr := .null
  cquantFinishPass : FnPtr := .null
  deriving Repr, Inhabited, DecidableEq

/-- Zero-byte representation of `struct jpeg_decompress_struct` after `memset(cinfo, 0, sizeof(...))`. -/
def JpegDecompressStruct.zeroed : JpegDecompressStruct := {
  isDecompressor := 0
  scaleNum := 0
  scaleDenom := 0
  doFancyUpsampling := 0
  doBlockSmoothing := 0
  dataPrecision := 0
  maxHSampFactor := 0
  maxVSampFactor := 0
  minDctHScaledSize := 0
  minDctVScaledSize := 0
  blockSize := 0
  limSe := 0
}

/-- Zero-byte representation of `my_decomp_master` after `memset(cinfo->master, 0, sizeof(...))`. -/
def JpegDecompMaster.zeroed : JpegDecompMaster := {}

/-- Heap state with byte blocks, static tables, typed libjpeg objects, allocation/garbage/address oracles. -/
structure Heap where
  bytes : Tbl (Option (Array UInt8)) := .empty
  consts : Tbl (Option (Array UInt8)) := .empty
  i32s : Tbl (Option (Array Int32)) := .empty
  rgbPixelsize : Array Int32 := #[-1, -1, 3, -1, -1, -1, 3, 4, 3, 4, 4, 4, 4, 4, 4, 4, -1]
  naturalOrder : Array Int32 := #[
     0,  1,  8, 16,  9,  2,  3, 10,
    17, 24, 32, 25, 18, 11,  4,  5,
    12, 19, 26, 33, 40, 48, 41, 34,
    27, 20, 13,  6,  7, 14, 21, 28,
    35, 42, 49, 56, 57, 50, 43, 36,
    29, 22, 15, 23, 30, 37, 44, 51,
    58, 59, 52, 45, 38, 31, 39, 46,
    53, 60, 61, 54, 47, 55, 62, 63,
    63, 63, 63, 63, 63, 63, 63, 63,
    63, 63, 63, 63, 63, 63, 63, 63
  ]
  errMgrs : Tbl (Option (Array JpegErrorMgr)) := .empty
  decomps : Tbl (Option (Array JpegDecompressStruct)) := .empty
  comps : Tbl (Option (Array JpegCompInfo)) := .empty
  masters : Tbl (Option (Array JpegDecompMaster)) := .empty
  inputctls : Tbl (Option (Array JpegInputController)) := .empty
  markers : Tbl (Option (Array JpegMarkerReader)) := .empty
  mems : Tbl (Option (Array JpegMemMgr)) := .empty
  srcs : Tbl (Option (Array JpegSourceMgr)) := .empty
  quants : Tbl (Option (Array JQuantTbl)) := .empty
  huffs : Tbl (Option (Array JHuffTbl)) := .empty
  savedMarkers : Tbl (Option (Array JpegSavedMarker)) := .empty
  nextBlk : Nat := 0
  nalloc : Nat := 0
  allocOk : Nat → Bool := fun _ => true
  garbage : Nat → Nat → UInt64 := fun _ _ => 0
  baseAddr : BRef → UInt64 := fun _ => 0

namespace Heap

def empty : Heap := {}

def litBytes (s : String) : Array UInt8 := s.toUTF8.data.push 0

def getBytes (h : Heap) : BRef → Option (Array UInt8)
  | .heap b => h.bytes b
  | .const b => h.consts b
  | .const_eof => some #[0xff, 0xd9, 0, 0]
  | .str i => strTable[i]?.map litBytes

def putBytes (h : Heap) (r : BRef) (a : Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := upd h.bytes b (some a) }
  | .const _ => h
  | .const_eof => h
  | .str _ => h

def isRoBytes (_h : Heap) : BRef → Bool
  | .heap _ => false
  | .const _ => true
  | .const_eof => true
  | .str _ => true

def modifyBytes (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) : Heap :=
  match r with
  | .heap b => { h with bytes := h.bytes.modify b (Option.map f) }
  | .const _ => h
  | .const_eof => h
  | .str _ => h

theorem modifyBytes_eq (h : Heap) (r : BRef) (a : Array UInt8) (f : Array UInt8 → Array UInt8)
    (hg : getBytes h r = some a) :
    modifyBytes h r f = putBytes h r (f a) := by
  cases r with
  | heap b =>
    simp only [getBytes] at hg
    simp only [modifyBytes, putBytes, Tbl.modify_opt h.bytes b f a hg]
  | const _ => rfl
  | const_eof => rfl
  | str _ => rfl

def getI32 (h : Heap) : IRef → Option (Array Int32)
  | .st_rgb_pixelsize => some h.rgbPixelsize
  | .st_natural_order => some h.naturalOrder
  | .heap b => h.i32s b

def putI32 (h : Heap) (r : IRef) (a : Array Int32) : Heap :=
  match r with
  | .heap b => { h with i32s := upd h.i32s b (some a) }
  | _ => h

def isRoI32 (_h : Heap) : IRef → Bool
  | .heap _ => false
  | _ => true

def modifyI32 (h : Heap) (r : IRef) (f : Array Int32 → Array Int32) : Heap :=
  match r with
  | .heap b => { h with i32s := h.i32s.modify b (Option.map f) }
  | _ => h

end Heap

instance : Space Heap BRef UInt8 where
  get := Heap.getBytes
  put := Heap.putBytes
  ro := Heap.isRoBytes
  modify := Heap.modifyBytes
  modify_eq h r a f hg := Heap.modifyBytes_eq h r a f hg

instance : Space Heap IRef Int32 where
  get := Heap.getI32
  put := Heap.putI32
  ro := Heap.isRoI32
  modify := Heap.modifyI32
  modify_eq h r a f hg := by
    cases r with
    | heap b =>
      simp only [Heap.getI32] at hg
      simp only [Heap.modifyI32, Heap.putI32, Tbl.modify_opt h.i32s b f a hg]
    | st_rgb_pixelsize => rfl
    | st_natural_order => rfl

instance : Space Heap ErrRef JpegErrorMgr where
  get h | .err b => h.errMgrs b
  put h | .err b => fun a => { h with errMgrs := upd h.errMgrs b (some a) }
  ro _ _ := false
  modify h | .err b => fun f => { h with errMgrs := h.errMgrs.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | err b =>
    exact congrArg (fun x => { h with errMgrs := x }) (Tbl.modify_opt h.errMgrs b f a hg)

instance : Space Heap DecompRef JpegDecompressStruct where
  get h | .decomp b => h.decomps b
  put h | .decomp b => fun a => { h with decomps := upd h.decomps b (some a) }
  ro _ _ := false
  modify h | .decomp b => fun f => { h with decomps := h.decomps.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | decomp b =>
    exact congrArg (fun x => { h with decomps := x }) (Tbl.modify_opt h.decomps b f a hg)

instance : Space Heap CompRef JpegCompInfo where
  get h | .comp b => h.comps b
  put h | .comp b => fun a => { h with comps := upd h.comps b (some a) }
  ro _ _ := false
  modify h | .comp b => fun f => { h with comps := h.comps.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | comp b =>
    exact congrArg (fun x => { h with comps := x }) (Tbl.modify_opt h.comps b f a hg)

instance : Space Heap MasterRef JpegDecompMaster where
  get h | .master b => h.masters b
  put h | .master b => fun a => { h with masters := upd h.masters b (some a) }
  ro _ _ := false
  modify h | .master b => fun f => { h with masters := h.masters.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | master b =>
    exact congrArg (fun x => { h with masters := x }) (Tbl.modify_opt h.masters b f a hg)

instance : Space Heap InputCtlRef JpegInputController where
  get h | .inputctl b => h.inputctls b
  put h | .inputctl b => fun a => { h with inputctls := upd h.inputctls b (some a) }
  ro _ _ := false
  modify h | .inputctl b => fun f => { h with inputctls := h.inputctls.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | inputctl b =>
    exact congrArg (fun x => { h with inputctls := x }) (Tbl.modify_opt h.inputctls b f a hg)

instance : Space Heap MarkerRef JpegMarkerReader where
  get h | .marker b => h.markers b
  put h | .marker b => fun a => { h with markers := upd h.markers b (some a) }
  ro _ _ := false
  modify h | .marker b => fun f => { h with markers := h.markers.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | marker b =>
    exact congrArg (fun x => { h with markers := x }) (Tbl.modify_opt h.markers b f a hg)

instance : Space Heap MemRef JpegMemMgr where
  get h | .mem b => h.mems b
  put h | .mem b => fun a => { h with mems := upd h.mems b (some a) }
  ro _ _ := false
  modify h | .mem b => fun f => { h with mems := h.mems.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | mem b =>
    exact congrArg (fun x => { h with mems := x }) (Tbl.modify_opt h.mems b f a hg)

instance : Space Heap SrcRef JpegSourceMgr where
  get h | .src b => h.srcs b
  put h | .src b => fun a => { h with srcs := upd h.srcs b (some a) }
  ro _ _ := false
  modify h | .src b => fun f => { h with srcs := h.srcs.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | src b =>
    exact congrArg (fun x => { h with srcs := x }) (Tbl.modify_opt h.srcs b f a hg)

instance : Space Heap QuantRef JQuantTbl where
  get h | .quant b => h.quants b
  put h | .quant b => fun a => { h with quants := upd h.quants b (some a) }
  ro _ _ := false
  modify h | .quant b => fun f => { h with quants := h.quants.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | quant b =>
    exact congrArg (fun x => { h with quants := x }) (Tbl.modify_opt h.quants b f a hg)

instance : Space Heap HuffRef JHuffTbl where
  get h | .huff b => h.huffs b
  put h | .huff b => fun a => { h with huffs := upd h.huffs b (some a) }
  ro _ _ := false
  modify h | .huff b => fun f => { h with huffs := h.huffs.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | huff b =>
    exact congrArg (fun x => { h with huffs := x }) (Tbl.modify_opt h.huffs b f a hg)

instance : Space Heap SavedMarkerRef JpegSavedMarker where
  get h | .savedMarker b => h.savedMarkers b
  put h | .savedMarker b => fun a => { h with savedMarkers := upd h.savedMarkers b (some a) }
  ro _ _ := false
  modify h | .savedMarker b => fun f => { h with savedMarkers := h.savedMarkers.modify b (Option.map f) }
  modify_eq h r a f hg := by
    cases r with | savedMarker b =>
    exact congrArg (fun x => { h with savedMarkers := x }) (Tbl.modify_opt h.savedMarkers b f a hg)

end C
