import MozjpegF.Mozjpeg.«jmorecfg.h»
import MozjpegF.Mozjpeg.«jerror.h»

/-!
# `jpeglib.h` and `jpegint.h` — decompression constants and state helpers (`MozjpegF`)

Source: `mozjpeg/jpeglib.h` and `mozjpeg/jpegint.h` (`WITH_JPEG8 = 1`, `JPEG_LIB_VERSION = 80`).
-/

set_option autoImplicit false

namespace Mozjpeg.JpeglibH
open C

def JPEG_LIB_VERSION : Int32 := 80
def DCTSIZE : Int32 := 8
def DCTSIZE2 : Int32 := 64
def NUM_QUANT_TBLS : Int32 := 4
def NUM_HUFF_TBLS : Int32 := 4
def MAX_SAMP_FACTOR : Int32 := 4
def JPEG_MAX_DIMENSION : Int64 := 65500

def JPOOL_PERMANENT : Int32 := 0
def JPOOL_IMAGE : Int32 := 1
def JPOOL_NUMPOOLS : Int32 := 2

def JPEG_SUSPENDED : Int32 := 0
def JPEG_HEADER_OK : Int32 := 1
def JPEG_HEADER_TABLES_ONLY : Int32 := 2

def JPEG_COM : Int32 := 0xfe
def JPEG_APP0 : Int32 := 0xe0

def DSTATE_START : Int32 := 200
def DSTATE_INHEADER : Int32 := 201
def DSTATE_READY : Int32 := 202
def DSTATE_PRELOAD : Int32 := 203
def DSTATE_PRESCAN : Int32 := 204
def DSTATE_SCANNING : Int32 := 205
def DSTATE_RAW_OK : Int32 := 206
def DSTATE_BUFIMAGE : Int32 := 207
def DSTATE_BUFPOST : Int32 := 208
def DSTATE_RDCOEFS : Int32 := 209
def DSTATE_STOPPING : Int32 := 210

def JCS_UNKNOWN : Int32 := 0
def JCS_GRAYSCALE : Int32 := 1
def JCS_RGB : Int32 := 2
def JCS_YCbCr : Int32 := 3
def JCS_CMYK : Int32 := 4
def JCS_YCCK : Int32 := 5
def JCS_EXT_RGB : Int32 := 6
def JCS_EXT_RGBX : Int32 := 7
def JCS_EXT_BGR : Int32 := 8
def JCS_EXT_BGRX : Int32 := 9
def JCS_EXT_XBGR : Int32 := 10
def JCS_EXT_XRGB : Int32 := 11
def JCS_EXT_RGBA : Int32 := 12
def JCS_EXT_BGRA : Int32 := 13
def JCS_EXT_ABGR : Int32 := 14
def JCS_EXT_ARGB : Int32 := 15
def JCS_RGB565 : Int32 := 16

def sizeof_jpeg_marker_struct : Int64 := 32
def sizeof_jpeg_decompress_struct : UInt64 := 656
def sizeof_my_decomp_master : UInt64 := 160
def sizeof_jpeg_source_mgr : UInt64 := 56

end Mozjpeg.JpeglibH
