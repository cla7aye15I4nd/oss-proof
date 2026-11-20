# Differential tests: the Lean translation against the real C

The translation in `MozjpegF/Mozjpeg/*.lean` is trusted, not proved. This directory compares
the real compiled `mozjpeg` static C library (configured with `-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE`)
against the Lean translations on identical inputs byte for byte.

Differential testing is evidence of translation fidelity, not proof.

## Run

```bash
MOZJPEG_SRC=$PWD/mozjpeg bash tests/run.sh          # from projects/mozjpeg
SAN=1 MOZJPEG_SRC=$PWD/mozjpeg bash tests/run.sh    # C side under ASan + UBSan (what CI runs)
```

## Drivers

| Name | C file | Functions |
| --- | --- | --- |
| `jutils` | `jutils.c` | `jdiv_round_up`, `jround_up`, `jzero_far`, `jpeg_natural_order` |
| `jerror` | `jerror.c` | `jpeg_std_error`, `jpeg_std_message_table` |
| `jdmarker` | `jdmarker.c` | `jpeg_save_markers` |
| `jdmaster` | `jdmaster.c` | `jpeg_core_output_dimensions`, `jpeg_calc_output_dimensions` |
