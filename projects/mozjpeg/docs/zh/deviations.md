<!-- source-sha256: 2b43f67e245aec49357387d769109c4b957b2aa1c96f89af86ba7be5c64b3029 -->
# 前提与偏差：调用必须满足的条件

本页列出目标中比 `jpeglib.h` 更窄、或调用方必须满足的前提。不满足这些前提的调用不在覆盖范围内：既未证明其安全，也不声称其不安全。

## 每次调用

- 库为 `mozjpeg` 5.0.0（`08265790`），以 `-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE` 构建为静态 x86_64 Linux LP64 库。SIMD 内核（NASM 汇编路径）、尚未证明的 12 位/16 位无损路径及 `turbojpeg` 接口不在覆盖范围内。
- 通过公开结构体传递的堆对象（`jpeg_error_mgr`、`jpeg_decompress_struct`、`jpeg_memory_mgr`、`jpeg_decomp_master`、`jpeg_input_controller`、`jpeg_marker_reader`、`comp_info` 数组）必须是存活、类型匹配且由 `jpeg_CreateDecompress` 与头部解析维护的基指针分配（`ValidDecompCore`、`ValidDecompDimsInput`）。
- 当 C 代码触发错误处理（`ERREXIT` / `ERREXIT1`）时，`error_exit` 经 `longjmp` 转移控制权；模型返回 `JpegRes.errExit code`，并更新 `err->msg_code` 与 `err->msg_parm.i[0]`。

## 比 `jpeglib.h` 更窄的前提

| 函数 | 前提 | Lean | 原因 |
| --- | --- | --- | --- |
| `jdiv_round_up`、`jround_up`（内部） | `0 ≤ a`、`0 < b`、`a + b < 2^63`（且 `a + b - 1 < 2^63`）。 | `Goal.jdiv_round_up_safety`、`Goal.jround_up_safety`、`Goal.jdiv_round_up_functional` | 有符号 `long` 加法 `(a + b)` 在 `a + b ≥ 2^63` 时按 ISO C17 发生有符号溢出；同时排除除零与负数取整。 |
| `jpeg_core_output_dimensions`、`jpeg_calc_output_dimensions` | `ValidDecompDimsInput`：`0 ≤ num_components ≤ 10`、`image_width ≤ 65500`、`image_height ≤ 65500`、采样因子在 `1..4` 之间、`comp_info` 至少包含 `num_components` 项，且 `jpeg_calc_output_dimensions` 时可为或不为 `DSTATE_READY`。 | `Goal.jpeg_core_output_dimensions_safety`、`Goal.jpeg_calc_output_dimensions_safety` | 约束在尺寸计算前由 JPEG 标准头部检查建立的不变量（`MAX_COMPONENTS = 10`、`JPEG_MAX_DIMENSION = 65500`）。 |
| `jpeg_core_output_dimensions`（缩放功能定理） | `scale_num = 1`、`scale_denom ∈ {1, 2, 4, 8}`、`master->lossless == 0`。 | `Goal.jpeg_core_output_dimensions_shrink_functional` | 对应 `Sharp` 的加载期缩放路径。 |
| `jpeg_save_markers` | `0 ≤ mem->max_alloc_chunk ≤ 1000000000` 且标记读取器数组长度为 `16`。 | `Goal.jpeg_save_markers_safety` | 对应 `jmemnobs.c` / `jdmarker.c` 中的 `MAX_ALLOC_CHUNK` 与 `APPn` 表长度。 |
