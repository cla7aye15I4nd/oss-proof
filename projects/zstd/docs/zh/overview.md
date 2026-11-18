<!-- source-sha256: 223c131559584124b1c6a569ec3d0fed304d59dffdb1d689319e4f854048472a -->
# Zstandard（`libzstd` 解码器）

验证对象：便携标量 x86_64 Linux LP64 配置（`-DZSTD_DISABLE_ASM -DDYNAMIC_BMI2=0 -DZSTD_LEGACY_SUPPORT=0`）下
Meta Zstandard 的独立 C 解码器（`lib/zstd.h`、`lib/zstd_errors.h`、`lib/decompress/*.c` 及其链接的六个
`lib/common/*.c` 单元）。

## 范围

- **流式解压与上下文生命周期：** `ZSTD_createDCtx`、`ZSTD_freeDCtx`、`ZSTD_DCtx_setParameter`、`ZSTD_DCtx_reset`
  与任意输入输出切分下的 `ZSTD_decompressStream`。
- **单次调用解压：** `ZSTD_decompress`、`ZSTD_decompressDCtx`、`ZSTD_decompress_usingDict` 与 `ZSTD_decompress_usingDDict`。
- **字典与前缀借用：** `ZSTD_createDDict`、`ZSTD_freeDDict`、`ZSTD_DCtx_loadDictionary`、`ZSTD_DCtx_refDDict`
  与 `ZSTD_DCtx_refPrefix`（含 `0xEC30A437` 格式化字典）。
- **帧检查与查询：** `ZSTD_getFrameContentSize`、`ZSTD_findFrameCompressedSize` 及错误与版本查询函数。

压缩器（`lib/compress/`）、字典训练器（`lib/dictBuilder/`）、旧版 v0.1–v0.7 解码器及手写汇编不在计划内。

## 当前已证明的内容

严格遵循 ISO C17 的堆与指针运行时（`ZstdF.Runtime`）已由 Lean 4 内核检查通过，包含对跨对象 `virtualStart` 指针减法及
空指针/悬垂指针加零的未定义行为拒绝定理。C 源码逐语句翻译与公开解码器安全性证明尚未完成。
