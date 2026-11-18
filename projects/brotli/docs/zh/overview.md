<!-- source-sha256: 30292fec3638baea4249c1694bc9e8b1fffce740fd8bb4bec175b0568100cf9c -->
# Brotli（`libbrotlidec`）

验证对象：便携标量 x86_64 Linux LP64 配置（`BROTLI_BUILD_PORTABLE`）下 Google Brotli 的 C 解码器
（`c/include/brotli/decode.h`、`c/dec/*.c` 及其依赖的 `c/common/*.c` 单元）。

## 范围

- **流式与单次解压：** 跨任意挂起与恢复状态（`SUCCESS`、`NEEDS_MORE_INPUT`、`NEEDS_MORE_OUTPUT`、`ERROR`）的
  `BrotliDecoderDecompressStream`，以及单次调用 `BrotliDecoderDecompress`。
- **零拷贝输出借用：** `BrotliDecoderHasMoreOutput` 与 `BrotliDecoderTakeOutput` 返回的环形缓冲区切片在下一次可变调用前的有效性。
- **生命周期、参数与附加字典：** `BrotliDecoderCreateInstance`、`BrotliDecoderDestroyInstance`、
  `BrotliDecoderSetParameter`、`BrotliDecoderAttachDictionary` 及错误与版本查询函数。

编码器（`c/enc/`）不在计划内。

## 当前已证明的内容

严格遵循 ISO C17 的堆与指针运行时（`BrotliF.Runtime`）已由 Lean 4 内核检查通过。`libbrotlidec` 的 C 源码逐语句翻译与
公开解码器安全性证明尚未完成。
