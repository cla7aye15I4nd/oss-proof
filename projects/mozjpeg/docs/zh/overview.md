<!-- source-sha256: d40cc8c3dc349679209a8a7e95460005c0d0d6b5ba145bb4cca6d3962fa5fbd7 -->
# mozjpeg

验证对象：`mozjpeg` 5.0.0（`08265790`），按可移植静态 8 位 x86_64 Linux LP64 库（`libjpeg.a`）构建，范围为默认 `Sharp` / `libvips` 调用链路触达的非可信输入解码（Tier 0）入口函数。

## 构建配置

被验证的库以如下 CMake 选项从固定上游源码构建：

```
-DBUILD_SHARED_LIBS=FALSE -DWITH_JPEG8=1 -DWITH_TURBOJPEG=FALSE -DPNG_SUPPORTED=FALSE -DWITH_SIMD=FALSE
```

- `WITH_JPEG8=1` 匹配现代 Linux 构建所用的 `libjpeg` v8 接口（`JPEG_LIB_VERSION = 80`）。
- `WITH_TURBOJPEG=FALSE` 与 `PNG_SUPPORTED=FALSE` 排除上层 `turbojpeg` 包装及 PNG 命令行工具依赖。
- `WITH_SIMD=FALSE` 关闭平台 SIMD 内核，使所有解码路径均运行可移植的标量 C 代码。

## 范围

- **Tier 0 解码安全性：** 在严格 ISO C17 下无未定义行为、无内存错误，并在非可信 JPEG 解码入口（`jpeg_std_error`、`jpeg_CreateDecompress`、`jpeg_mem_src`、`jpeg_save_markers`、`jpeg_read_header`、`jpeg_consume_input`、`jpeg_has_multiple_scans`、`jpeg_input_complete`、`jpeg_core_output_dimensions`、`jpeg_calc_output_dimensions`、`jpeg_resync_to_restart`、`jpeg_start_decompress`、`jpeg_read_scanlines`、`jpeg_read_raw_data`、`jpeg_finish_decompress`、`jpeg_abort_decompress`、`jpeg_destroy_decompress`、`jpeg_abort`、`jpeg_destroy`）上干净返回（或经 `error_exit` 跳转退出且不泄漏堆状态）。
- **已声明的功能定理：** `jdiv_round_up` 的精确向上取整除法、`jpeg_std_error` 的错误表与方法初始化，以及加载期缩放（`scale_num = 1`、`scale_denom ∈ {1, 2, 4, 8}`）下 `jpeg_core_output_dimensions` 的精确输出尺寸。

## 当前已证明的内容

- 严格 ISO C17 运行时模型拒绝 `NULL + 0`、悬垂指针 `+ 0`、`NULL - NULL`、跨对象指针减法及对 `NULL` 调用零长度 `memset`。
- `jdiv_round_up`、`jround_up` 与 `jzero_far`（`jutils.c`）安全；对不溢出的非负输入，`jdiv_round_up` 计算精确的 `⌈a / b⌉`。
- `jpeg_std_error`（`jerror.c`）安全，并初始化 `last_jpeg_message = 131`、`jpeg_std_message_table` 及标准错误处理方法，附带具体非空见证。
- 在有效对象不变量下，`jpeg_abort`、`jpeg_destroy`（`jcomapi.c`）、`jpeg_abort_decompress`、`jpeg_destroy_decompress`、`jpeg_input_complete` 与 `jpeg_has_multiple_scans`（`jdapimin.c`）安全。
- `jpeg_save_markers`（`jdmarker.c`）对所有 `COM`、`APP0`..`APP15` 及无效标记码和 `max_alloc_chunk` 边界均安全。
- `jpeg_core_output_dimensions` 与 `jpeg_calc_output_dimensions`（`jdmaster.c`）安全；在 `scale_num = 1`、`scale_denom ∈ {1, 2, 4, 8}` 时 `jpeg_core_output_dimensions` 返回精确的 `ceil(width / denom)` 与 `ceil(height / denom)`，且 `jpeg_calc_output_dimensions` 附带 1001×753 加载期缩放具体见证。

其余 Tier 0 解码函数（`jpeg_CreateDecompress`、`jpeg_mem_src`、`jpeg_read_header`、`jpeg_consume_input`、`jpeg_resync_to_restart`、`jpeg_start_decompress`、`jpeg_read_scanlines`、`jpeg_read_raw_data`、`jpeg_finish_decompress`）尚未完成。AddressSanitizer 与 UndefinedBehaviorSanitizer 下的差分测试将每个已翻译模块与真实静态 C 库进行比较；这些测试是翻译一致性的证据，而不是证明。参见[结论的状态](progress.html)、[前提与偏差](deviations.html)与[发现的问题](findings.html)。
