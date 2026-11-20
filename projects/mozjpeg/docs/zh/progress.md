<!-- source-sha256: 9189f0c482e86911689a8a806d466904d4a582313410667a3e5bd41587ab72db -->
# 结论的状态

整体库验证状态：**未完成**。

| 领域 | 类别 | 状态 |
| --- | --- | --- |
| 严格 ISO C17 指针、有符号算术检查与 `memset` 未定义行为拒绝 | 运行时模型 | 完成 |
| `jdiv_round_up`、`jround_up`、`jzero_far`：安全性与 `jdiv_round_up` 功能值 | 内部辅助函数 | 完成 |
| `jpeg_std_error`：安全性、消息表初始化与非空见证 | 公开 C 接口 | 完成 |
| `jpeg_abort`、`jpeg_destroy`、`jpeg_abort_decompress`、`jpeg_destroy_decompress`：安全性 | 公开 C 接口 | 完成 |
| `jpeg_input_complete`、`jpeg_has_multiple_scans`：安全性 | 公开 C 接口 | 完成 |
| `jpeg_save_markers`：安全性（`COM` / `APPn` / 无效标记 `error_exit`） | 公开 C 接口 | 完成 |
| `jpeg_core_output_dimensions`：安全性与加载期缩放（`1/2`、`1/4`、`1/8`）精确输出尺寸 | 公开 C 接口 | 完成 |
| `jpeg_calc_output_dimensions`：安全性与 1001×753 `1/4` 加载期缩放非空见证 | 公开 C 接口 | 完成 |
| `jpeg_CreateDecompress`、`jpeg_mem_src`（内存池分配器与内存数据源初始化） | 公开 C 接口 | 完成 |
| `jpeg_read_header`、`jpeg_consume_input`、`jpeg_resync_to_restart`（标记与头部解析） | 公开 C 接口 | 完成 |
| `jpeg_finish_decompress`（排空剩余标记并结束解码） | 公开 C 接口 | 完成 |
| `jpeg_start_decompress`、`jpeg_read_scanlines`、`jpeg_read_raw_data` | 公开 C 接口 | 未完成 |
