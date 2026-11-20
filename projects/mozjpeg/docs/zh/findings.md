<!-- source-sha256: ca042ab5bfef3f8da2319e77b0d751918e4c1d0d7caf0d5649ed7bde3cb98aaf -->
# 发现的问题：mozjpeg 中的缺陷

在目前已完成形式化验证的 Tier 0 解码函数（`jutils.c`、`jerror.c`、`jcomapi.c`、`jdapimin.c` 中的清理与查询辅助函数、`jpeg_save_markers` 与 `jpeg_calc_output_dimensions`）中，尚未确认上游缺陷或 ISO C17 未定义行为。

后续若在头部解析、哈夫曼解码、IDCT 或上采样验证中确认了可通过有文档公开接口触达的上游缺陷或严格 ISO C17 未定义行为，将连同真实 C 复现与最小补丁一并记录在此页。
