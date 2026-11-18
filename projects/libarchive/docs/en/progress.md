# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (`LibarchiveF.Runtime`) | Runtime model | done |
| RAR5 representation invariant, solid skip, and cleanup (`LibarchiveF.Model`) | Top-down model | done |
| RAR5 filter-queue throttle deadlock freedom and bitreader progress (`LibarchiveF.Model`) | Top-down model | done |
| 7-Zip folder DAG port conservation, substream bounds, and PPMd7 arena init (`LibarchiveF.Model`) | Top-down model | done |
| `archive_read_support_format_rar5.c` translated C safety | Public C API | not done |
| `archive_read_support_format_7zip.c` translated C safety | Public C API | not done |
| `archive_ppmd7.c` translated C safety | Public C API | not done |
