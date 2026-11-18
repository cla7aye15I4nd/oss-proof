# Status of the results

Overall library status: **not done**.

| Area | Kind | Status |
| --- | --- | --- |
| Strict ISO C17 pointer and `memset` UB rejection (`SevenZipF.Runtime`) | Runtime model | done |
| `.7z` folder DAG acyclicity and `SzArEx` solid-cache coherence (`SevenZipF.Model`) | Top-down model | done |
| BCJ2 4-stream in-place overlap and range-decoder bounds (`SevenZipF.Model`) | Top-down model | done |
| PPMd7 arena partition and `SplitBlock` unit conservation (`SevenZipF.Model`) | Top-down model | done |
| LZMA lookahead margin and LZMA2 control-byte state guards (`SevenZipF.Model`) | Top-down model | done |
| `SzArEx_Open` / `SzArEx_Extract` / `SzArEx_Free` translated C safety | Public C API | not done |
| `Bcj2Dec_Decode` translated C safety | Public C API | not done |
| `Ppmd7_Alloc` / `Ppmd7_Init` / `Ppmd7_DecodeSymbol` translated C safety | Public C API | not done |
| `LzmaDec_DecodeToBuf` / `Lzma2Dec_DecodeToBuf` translated C safety | Public C API | not done |
