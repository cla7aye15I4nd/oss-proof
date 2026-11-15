<!-- source-sha256: b4e9a1e6190a714d803f42277880cb92d6d16c261597708380b486d5c6a5b050 -->

# 证明变异

例如，一个函数先检查写入边界，再写入字节；若删掉这个检查后，原证明仍被接受，就需要调查证明是否覆盖了这次访问。证明必须拒绝被验证函数中的故意错误。证明变异在临时副本中修改一个翻译后的函数，并要求失败发生在该函数的证明中。必须先确认未修改的证明通过，这一步称为正向基线。否则，“修改后失败”可能只是原版本来就无法检查。

这不同于 `tests/selftest.sh` 中的差分自测，后者要求执行比较发现变异。如果只有测试发现变异，可能暴露缺失的证明覆盖。证明拒绝变异说明它对变化敏感，但不证明变异改变了可观察行为，也不证明定理覆盖每种错误。审阅必须确认所需变异确实在允许输入上改变行为。

本页分四部分：两种检查，规则，如何添加和运行变异，以及为各组目标记录的证据。

## 两种检查

| 检查 | 做什么 | 何时算作拒绝 |
| --- | --- | --- |
| 重新繁饰（`tests/audit/proofmut.sh`） | 把列表中的一行应用到工作区副本上，并构建该行指定的证明模块。 | 第一个错误位于这些证明模块之一（`KILLED`）。 |
| 内核重放（`zlibf-proof-replay`） | 取出某个目标已登记的精确证明，在全新内核中只把变化的源码声明替换进它的依赖闭包。 | 内核报告类型不匹配。原版必须先被接受。 |

套件运行的每个列表的每一行都经过重新繁饰。某个目标在 `tests/audit/public-mutants.json` 中指定的行（它的**键**）还要另外经过内核重放。对重放而言，无关定理的失败，或带额外前提的更强定理的失败，都不足以满足要求。超时或内核资源错误不算拒绝。验收套件防御什么、不防御什么，见[防止取巧的规则](../anti-cheating.md)。

## 哪些目标需要哪种证据

| 目标 | 审计要求的证据 |
| --- | --- |
| 公开函数的功能目标 `Goal.<function>`，在它已被证明时 | `public-mutants.json` 中至少有一行的键。 |
| 函数自己的安全目标（`Goal.<function>_safety` 或 `_safe`），在它已被证明时 | 它自己的键。 |
| 不针对单个函数的已证明必需目标：四个序列安全目标、三个拒绝目标和四个非空性目标 | `scripts/verification.py` 中 `PINNED_EVIDENCE` 固定的证据。 |

针对单个公开函数的已证明目标若没有键，会被拒绝。脚本为此设有一个豁免列表（`MUTANT_COVERAGE_PENDING`）；它目前为空，并且只能缩小。已证明的必需目标若既没有键也没有固定证据，同样被拒绝。

**固定证据。**十一个已证明的必需目标没有自己的键。脚本为每个这样的目标固定了承载其证据的语义表，各表附有必须被杀死的最少行数，还固定了其重放同时检查该目标的带键目标（这些目标的证明是它的推论，或与它共用运行引理）。每个固定的表都必须是变异分片会运行的表。每个固定的带键目标至少要有一行。

| 目标 | 固定的表（必须杀死的最少行数） | 固定的带键目标 |
| --- | --- | --- |
| `gz_sequence_safety` | `gz-sequence.tsv`（43）、`gz-read.tsv`（18） | 无 |
| `inflate_back_sequence_safety` | `infback-sequence.tsv`（11） | 无 |
| `deflate_sequence_safety` | `deflate-header.tsv`（5）、`deflate-strategies.tsv`（10）、`deflate-ops.tsv`（7） | `deflate_safety`、`deflateEnd_safety` |
| `inflate_sequence_safety` | 无 | `inflate_safety`、`inflateEnd_safety`、`inflateCopy_safety` |
| `inflate_refusal`、`deflate_refusal` | `stream-refusal.tsv`（5） | 无 |
| `gz_refusal` | `gz-refusal.tsv`（19） | 无 |
| `inflate_initialisation_domain` | 无 | `inflateInit2__safety` |
| `deflate_initialisation_domain` | 无 | `deflateInit2__safety` |
| `inflate_back_initialisation_domain` | `infback-sequence.tsv`（11） | `inflateBackInit_` |
| `gz_sequence_nonvacuity` | `gz-sequence.tsv`（43） | `gzdopen` |

表中的列表都在 `tests/proof-mutants/` 下。

## 规则

### 带键的行

`public-mutants.json` 中指定的行必须满足以下全部条件。脚本检查第 1 到第 4 条；重放预算保证第 5 条。

1. 列表是 `tests/audit/proofmut/`、`tests/proof-mutants/` 或 `tests/proofmut/` 中的 `.tsv` 文件，名称恰好选中一行。
2. 该行的文件是带键函数的翻译源码。旧文本在该文件中恰好出现一次，位于函数体内，并且与新文本不同。签名保持不变。解析器在不加载候选导入的情况下检查两个版本。
3. 该行没有 `same:` 或 `gap:` 标记，并且指定了证明模块。
4. 修改另一个函数、只改规范或注入声明都不算。
5. **该行不得修改循环体或机器算术。**这类变异只放在源码级的表中，由重新繁饰检查。

有第 5 条，是因为内核重放不能在预算内驳倒所有种类的变异。只有内核类型不匹配才算拒绝。有两类修改会让内核无界地工作：

- 对自由变量做机器算术的修改，例如把 `x - left` 改成 `x - len`。为驳倒它，内核把 `UInt64` 和 `UInt32` 运算一直展开到 `Nat` 取模，却没有可计算的值。`uncompress2_z` 上实测：806 s 后达到 12 GiB 预算。
- `cdoWhile` 循环体内的任何修改，哪怕只是去掉一个测试。两个循环体比较失败后，惰性 delta 在两边展开 `cdoWhile`。它的燃料递归随后一次展开一轮迭代，并在每一步再次比较循环体。`compress2_z` 上实测：467 s 后达到 12 GiB 预算；去掉一个测试的变异 214 s 后达到 16 GiB。

循环外的修改很快被拒绝：去掉或替换的调用、去掉的存储、改变的常量。在 `uncompress2_z` 和 `compress2_z` 上，每个这样的行用 120 s 到 200 s，约 10.5 GB。因此键指定结构性变异。超出预算（12 GiB 常驻内存；可用 `ZLIBF_REPLAY_RSS_MB` 调整）的重放会被终止并判为失败，失败信息会提示把该行移走。闭包变大时不提高预算；解决办法是缩小重放闭包。

表中也保留算术变异和循环体变异，每个变异分片都用重新繁饰检查它们，证明必须在语义引理处失败。`tests/proof-mutants/api-boundary.tsv` 是一个例子：`uncompress2_z-destLen-count` 和两个 `refill-off-by-one` 行由重新繁饰检查。意图相同、修改是结构性的行承担内核重放：`uncompress2_z-destLen-drop`（错误的 `destLen` 计数），以及两个 `initial-room` 行（输出空间超过剩余量）。

### 好的变异

有用的变异会删除检查或赋值，改变界限或比较，改变下标或移位，或返回错误结果。应选择已证明函数的不同部分。语法错误，或仅破坏源码相等性引理的变异，都不足以证明其执行契约的敏感性。

有些证明用一条 `rfl` 等式重述函数的代码，再对重述做推理。对这种函数只改一个文件，会先在该等式处失败，这只说明证明与翻译绑定在一起。`script:` 行解决这个问题：它的脚本在翻译和证明对它的每处重述中做相同修改，使得只有语义引理会失败。脚本行不能带键（第 2 条），所以它放在语义表中。

### 冻结的行

语义安全表（脚本中的 `SAFETY_MUTANT_LISTS`）和 `tests/proof-mutants/api-boundary.tsv` 的行沿[只减不增规则](goals.md#shrink-only-rules)的提交链冻结：包括每个字段、`PROOF_MODULES` 列和标记，以及 `script:` 行变异脚本的 sha256。可以添加行。修改或删除一行需要在 `tests/audit/registry-removals.json` 中有 `mutant_rows` 条目 `{list, name, reason}`；什么也不豁免的条目会被当作过时条目拒绝。

已证明目标的键所引用的行以同样方式受保护：没有 `mutant_references` 条目 `{goal, list, name, reason}`，引用不能消失，被引用行的文件、旧文本和新文本也不能改变。因此提交者不能不在差异中留下理由就删掉某个目标的键、把它的行减到一行，或把某一行换成更弱的行。

语义安全表是 `tests/proof-mutants/` 下的 `deflate-header.tsv`、`deflate-strategies.tsv`、`deflate-ops.tsv`、`stream-refusal.tsv`、`infback-sequence.tsv`、`gz-refusal.tsv`、`gz-sequence.tsv` 和 `gz-read.tsv`。其中任何一个缺失或为空，分片就失败。

### 每个表至少杀死一行

严格模式下的 `proofmut.sh` 至少需要一个 `KILLED` 行；能构建的 `same:` 行不是证据。分片把每个 `same:` 行分给同时运行该表某个可杀死行的分片。没有可杀死行的表会被拒绝。

## 添加变异

1. 选择列表。将带键的公开函数结构性变异放在 `tests/proof-mutants/` 下的列表中（例如 `public-safety.tsv`）。循环体或机器算术中的变异，以及需要成对修改的变异，放在语义表中。
2. 添加一行，字段以制表符分隔。以 `#` 开头的行是注释。

   ```text
   NAME <TAB> FILE <TAB> OLD <TAB> NEW <TAB> PROOF_MODULES [<TAB> same:REASON | gap:REASON]
   ```

   | 字段 | 含义 |
   | --- | --- |
   | `FILE` | 相对仓库根目录的翻译源码路径，例如 `ZlibF/Zlib/adler32.c.lean`。也可以是 `script:PATH`：执行器调用 `python3 PATH <copy> NAME` 来生成变异；此时 `OLD` 和 `NEW` 写作 `-`。 |
   | `OLD`、`NEW` | 替换文本。字面量 `\n` 表示换行；`OLD` 必须恰好出现一次。 |
   | `PROOF_MODULES` | `ZlibF/Proof` 下用逗号分隔的路径，不带 `.lean`，指明预期的函数证明。只构建这些模块。 |
   | 可选标记 | `same:` 解释等价性；`gap:` 仅为开发记录缺失覆盖。带键的行中两者都不允许。 |

3. 用列表执行器运行这一行，并阅读判定（见下一节）。

   ```sh
   bash tests/audit/proofmut.sh tests/proof-mutants/public-safety.tsv '^deflatePrime'
   ```

4. 对带键的行，在 `tests/audit/public-mutants.json` 中该目标之下添加 `{"list": ..., "name": ...}`，然后检查这个键。

   ```sh
   python3 scripts/verification.py coverage
   ```

5. 对没有键的目标，在 `PINNED_EVIDENCE` 中添加或提高它的条目。这是对 `scripts/` 的修改，需要审查。

## 运行检查

在仓库根目录、已有预热 `.lake` 构建缓存时运行：

```sh
python3 scripts/verification.py mutants
python3 scripts/verification.py mutants --shard-count 20 --shard-index 3
bash tests/audit/proofmut.sh tests/audit/proofmut/adler32.tsv
bash tests/audit/proofmut.sh tests/audit/proofmut/crc32.tsv '^combine'
```

第一条命令构建项目，然后对每个带键的目标检查解析后的变异边界，重放原来的精确证明，并重放每个带键的行。随后它以严格模式运行 `api-boundary.tsv`、各语义安全表以及键所引用的每个列表。第二条命令运行二十个分片中的一个，与 CI 相同。最后两条运行单个列表，可按变异名称筛选。它们用于开发，不能替代验收。

**分片。**带键的目标按名称顺序分给各分片；每个目标未修改的对照重放与它的全部带键行在同一分片。各列表的可杀死行轮流分配，所以没有行丢失或重复运行。无事可做的分片会被拒绝。

**列表执行器**将工作区和预热缓存复制到临时目录，先构建未修改的指定证明模块，再对每个替换恰好应用一次，只构建指定模块。第一个报告的错误必须位于预期证明模块。原缓存保持不变。一次只运行一个变异。

| 判定 | 含义 |
| --- | --- |
| `KILLED` | 第一个错误位于预期证明模块。变异检查通过。 |
| `SAME ok` | 显式标为等价的变异仍能构建。应审阅等价理由。 |
| `GAP (known)` | 已记录的证明缺口在开发模式下存活。它不算覆盖，严格验收会失败。 |
| `SURVIVED` | 没有正当豁免的变异仍能构建。调查缺失覆盖或等价性。 |
| `BAD MUTANT` | 翻译或证明树以外的文件失败。修复变异。 |
| `WRONG PLACE` | 另一个证明先失败。不满足指定函数的检查。 |
| `SORRY` | 变异后的副本含有 `sorry`。修复变异。 |
| `NO ERROR` | 即使重试一次，构建失败仍没有可识别错误。未建立证明拒绝的证据。 |
| `UNEXPECTED` | 标为等价的变异失败。审阅标记和变异。 |
| `NOT APPLIED` | 替换文本没有恰好出现一次，或者内容未改变，或者变异脚本失败。更新变异。 |

被杀死的变异若仍带过时的 `gap:` 标记，也会失败。缺口关闭后移除该标记。严格模式强制执行正向基线，拒绝已知缺口，并要求有 `KILLED` 行。跳过基线不能支持最终验收。

**执行器设置。**`PROOFMUT_CACHE` 选择预热缓存。`PROOFMUT_TIMEOUT` 设置每次构建的秒数，默认 3600。`PROOFMUT_KEEP=1` 保留临时副本；`PROOFMUT_SHOWLOG=1` 输出失败细节。`PROOFMUT_BASELINE=0` 仅为本地诊断跳过正向构建。`PROOFMUT_STRICT=1` 会覆盖这个跳过设置，拒绝所有已知缺口，并要求有被杀死的行。

**哪里运行什么。**每晚的套件运行这二十个分片。既没有键引用、又不是语义安全表或 `api-boundary.tsv` 的列表，分片不会运行；它只在 `python3 scripts/verification.py final` 中运行，后者以严格模式运行三个目录中的每个列表。建议中的工作流片段和没有执行过的列表，都不算通过的检查。

## 已知限制

- 审计工具（`tests/audit/*.lean`）、`proofmut.sh`、`selftest.sh` 和变异脚本（`tests/proof-mutants/*.py`）是受信任的，与 `scripts/` 一样靠审查保护。变异脚本的内容由其哈希冻结，但它做什么只能靠阅读来检查。特别是 `proofmut.sh` 的 `BAD MUTANT` 保护把第一个错误与该行的 `FILE` 比较，而 `script:` 行的 `FILE` 是脚本本身，所以把错误写进预期证明模块的变异脚本会被算作 `KILLED`。要堵上这一点需要重新设计脚本行；目前靠审查防范。
- 带理由的删除条目是每个只减不增检查的经审查的出口。它在差异中可见，过时的条目会被拒绝。
- 修订链覆盖 `HEAD` 仍包含的、在固定下限提交之后的历史。在下限之后改写 `dev` 的强制推送会逃过它；防范手段是禁止强制推送的分支保护。
- 一次杀死只说明证明对这一处修改敏感。它不说明目标覆盖了每种错误；列表存在或历史结果也不证明其 C 文件中的每个函数都被覆盖。

## 记录的证据

这一部分为每组目标记录由哪些行承载证据，以及它们在哪里被杀死。列表和 `public-mutants.json` 才是依据；测量数据来自登记这些目标时的运行。当前的覆盖工作记录在[进度](../progress.md)中。

### 列表

`tests/audit/proofmut/` 下的列表覆盖校验和、辅助函数、树、inflate、deflate 和解码表证明组。其他列表位于 `tests/proof-mutants/` 和 `tests/proofmut/`。这些文件和键定义它们的确切范围。

### `Goal.deflate`

`Goal.deflate` 的带键行（`tests/proof-mutants/public-deflate.tsv`）是对 `deflate` 函数体的单文件修改。每一行都先在 `deflate_phases` 处被拒绝，这是把 `deflate` 拆成各阶段的 `rfl` 等式；对函数体的任何修改都会在那里失败。所以这些行说明已登记的证明与翻译绑定，而不说明它依赖被变异的检查。它们之所以可用于精确重放，只是因为语义上的杀死由每个变异分片都运行的脚本行列表承担：`deflate-header.tsv`（头部各阶段和 `_tr_flush_block`）、`deflate-strategies.tsv`（`fill_window`、`longest_match` 和各策略）以及 `deflate-ops.tsv`（流操作）。每个脚本行在翻译和证明对它的每处重述中做相同修改，并且必须在其语义引理中被杀死。

### `Goal.deflateCopy` 和拒绝目标

`Goal.deflateCopy` 在 `tests/proof-mutants/public-streams.tsv` 中的五行都是结构性的：
- 空目标返回 `Z_OK`；
- 状态分配失败时返回 `Z_OK`；
- 缓冲区失败路径保留 `dest->state`；
- 缓冲区失败路径跳过对 `pending_buf` 的释放；
- 副本的反向指针被设为源。

每一行都被重放拒绝；`deflate_copy_public` 的重放峰值约为 10.4 GB。拒绝目标 `Goal.inflate_refusal` 与 `Goal.deflate_refusal` 没有键。它们的行在 `tests/proof-mutants/stream-refusal.tsv` 中，由变异分片以重新繁饰检查：每一行把一次拒绝改为 `Z_OK`。

### 各函数的安全目标

大多数函数的安全目标用的是其功能目标的那些行：流调用的安全证明是序列定理（`inflate_sequence_safety_public`、`deflate_sequence_safety`，调用用第 2 条，`End` 用第 3 条）的推论，初始化、复制和无状态函数的安全证明是其功能证明的推论，所以同样的翻译修改必须使它们失败。没有这类行的函数，其行在 `tests/proof-mutants/public-safety.tsv` 中，都是结构性的：
- `compress`、`compress_z`、`compress2`：不传递长度指针（改传 `NULL`）。`api-boundary.tsv` 中让 `compress2` 在 `destLen` 为 `NULL` 时返回的那一行不是 `Goal.compress2_safety` 的变异体：C 先读取 `*destLen`，所以该目标排除 `NULL` 长度（`CompressorSafety` 取 `nullableLength = false`），重放接受这一行；
- `uncompress2`：目标长度从 `sourceLen` 读取；去掉一个局部单元的释放；
- `uncompress_z`、`uncompress`：把源长度单元当作目标长度传递；去掉局部单元的释放；
- `deflateBound`：丢弃结果；`deflateBound_z`：去掉状态检查；
- `deflatePrime`：去掉 `bits > 16` 的测试；去掉待输出空间的测试；
- `inflateSync`：局部缓冲区是三个字节而不是四个。

`deflateParams` 和 `deflateSetDictionary` 用 `stream-refusal.tsv` 中它们的拒绝行。去掉 `deflateEnd` 或 `inflateEnd` 调用的行属于发出该调用的 `compress2_z` 和 `uncompress2_z`。`Goal.deflate_initialisation_domain` 没有键：它陈述 `deflateInit2_` 的成功运行，`deflateInit2_` 的四行就是它的变异体：对 `deflate_initialisation_domain_public` 的内核重放拒绝全部四行（峰值约 3.4 GB）。

### `Goal.inflate_back_sequence_safety`

它的十一行在 `tests/proof-mutants/infback-sequence.tsv` 中：`inflateBack` 四行、`inflateBackInit_` 四行、`inflateBackEnd` 三行，都是结构性的：
- `inflateBack`：空流返回 `Z_OK`；模式没有重置为 `TYPE`；输出从 `NULL` 而不是窗口开始；结束之后最后一个窗口被拒绝时返回 `Z_OK`；
- `inflateBackInit_`：状态没有存入流；窗口没有存入；分配失败返回 `Z_OK`；`sane` 被清零；
- `inflateBackEnd`：跳过对状态的释放；保留 `strm->state`；返回 `Z_STREAM_ERROR`。

收尾部分的那一行是脚本（`infback-sequence.py`），它在重述 `backTail` 中做相同修改，使失败的是语义引理，而不是 `inflateBack_eq` 的 `rfl`。变异分片以重新繁饰检查这些行。用每行的翻译修改对 `inflate_back_sequence_safety` 做内核重放，也拒绝全部十一行；原始证明的重放峰值约为 9.8 GB。

### gz 目标

gz 目标没有键；它们的行在三个语义表中。
- `tests/proof-mutants/gz-refusal.tsv`，对应 `Goal.gz_refusal`：十九行，每行在 `NULL` 句柄上改变返回值或去掉 `NULL` 检查，覆盖除 `gzread` 与 `gzfread`（在 `gz-read.tsv` 中）以及 `gzbuffer`、`gzeof` 与 `gzoffset64`（在 `public-streams.tsv` 中）之外的每个 gz 函数。目标的子句由求值成立，所以每行都在 `public-gz-refusal` 中失败。
- `tests/proof-mutants/gz-sequence.tsv`，对应 `Goal.gz_sequence_safety`：写入调用（`gzwrite`、`gzfwrite`、`gzputc`、`gzputs`、`gzvprintf` 从而 `gzprintf`、`gzflush`、`gzsetparams`）、关闭（`gzclose_w`、`gzclose_r`、`gzclose` 的分派）、打开（`gz_open`、`gzdopen`）、`gzseek64` 与 `gztell64`、`gz_error`（跳过释放；为 `Z_MEM_ERROR` 分配消息）、`gzgetc()` 宏的两个分支（`zlib.h.lean`：去掉 `have` 检查；`pos` 不前进）、读取叶子 `gzgetc`、`gzungetc`、`gzgets` 与 `gzdirect`，以及补丁 0002 到 0005 的每个补丁块各一行，去掉该补丁块（即未打补丁的 C）。大多数行是脚本行（`gz-sequence.py`），在代码的每个 `rfl` 重述（`gzwrite_eq`、`putcSlow`、`closeTail`、`pfFmt`、`gTail`、`seekTail`、`openAfterMode`、`fetchBody`、`restK`、`getsRest`、`gz_error` 的私有副本）中做相同修改，使失败的是语义引理，而不是重述。
- `tests/proof-mutants/gz-read.tsv`（及 `gz-read.py`），来自读取侧：`gzread`、`gzfread`、`gzgetc` 与 `gzungetc` 的拒绝，以及 `gzclose_r`。其中两行 `gzungetc-mode-check` 与 `gzungetc-skip-dropped` 还列出步骤引理所在的模块 `gz.read-getc-step`：只列 `gzread.c.getc-ungetc` 时不会构建 `gzungetc_step` 的证明，两行都能构建通过；列出后两行都在那里被杀死。

**第一个错误的位置。**每一行都在被变异函数的证明中被杀死：其步骤引理、其函数体的精确运行，或（对被调用者）该被调用者的证明。有五行列出步骤引理之外的模块，它们都是被变异函数的证明：三行 `gz_open` 在 `gz_open` 的精确运行中失败（`gzlib.c.open-init` 中的 `gz_open_empty_mode`，`gzlib.c.open-io` 中的 `openAfterPath_writer`：`gz_open` 的 I/O 尾部，它释放路径并调用 `gz_reset`），`gzdopen` 一行在 `gzdopen` 的运行中失败（`gzdopen_writer_regular_run`，`gzlib.c.dopen-entry`），`gztell64` 一行在 `gztell64` 的运行中失败（`gztell64_run`，`gzlib.c.simple`）。`gzclose_w` 的各行在 `closeTail_ok`（`gzwrite.c.close`）中失败，即 `gzclose_w` 的释放证明；`gzclose` 的分派一行在 `gzclose_dispatch` 中失败。有一行由心跳超时而非类型错误杀死：`patch0004-fetch-copy-room-removed`，在 `fetch_look`（`gz.read-fetch`）中，这是同一函数 `gz_fetch` 的证明。

**发现目标有误的一行。**`macro-have-guard-dropped` 一行起初存活：目标只在 `x.have ≠ 0` 时运行宏，所以它的 `have = 0` 分支从未被运行。目标已更正（3c5292f7；回归 `tests/verification/regressions/gz-macro-have-zero.lean`），该行现在在 `zlib.h.gzgetc-macro` 中被杀死。

**gz 各表的内核重放。**变异分片以重新繁饰检查这三个表。对 `gz_refusal` 的内核重放拒绝全部十九行拒绝变异（每次重放在两秒内结束）。用每个结构性行的翻译修改对 `gz_sequence_safety_public` 做内核重放（不含位于循环体或机器算术中的行：`patch0003-*`、`gz_fetch` 与 `gz_read` 的三行 `patch0004`、`patch0004-gets-room-removed`、`gzgets-left-whole-length`、`gztell64-adds-max`），接受原始证明（51615 个依赖，峰值约 10.7 GB），并拒绝所给 36 行中的 29 行，多数在被变异函数的重述处（`gzwrite_eq`、`gzclose_w_eq`、`gzgetc_macro_eq` 等），峰值约 10.7 GB。有七行在得出结论之前达到 12 GiB 预算：`gzvprintf-length-check-dropped`、`gz_open-open-failure-path-leak`、`gz_open-reset-skipped`、`gzseek64-have-not-consumed`、`gzseek64-skip-wrong`、`patch0005-seek-next-unconditional` 与 `patch0004-printf-position-check-removed`。它们所在的函数（`gzvprintf`、`gz_open`、`gzseek64`）含有循环，函数体不同时内核会展开该循环；对这些行，以重新繁饰杀死为证据。
