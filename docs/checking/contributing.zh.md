<!-- source-sha256: b9f2e885a567cd08f2889528918bcd2896c436a436d2951ded324856dd6a3663 -->
# 参与贡献

本页列出三件事的步骤：做任何一次改动，登记一个已证明的目标，运行验收套件。每一步给出命令，以及命令成功时打印的最后一行。所有命令都在仓库根目录运行。

规则在 `AGENTS.md` 中。每项检查能确立什么，以及已检查、已登记、已验收三个层级，见[检查指南](README.md#three-levels)。

**哪些“最后一行”是原样的。**标有“（已运行）”的行，抄自在提交 `8642e435` 上对该命令的一次运行。标有“（取自脚本）”的行，是脚本成功时打印的文字，读自脚本源码；这条命令需要 Lean 构建，写本页时没有运行。

## 每次改动

1. 获取源码，包括上游子模块。如果克隆时没有带子模块，运行 `git submodule update --init zlib`。

   ```bash
   git clone --recurse-submodules <repository-url>
   ```

2. 从 `dev` 开一个分支工作。提交要小。按路径暂存文件。推送到 `dev`；或者在快速关卡全部通过后，把拉取请求合并到 `dev`。不需要审查。

3. 构建库和审计工具。最多使用四个并行任务，内存上限 16 GB。`crc32.c` 和 `inftrees.c` 的证明各需要 8 到 9 GB。

   ```bash
   lake build ZlibF zlibf-audit zlibf-span zlibf-proof-replay
   ```

4. 运行快速关卡的其余检查。

   | 命令 | 是否需要第 3 步的构建 | 成功时的最后一行 |
   | --- | --- | --- |
   | `scripts/check-sorry.sh` | 否 | `sorry count: 0`（已运行） |
   | `python3 scripts/check-strlit.py` | 否 | `check-strlit: 19 literals used, all in strTable (178 entries)`（已运行） |
   | `python3 scripts/check-spec-layers.py` | 否 | `specification layers: 35 safety and common modules import no functional module`（已运行） |
   | `lake env lean --run tests/audit/PartialCheck.lean` | 是 | 写本页时没有运行 |

   最后一项检查是一次搜索，成功时什么也不打印（已运行）：

   ```bash
   grep -rnE '\b(native_decide|bv_decide|implemented_by)\b|^\s*axiom\b' ZlibF.lean ZlibF
   ```

   它是 `lean.yml` 中那个模式的简写；完整的模式还拒绝 `partial`、`unsafe`、`opaque` 和 `extern`。

5. 如果改了 `patches/`，检查每个补丁都能应用到固定的上游源码上。每个补丁都能应用时，这些命令什么也不打印。写本页时没有按这个形式运行它们；五个补丁是用 `patch -p1` 应用到固定版本源码的一份副本上的，没有出错。

   ```bash
   rm -rf /tmp/zlib-verified && cp -r zlib /tmp/zlib-verified && rm -rf /tmp/zlib-verified/.git
   for p in patches/*.patch; do (cd /tmp/zlib-verified && git apply "$OLDPWD/$p"); done
   ```

6. 如果改了 `docs/`，构建并检查网站。使用 Python 3.12 或更新的版本。

   ```bash
   python3 -m pip install -r docs/web/requirements.txt
   python3 docs/web/build.py
   python3 docs/web/check.py
   node --test docs/web/tests/*.test.mjs
   ```

   `build.py` 的最后一行是 `Built the landing page and the status summary`（已运行）。`check.py` 的最后一行以 `Static checks passed:` 开头，给出页面数（已运行）；链接或锚点失效时，它以一个 `AssertionError` 停下，其中写出页面和链接。`node` 的运行以一段汇总结束，要看的是其中的 `# fail 0` 一行（已运行）。

7. 每份英文文档旁边都有一份中文对应文件 `*.zh.md`。`docs/` 之外的文件，其对应文件在 `docs/web/content/repository/` 下。对应文件的第一行记录英文文件的 `source-sha256`。改了英文文件之后，在同一个提交里更新中文文本并填好哈希。

   ```bash
   sha256sum docs/glossary.md
   ```

   没有 `sha256sum` 的系统上，`shasum -a 256` 打印同样的哈希。

   对应文件过时不会让构建失败。这时中文页面会显示一条提示，说明英文源文件比它新。

8. 推送到 `dev`。每次推送和每个拉取请求都会运行快速关卡（`build`、`no-sorry`）。它是合并的唯一关卡。如果一次推送让它失败，先修复它。

改动翻译时，还需要一个能发现旧行为的差分测试（`AGENTS.md`）。改动目标或规格时，单独用一个提交，并把反例保存在 `tests/verification/regressions/` 下。

第 8 步之后，快速关卡全部通过，新的定理就是**已检查**的。

## 登记一个结果

登记在里程碑处成批进行，不是每次改动都做。里程碑是指：`inflate` 证完、`deflate` 证完、一个序列目标证完，或者新增了大约二十个已检查的目标。[公开目标](goals.md#what-a-registration-needs)说明每一项为什么需要。

下面以 `adler32` 的安全目标为例。其中的登记行是真实的：它们就在所说的文件里。

1. **检查定理的类型。**类型恰好是这个目标：没有多出的前提，也不是别的常量。定理有文档字符串；已登记的定理没有文档字符串时，审计器拒绝。如果目标的前置条件比 zlib.h 更窄，文档字符串要写明，并且 `docs/deviations.md` 中有对应的一行。

   ```lean
   /-- `Goal.adler32_safety`: `adler32` runs without fault on every input its contract allows; ... -/
   theorem adler32_safety : Goal.adler32_safety := ...
   ```

   （`ZlibF/Proof/public-stateless-safety.lean`。目标定义在 `ZlibF/Spec/Safety/Checksums.lean` 中。）

2. **把定理加入 `tests/audit/theorems.txt`**：它的完全限定名，单独占一行。

   ```text
   ZlibF.Spec.Public.StatelessSafetyProof.adler32_safety
   ```

3. **把目标加入 `tests/audit/proved-goals.txt`**：它的完全限定名，单独占一行。

   ```text
   ZlibF.Spec.Public.Goal.adler32_safety
   ```

4. **只针对新目标**：把同一个目标名加入 `tests/audit/goals.txt`。库中的 `Goal.*` 命题若没有列在那里，审计器拒绝。

5. **只针对新加入必需集合的目标**：把它的名字加入 `tests/audit/public-api.json` 的分组 `safety_goals`，并加入 `scripts/verification.py` 的函数 `coverage` 中同名的列表。如果它是某一个函数的安全目标，还要在清单中该函数的条目里设置 `safety_goal` 字段：

   ```json
   "safety_goal": "ZlibF.Spec.Public.Goal.adler32_safety"
   ```

   对 `scripts/` 的改动要经过审查。如果目标列在清单文件的 `open_safety` 中，在这个提交里删掉那个条目：一个目标不能既未证明又已证明。

6. **添加变异体证据。**针对单个公开函数的目标，需要在 `tests/audit/public-mutants.json` 中有一个键，其中至少指定一个变异体行：

   ```json
   "ZlibF.Spec.Public.Goal.adler32_safety": [
     {"list": "tests/proof-mutants/public-checksums.tsv", "name": "adler32-wrapper-length"}
   ]
   ```

   [证明变异体](proof-mutants.md)解释这一行，并说明怎样写一行。运行这一行。这需要上面第 3 步的构建（已构建好的 `.lake` 缓存），并且要把四个证明模块构建两遍。

   ```bash
   bash tests/audit/proofmut.sh tests/proof-mutants/public-checksums.tsv '^adler32-wrapper-length$'
   ```

   最后一行：`PROOFMUT PASS`（取自脚本）。

7. **核对函数清单。**这需要子模块，不需要构建。

   ```bash
   python3 scripts/verification.py coverage
   ```

   最后两行（已运行）：

   ```console
   coverage: 96 public declarations, 95 default-build entries (86 documented, the rest undocumented in zlib.h), 4 sequence targets, 4 non-vacuity targets, 57 safety targets; 63 required goals, 0 open
   coverage is not specification readiness or proof completion
   ```

   失败时打印一行 `REJECTED: <reason>`。上面第二行是一句提醒：这条命令检查清单文件、头文件和键是否一致，不检查任何证明。

8. **重新生成进度视图**，也就是 `docs/progress.md` 和 `docs/progress.zh.md` 中 `proof-progress` 两个标记之间的那一块。这需要上面第 3 步的构建。

   ```bash
   python3 scripts/proof-progress.py
   python3 scripts/proof-progress.py --check
   ```

   两条命令各打印一行 JSON，给出目标的数目和它们的状态；第二条的输出中有 `"checked": true`（取自脚本）。视图过时时，第二条命令失败，并打印 `Progress generation failed: ...`。

9. **把登记行、变异体行和重新生成的视图一起提交并推送。**这个目标在该提交上就是**已登记**的。它还不是已验收的：在验收套件检查之前，这些行只是一个声明。

## 运行验收

验收套件就是手动启动的工作流 `lean`，或它每晚在 `main` 上的运行。下面的本地命令是它的各个部分。如果某种失败在 CI 中要很久才能发现，就在启动工作流之前先在本地运行它们。

1. **审计。**它需要完整的历史（浅克隆中先运行 `git fetch --unshallow`）和基线分支 `origin/main`。

   ```bash
   python3 scripts/verification.py specs
   ```

   最后一行：`stage passed: specs`（取自脚本）。失败时打印 `REJECTED: <reason>`；如果是审计器拒绝，它前面的各行以 `goal ` 或 `PROBLEM:` 开头。

2. **变异体。**这条命令在一个进程里运行所有分片，要很多个小时。在 CI 中，变异体分二十个分片运行（`--shard-count 20 --shard-index N`）。

   ```bash
   python3 scripts/verification.py mutants
   ```

   最后一行：`stage passed: mutants`（取自脚本）。

3. **差分测试**，普通构建一遍，C 在 sanitizer 下再一遍。

   ```bash
   ZLIB_SRC=$PWD/zlib bash tests/run.sh
   SAN=1 ZLIB_SRC=$PWD/zlib bash tests/run.sh
   ```

   每条命令成功时退出状态为 0；脚本在第一个失败的驱动程序或回归测试处停下（取自脚本）。套件还运行两个自测：`bash tests/audit/selftest.sh` 和 `bash tests/selftest.sh`；后者以 `SELFTEST PASS` 结束（取自脚本）。

4. **在已推送的提交上启动套件。**在仓库的 Actions 页面上选择工作流 `lean`，点“Run workflow”，再选分支 `dev`。这个工作流有手动触发方式（`.github/workflows/lean.yml` 中的 `workflow_dispatch`）；用它启动时，除快速关卡外还会运行验收的各个工作任务。

5. **读两项结果。**`audit` 和 `difftest` 两项结果都通过时，这次运行就是全部通过。其中任何一个工作任务失败、被跳过或被取消，对应的结果就失败。

6. **报告。**结果在该提交上是**已验收**的。报告中写“已验收”时要同时写出提交的哈希，[进度页的“范围”一节](../progress.md#scope)记录这个提交。在这之后，`main` 接收 `dev`。

没有运行过的检查，决不能报告为通过。差分测试是关于忠实性的证据，不是证明。

## 删除或修改已登记的条目

已登记的定理、已证明的目标、变异体引用或冻结的变异体行如果消失或改变，审计会拒绝（见[防止悄悄删除的规则](goals.md#shrink-only-rules)）。确实应当删除时，在同一个提交里向 `tests/audit/registry-removals.json` 添加一个带理由的条目。这个条目就是这次删除经过审查的记录。什么也不豁免的条目，审计会拒绝。
