# 五阶证明的阅读顺序

本仓库收录五阶证明的完整 Lean 源码；下表保留证明章节编号作为阅读导航。
公开定理仍为 `SPR.N5.Direct.robustSPR`，位于 [Main.lean](../../Main.lean)。
建议先读精确陈述和最终组装，再按需要进入相应章节的实现。全部定义与定理保留原命名空间，目录路径统一位于 `SPR.N5`。

| 论文位置 | Lean 入口 | 主要作用 |
|---|---|---|
| §1，定理 1.1 | [Definitions/Frequency.lean](Definitions/Frequency.lean) | `RobustSPRStatement`：一个固定的实际五次分子、全族、全部实频率；允许退化区间。 |
| §2，式 (2.1)–(2.6) | [Definitions/General.lean](Definitions/General.lean) | `numeratorEven`、`numeratorOdd`、`generalPairing` 及四顶点约化。 |
| §2.1，分母交错 | [Preliminaries/HermiteBiehler.lean](Preliminaries/HermiteBiehler.lean) | `denominator_interlacing`；相位和系数正性分列于同目录。 |
| §2.2，统一零点区间 | [Preliminaries/RootBands.lean](Preliminaries/RootBands.lean) | `RootBands` 与 `Box5.rootBands`；区域编号见 `DenominatorZones`。 |
| §3，临界构造 | [Critical/FullWidthCritical.lean](Critical/FullWidthCritical.lean) | `Box5.fullWidth_critical_certificate`；稳定扩张、首次临界参数、有限表示各有独立模块。 |
| §3.3，合并同频率节点 | [Critical/MergedCertificate.lean](Critical/MergedCertificate.lean) | `MomentCertificate.merge` 保持矩、接触等式和支持界。 |
| §4.1–4.2，非负性的代数后果 | [Algebra/WeakCoprime.lean](Algebra/WeakCoprime.lean) | 顺次依赖公共根排除、分量非零、系数符号、根位置与互素性。 |
| §4.3，消失矩与插值 | [Interpolation/MomentInterpolation.lean](Interpolation/MomentInterpolation.lean) | `residuePoly`、`degree_residuePoly_moments`；一般有限插值引理独立于临界族。 |
| §4.3，常数倍与支持二分 | [Interpolation/ConstantMultiplier.lean](Interpolation/ConstantMultiplier.lean) | `constant_multiplier`、`support_dichotomy`；先证明非零，再比较精确次数。 |
| §5.1–5.2，接触重数 | [Contacts/StableContacts.lean](Contacts/StableContacts.lean) | 三接触、A/B 次序、零常数项 B/C 矛盾；`CornerContacts` 给实际顶点桥接。 |
| §5.3，Q1–Q5 | [Classification/QuinticReduction.lean](Classification/QuinticReduction.lean) | 必要候选逐项归入已证明的接触排除；四次情形见 `QuarticExclusion`。 |
| 附录 A，完整候选表 | [Classification/Classification.lean](Classification/Classification.lean) | 路径判定、完备枚举、2/3/21 项表及 Q1–Q5；计算全部在 Lean 内核中完成。 |
| §6，公共比值与三类不等式 | [Comparisons/RootRatios.lean](Comparisons/RootRatios.lean) | 根因子单调性、公共比值夹逼，以及 B/C、A/D、C/D 比较。 |
| §6，由实际接触到严格根序 | [Comparisons/TerminalGeometry.lean](Comparisons/TerminalGeometry.lean) | 将候选区间和节点符号转成三类比较的完整根序。 |
| §6，五项全部排除 | [Comparisons/FinalFiveExclusion.lean](Comparisons/FinalFiveExclusion.lean) | Q1/Q2 → A/D，Q3 → C/D，Q4/Q5 → B/C；另处理 b₅=0。 |
| §7，最终组装 | [Synthesis/CertificateExclusion.lean](Synthesis/CertificateExclusion.lean) → [Main.lean](../../Main.lean) | 排除全部临界表示，然后回到原区间族的存在性命题。 |

## 记号对应

| 论文 | Lean | 说明 |
|---|---|---|
| 稳定闭区间族 K | `Box5`、`K.RobustlyHurwitz` | 包含关系写为 `K.Contains a`。 |
| 各区间非退化 | `K.FullWidth` | 五个严格宽度不等式的简称，定义于 `Critical/ContractedBoxes`。 |
| b₀,…,b₅ | `b : Vec6`、`b 0` 至 `b 5` | 临界分子的次数可能为四；最终分子要求 `natDegree = 5`。 |
| E_b、O_b、P_{a,b} | `numeratorEven`、`numeratorOdd`、`generalPairing` | 函数参数 t 表示 ω²；多项式版本分别带 `Poly` 后缀或名为 `pairingPoly`。 |
| 支持节点、权重、无穷远质量 | `C.nodes`、`C.μ`、`C.μinf` | `C : DistinctMomentCertificate K b`；零节点与无穷远质量分别处理。 |
| R_z、R_y、U、V | `residuePoly`、`C.U`、`C.V` | `residuePoly` 是按节点权重构造的插值多项式，非新的数学假设。 |
| 分子区间编号 q_i | `D.phase t`、`P.phase t` | 旧名称 `phase` 在此表示区间编号，不是复数辐角。 |
| 分母符号/区域路径 | `StageSigns`、`Classification.ZonePath` | 与分子的 q_i 编号不同。 |
| Q1–Q5 | `Classification.finalFive` | `finalFive_cases` 按论文次序展开五种编号序列。 |
| h、g、h₀ | `inner`、`outer`、`below` | 根因子比值及其单调性。 |

`Certificate`、`Phases`、`TerminalContacts` 是整理已有数学数据及其性质的 Lean 结构；其字段都必须由前面引理构造，不能把最终综合结论藏作假设。`TerminalCertificate` 专门展示从原接触到顶点接触时，分量取值与符号如何保持。

## 结构与依赖

目录按论文数学主题组织；Lean 中使用某个辅助引理时仍须遵循实际声明依赖，因此导入顺序不要求与论文段落逐一相同。例如多项式配对接口同时提供后续重数分析的系数桥接。完整依赖图无循环，底层不导入 `Main` 或 `Audit`。

本仓库只维护五阶证明的 `SPR.N5.*` 实现和公共入口，不包含研究兼容转发模块。

## 验证

从工程根目录执行：

```sh
lake build
lake env lean Lean/Audit.lean
```

`lakefile.toml` 的 `SPR.+` 递归覆盖新增目录；最终定理及所有导入的 `SPR` 定理均做传递公理审计。只允许 `propext`、`Classical.choice`、`Quot.sound`。论文源码不是 Lean 内核的输入；本目录也不依赖 Python 生成证明。
