# 五阶 SPR 证明

[English](README.md)

本仓库是一个独立的 Lean 4 / mathlib 形式化工程，证明实系数首一五阶区间多项式族的鲁棒严格正实（SPR）综合定理。

## 本仓库证明的结论

考虑 5 个彼此独立的有限闭系数区间，允许退化区间。假设**区间箱内每个分母均严格 Hurwitz 稳定**（所有根的实部为负），则存在**同一个实际次数恰为 5 的实系数分子**，使得

$$
\mathrm{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\quad\text{对箱内每个分母 }a\text{ 以及每个 }\omega\in\mathbb R.
$$

同一个分子适用于整个区间箱和全部实频率，包括零频率。这是存在性定理，不是数值综合算法，也不是任意阶数的定理。

- 公开定理：[`SPR.N5.Direct.robustSPR`](Lean/Main.lean)。
- 精确定义：[`Lean/SPR/N5/Definitions/Frequency.lean`](Lean/SPR/N5/Definitions/Frequency.lean)。
- [模块指南](Lean/SPR/N5/README.md) · [证明思路](docs/PROOF.md) · [核验记录](docs/VERIFICATION.md)。

## 环境安装与构建

安装 Git 和 [elan](https://github.com/leanprover/elan)（Lean 工具链管理器），并确认 `elan`、`lean`、`lake` 已加入 PATH。以下命令适用于 macOS、Linux 或 Windows 的 WSL 环境，在仓库根目录执行。

```sh
git clone https://github.com/dgjszy/quintic-spr-proof.git
cd quintic-spr-proof
lake exe cache get
lake build
```

`lean-toolchain` 固定 Lean **4.30.0**，mathlib 固定为 **v4.30.0**，精确依赖提交记录在 `lake-manifest.json`。首次运行需要联网下载工具链、依赖和编译缓存；保留锁文件，正常构建无需运行 `lake update`。缓存用于加速依赖构建，项目证明源码由 Lean 检查。

本仓库作为本地证明库使用，无需部署服务器或配置数据库。正式构建不需要 Python 或外部求解器。

## 验证与使用

```sh
lake env lean Lean/Audit.lean
```

默认构建包含传递公理审计，仅允许 `propext`、`Classical.choice` 和 `Quot.sound`；发现其他公理时会报错。

在本工程的 Lean 环境中使用：

```lean
import SPR

#check SPR.N5.Direct.robustSPR
#print axioms SPR.N5.Direct.robustSPR
```

## 仓库结构

- [`Lean/Main.lean`](Lean/Main.lean)：公开定理与最终证明组装。
- [`Lean/SPR.lean`](Lean/SPR.lean)：公共导入入口。
- [`Lean/SPR/N5/`](Lean/SPR/N5/)：定义与五阶证明模块。
- [`Lean/Audit.lean`](Lean/Audit.lean)：公理审计。
