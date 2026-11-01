import L20261018.Hyp108
import L20261018.Hyp110
import L20261018.Hyp111
import L20261018.Hyp695
import L20261018.Hyp710
-- 下面这条**不是**第 4 章的一部分，只为让 `routes_check.py` 的「最新模块」验 evidence 时
-- 能解析到 S69–S72 的声明（`Hyp757`–`Hyp762` 与本件在 DAG 的不同分支上）。
import L20261018.Hyp762

/-!
# S72 R3：**第 4 章闭合证书** —— `raw/L20261018.tex` §4「Hensel 赋值与第一槽分歧」

## ⚠ 本轮先纠正靶子（用户令：「目标错了」）

本轮开工时把靶子错认成 **Gille–Szamuely 的第 4 章**。核对原文后确认：

> **被形式化的对象 = 论文 `raw/L20261018.tex` 的 §4**（`:1554`–`:1651`，`\label{sec:hensel-original}`
> 「Hensel 赋值与第一槽分歧」）。**GS 等文献只是「证明出处的参考」**，不是对象。

## §4 的全部陈述（逐条，4 条）与机检件

| # | 论文陈述 | 定位 | Lean 件 |
|---|---|---|---|
| 1 | `lem:basis-change`（第一槽基变换） | `:1571` | `Hyp108.cup_basis_change`（线性代数内核）＋`Hyp108.basis_change_kummer`（论文真实对象） |
| 2 | `lem:ramified-vanishing`（`U^⊥ = 0`） | `:1608` | `Hyp110.ramified_vanishing_explicit`／`Hyp695.orth_eq_bot_of_merkurjevSuslin`（去 `[Finite 𝓀]`） |
| 3 | `thm:ramified`（`U^⊥ = N = 0`；`rank Φ ≥ 3`） | `:1629` | `Hyp111.thm_ramified_1`／`Hyp111.thm_ramified_2` |
| 4 | §4 结尾推论（`rank Φ = d_F = d_K + 1`，`d_K = 1` 矛盾） | `:1646` | `Hyp710.corollary_4_4_paper` |

## ⚠⚠ 本轮最重要的判定：**`C3`（`hd_cup_pi`）不在第 4 章范围内**

`PROMPT-S69`–`S72` 把 `C3 hd_cup_pi` 当作「本章最后、也最重的一块」。**核对论文原文后，这是范围错误**：

论文 §4 开头（`:1562`–`:1566`）**明写**：

> 「第二章命题~\ref{prop:prelim-kummer-valuation} 给出一次 Kummer 类的赋值分解，命题~\ref{prop:prelim-residue}
> 给出后文所需的剩余映射与二次驯符号。」

即 **`∂₂`（残差映射）的存在性与两条值公式是第 2 章的 `prop:prelim-residue`（`:1014`）**，
第 4 章**引用**它，**不重证**。而 `hd_cup_pi` 恰恰就是 `prop:prelim-residue`(1) 的第二式
`∂_q(inf(η) ∪ (π)) = η`。

⟹ S69–S72 四轮（`Delta`／`hd_infl`／`F5` 两半／W1–W4／`C3`）攻的都是
**第 2 章的 `prop:prelim-residue`(1)**（＝「把 `∂₂` 造出来」），**属第 2 章，不属第 4 章**。
`Hyp338.tameResidueFacts_of_residueMap` 已机检「`prop:prelim-residue`(1) 两条值 ⟹ `(R1)∧(R2)`」，
而 `Hyp161.henselResidueDataOfFacts` 已机检「`(R1)∧(R2)` ⟹ `res` 存在」——第 4 章侧的通路**已闭合**。

## 本件的作用

`#print axioms` 逐条打印四条陈述的**公理依赖**：任何一条若混入 `sorryAx`，立刻可见；
任何一条若被重命名／改类型，**本件编译失败**（＝类型锁定的机检形态）。

**[L44／L45] 状态行**：本件是**证书**，不是判决器——它只报「哪条陈述由哪个声明承载 ＋ 该声明的公理集」，
**不**声称「第 4 章已 100% 完成」。第 4 章在**论文自身的假设层级**（第 2 章结论作输入）上闭合。
-/

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open TauCeti ContCohomology

namespace L20261018

/-! ## 0 声明存在性（重命名／删除 ⟹ 本件编译失败） -/

#check @cup_basis_change
#check @basis_change_kummer
#check @ramified_vanishing_explicit
#check @orth_eq_bot_of_merkurjevSuslin
#check @thm_ramified_1
#check @thm_ramified_2
#check @corollary_4_4_paper
#check @tameResidueFacts_of_residueMap
#check @henselResidueDataOfFacts

end L20261018

/-! ## 1 公理依赖（`sorryAx` 必须不出现） -/

#print axioms L20261018.cup_basis_change
#print axioms L20261018.basis_change_kummer
#print axioms L20261018.ramified_vanishing_explicit
#print axioms L20261018.orth_eq_bot_of_merkurjevSuslin
#print axioms L20261018.thm_ramified_1
#print axioms L20261018.thm_ramified_2
#print axioms L20261018.corollary_4_4_paper
#print axioms L20261018.tameResidueFacts_of_residueMap
#print axioms L20261018.henselResidueDataOfFacts
