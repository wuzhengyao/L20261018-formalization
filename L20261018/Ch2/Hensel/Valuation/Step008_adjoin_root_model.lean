import L20261018.Ch2.Hensel.Valuation.Step007_integer_clear_denominators
import Mathlib.FieldTheory.KummerExtension

/-!
# R1024（路径 A · **A1′·2·b·iii 的地基**）：把 `L` 取成 `AdjoinRoot (X^p − π)` 模型

A1′·2 余下的核心是**范数残差** `N(y) ≡ a₀^p (mod s)`。它的 Lean 成本主要在「`L/F` 的基」与
「乘性矩阵」两处。本轮判定：**把 `L` 特化为 `AdjoinRoot (X^p − C π)`**（`F` 上），则两处都现成：

* 基：`AdjoinRoot.powerBasis (h : f ≠ 0) : PowerBasis F (AdjoinRoot f)`，
  `PowerBasis.basis` 给 `1, X, …, X^{p−1}`；
* 范数：mathlib 的 `norm_root_X_pow_sub_C` 直接给 `N(root) = (−1)^p·(−π)`。

本文件机检该模型上的两条地基事实：

| 声明 | 内容 |
|---|---|
| **`norm_root_uniformizer_adjoinRoot`** | **`Algebra.norm F (root (X^p − C π)) = π`**（`p` 奇） |
| `finrank_adjoinRoot_uniformizer` | `Module.finrank F (AdjoinRoot (X^p − C π)) = p` |

> **范围决策（本轮）**：A1′·2 从此在 `AdjoinRoot` 模型上做（`PLAN-A` §1 的 A1′·2·b·iii）。
> 论文的 `L = F(π^{1/p})` 与该模型只差一个 `F`-代数同构；范数群在 `F`-代数同构下不变
> （`Algebra.norm_eq_of_algEquiv`），把这一不变量形式化是 A2 收口时的最后一步。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section AdjoinRootModel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **一致化元的范数**：在模型 `L = F[X]/(X^p − π)` 上，`N(s) = π`（`p` 奇）。 -/
theorem norm_root_uniformizer_adjoinRoot (hp2 : p ≠ 2) (π : Fˣ) :
    Algebra.norm F (AdjoinRoot.root (X ^ p - C (π : F))) = (π : F) := by
  rw [norm_root_X_pow_sub_C (Fact.out : p.Prime).ne_zero]
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rw [hodd.neg_one_pow]
  ring

/-- **模型的次数**：`[F[X]/(X^p − π) : F] = p`。 -/
theorem finrank_adjoinRoot_uniformizer (π : Fˣ) :
    Module.finrank F (AdjoinRoot (X ^ p - C (π : F))) = p := by
  have hne : (X ^ p - C (π : F)) ≠ 0 := by
    intro h
    have hdeg := congrArg (fun f : F[X] => f.natDegree) h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at hdeg
    exact (Fact.out : p.Prime).ne_zero hdeg
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis (K := F) (f := X ^ p - C (π : F)) hne),
    AdjoinRoot.powerBasis_dim hne, natDegree_X_pow_sub_C]

end AdjoinRootModel

end L20261018

#print axioms L20261018.norm_root_uniformizer_adjoinRoot
#print axioms L20261018.finrank_adjoinRoot_uniformizer
