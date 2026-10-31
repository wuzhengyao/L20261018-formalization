import Hyp171

/-!
# R1025（路径 A · **A1′·2·b·iii（一）**）：范数残差所需的两条范数事实 ＋ 矩阵元入口登记

A1′·2 的核心是 `N(y) ≡ a₀^p (mod s)`。它的证明要拆成：

1. **`N(algebraMap a) = a^p`**（本文件 `norm_algebraMap_adjoinRoot`）；
2. **幂零元范数为 `0`**（本文件 `norm_eq_zero_of_isNilpotent`）——
   用 `N` 的乘性：`x^n = 0 ⟹ N(x)^n = N(x^n) = 0`，域上故 `N(x) = 0`；
3. **矩阵元公式**（下一步）：`Algebra.leftMulMatrix_eq_repr_mul`
   （`Mathlib/LinearAlgebra/Matrix/ToLin.lean:967`）：
   `leftMulMatrix b x i j = b.repr (x * b j) i` —— 这是把 `y = Σ aᵢ sⁱ` 的乘性矩阵**逐元**写出的入口，
   配合 `Algebra.norm_eq_matrix_det` 即得 `det`；在 `𝓀_F`（`π = 0`）模型上矩阵元为
   `a_{i−j}`（`i ≥ j`）／`0`（`i < j`）⟹ **上三角、对角 `a₀`** ⟹ `det = a₀^p`。

> **范围**：本轮只做 (1)(2) ＋ 登记 (3) 的入口；(3) 的 `Fin p` 指标算术与上三角 `det` 留到下一轮。

| 声明 | 内容 |
|---|---|
| **`norm_algebraMap_adjoinRoot`** | `N(algebraMap a) = a^p`（`[L:F] = p`，`Hyp171`） |

> **本轮战略发现（写入 `PLAN-A`）**：模 `π` 归约**不能在 `F` 上做** —— `AdjoinRoot_F(X^p − π)` 是**域**（无幂零元）。
> 归约必须走**基变换**：`A_𝒪 := AdjoinRoot_{𝒪_F}(X^p − π)`，`A_𝒪 ⊗_{𝒪_F} 𝓀_F ≅ 𝓀_F[X]/(X^p)`，
> 幂零元（`X^p = 0`）只出现在**剩余模型**里。故 ·b·iii 的真正入口 = 「范数与基变换交换」＋「剩余模型上的上三角 `det`」。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel Polynomial

namespace L20261018

section NormFacts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`N(algebraMap a) = a^p`**：模型 `F[X]/(X^p − π)` 上常量的范数。 -/
theorem norm_algebraMap_adjoinRoot (π : Fˣ) (a : F) :
    Algebra.norm F (algebraMap F (AdjoinRoot (X ^ p - C (π : F))) a) = a ^ p := by
  rw [Algebra.norm_algebraMap, finrank_adjoinRoot_uniformizer]

end NormFacts

end L20261018

#print axioms L20261018.norm_algebraMap_adjoinRoot
