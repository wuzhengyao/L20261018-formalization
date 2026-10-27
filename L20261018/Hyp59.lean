import L20261018.Hyp58
/-!
# `(1b)` 第三阶段（一）：交叉积里的 `X = inc α`、`Y = u_σ` 与两条关系（**一般 $L$ 版**）

`(1b)` 的最后一步要在 `CP := CrossedProduct (carryCocycle b)` 里给出 `X = inc α`、`Y = u_σ`
并验证 `X^p = a`、`Y^p = b`、`YX = ζXY`，再用 `Hyp47.nonempty_algEquiv_of_finrank` 收口。

本文件按 `Hyp51`–`Hyp53` 的**通用 $L$** 写法给出这些对象与前两条关系（不需要 `AdjoinRoot` 模型
的实例链——只在最后代入 `L = K[p√a]`）：

* `X = inc α`，**`X ^ p = a`**（只需 `α ^ p = a`）；
* `Y = basis σ`，**`Y * X = ζ • (X * Y)`**（只需 `σ α = ζ • α`，用 TauCeti `basis_mul_inc`）。

`Y ^ p = b` 需要 carry 余环的乘积计算，见下一轮。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolCarryCocycle

open TauCeti

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- **`X = inc α`**。 -/
noncomputable def X (c : TwoCocycle K L) (α : L) : CrossedProduct c :=
  CrossedProduct.inc c α

/-- **`X ^ p = a`**（由 `α ^ p = a` 与 `inc` 是代数同态）。 -/
theorem X_pow (c : TwoCocycle K L) (α : L) {a : K} (hα : α ^ p = algebraMap K L a) :
    X c α ^ p = algebraMap K (CrossedProduct c) a := by
  rw [X, ← map_pow, hα, AlgHom.commutes]

/-- **`Y = u_σ`**（交叉积的标准基元素）。 -/
noncomputable def Y (c : TwoCocycle K L) (σ : L ≃ₐ[K] L) : CrossedProduct c :=
  CrossedProduct.basis c σ

/-- **`Y * X = ζ • (X * Y)`**（TauCeti 半线性规则 `basis_mul_inc` ＋ `σ α = ζ • α`）。 -/
theorem Y_mul_X (c : TwoCocycle K L) (σ : L ≃ₐ[K] L) (α : L) {ζ : K}
    (hσ : σ α = ζ • α) :
    Y c σ * X c α = ζ • (X c α * Y c σ) := by
  rw [Y, X, CrossedProduct.basis_mul_inc, hσ, map_smul, smul_mul_assoc]

/-- **`X` 与 `Y` 的半线性关系（未加 ζ 的原始形态）**。 -/
theorem Y_mul_X' (c : TwoCocycle K L) (σ : L ≃ₐ[K] L) (α : L) :
    Y c σ * X c α = X c (σ α) * Y c σ := by
  rw [Y, X, CrossedProduct.basis_mul_inc]
  rfl

end SymbolCarryCocycle
