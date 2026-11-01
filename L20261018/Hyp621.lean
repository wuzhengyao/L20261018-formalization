import Hyp620

/-!
# S51 R14：**`𝒪[F]` 在 `F̄` 中的整闭包是 `Γ_F`-稳定的**（无条件！）⟹ 延拓假设的三条锁降为一条

## 0 依据（逐字核实过的出版侧）

**Neukirch 1999, (6.2) Theorem**（Chapter II §6 *Henselian Fields*；PDF p.160 ↔ 印刷 p.144）：

> Let `K` be a henselian field with respect to the valuation `|·|`. Then `|·|` admits **one and only one**
> extension to any given algebraic extension `L|K`. It is given by `|α| = |N_{L|K}(α)|^{1/n}`, if `L|K`
> has finite degree `n`. **In any case, the valuation ring of the extended valuation is the integral
> closure of the valuation ring of `K` in `L`.**

关键在最后一句：`𝒪_W = integralClosure 𝒪[F] F̄`。
而 `𝒪[F] ⊆ F` 被 `Γ_F` **逐点固定**，整闭包在**自同构下不变** ⟹
**`σ(𝒪_W) = 𝒪_W` 是定义的直接后果，连 Hensel 都不需要。**

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`isIntegral_algEquiv`** | ★★★★ `x` 在 `𝒪[F]` 上整 ⟹ `σ x` 亦然（`σ ∈ Γ_F`） |
| **`mem_integralClosure_algEquiv`** | ★★★★★ 同上，`Subalgebra` 形态：`𝒪bar` 是 `Γ_F`-不变子代数 |
| **`FbarValuationHyp₃`** | ★★★★★★ 延拓假设的**单一条件**形态：`∃ W, 𝒪_W = 𝒪bar` |

## 2 为什么这比 `Hyp619.FbarValuationHyp₂` 强

`FbarValuationHyp₂` 的**第 3 条锁**（`Γ_F`-稳定性）是**自造假设**；
本件的 `mem_integralClosure_algEquiv` **无条件**证明同一件事（只要 `𝒪_W` 是整闭包）。
⟹ 三条件锁降为**一条**：`𝒪_W = 𝒪bar`，而那正是 Neukirch (6.2) 的**结论**。
**`Γ_F`-稳定性从此不再出现在任何假设里。**

## 3 诚实边界

* `FbarValuationHyp₃` 仍是**假设**：`F̄` 上赋值环恰为 `𝒪bar` 的赋值存在性（Neukirch (6.2) 的
  Hensel 前提 ＋ Bourbaki VI §8 Prop. 6 的构造）未在 Lean 内建。
* 本件**不**声称 `𝒪bar` 是赋值环（那是 (6.2) 的实质内容）。
* 本轮**不增覆盖率**；它是 `(CI) ⊆` 的第四个前置件。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section IntegralStable

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★ **`𝒪[F]` 上的整性被 `Γ_F` 保持**：`x` 在 `𝒪[F]` 上整 ⟹ `σ x` 亦然。 -/
theorem isIntegral_algEquiv (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    {x : SeparableClosure F} (h : IsIntegral ↥𝒪[F] x) :
    IsIntegral ↥𝒪[F] (σ x) :=
  IsIntegral.map (A := F) (f := (σ : SeparableClosure F →ₐ[F] SeparableClosure F)) h

/-- ★★★★★ **整闭包 `𝒪bar` 是 `Γ_F`-不变子代数**（Neukirch (6.2) 最后一句的直接后果）。 -/
theorem mem_integralClosure_algEquiv (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    {x : SeparableClosure F}
    (hx : x ∈ integralClosure ↥𝒪[F] (SeparableClosure F)) :
    σ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F) :=
  isIntegral_algEquiv σ hx

end IntegralStable

/-! ## 3 延拓假设的**单一条件**形态 -/

section SingleLock

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★★ **延拓假设（单条）**：存在 `F̄` 上的赋值 `W`，其**赋值环恰为 `𝒪[F]` 在 `F̄` 中的整闭包**。

依据 **Neukirch 1999, (6.2) Theorem**（逐字核实见
`scratch/lean-l20261018/BOURBAKI-ACVI-8-VALUATIONS.md` §6）：
Hensel 时延拓**唯一**，且「the valuation ring of the extended valuation **is the integral closure**
of the valuation ring of `K` in `L`」。

⟹ 原 `Hyp619.FbarValuationHyp₂` 的**第 3 条锁（`Γ_F`-稳定性）不再是假设**：
它有 ``mem_integralClosure_algEquiv`` 的**无条件**机器证明。 -/
def FbarValuationHyp₃ : Prop :=
  ∃ W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)),
    ∀ x : SeparableClosure F,
      x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F)

end SingleLock

end L20261018

#print axioms L20261018.isIntegral_algEquiv
#print axioms L20261018.mem_integralClosure_algEquiv
