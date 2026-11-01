import L20261018.Ch2.Hensel.UnitsCupVanish.Step038_cocycle_constant_on_cosets

/-!
# S52 R28：**余圈的下降 `Γ⧸I → F̄`**（`Hyp636`）—— 收 R27 登记的那一格

## 0 目标

R27 机检了「余圈在 `I` 的右陪集上恒定」，但 `Quotient.lift` 的下降**卡在关系转换**。
本件用 `QuotientGroup.leftRel_apply`（`(leftRel s) x y ↔ x⁻¹ * y ∈ s`）把它做掉：

```
c : Γ_F → F̄，c(τ * h) = c(τ) (h ∈ I)  ⟹  c 下降为  Γ_F ⧸ I → F̄
```

## 1 本件交付（全机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`kummerCocycleQuot`** | ★★★★★ **下降后的余圈** `Γ_F ⧸ I → F̄` |
| **`kummerCocycleQuot_mk`** | 取值公式 `kummerCocycleQuot (mk τ) = c(τ)` |

## 2 工艺（R27 卡点的正解）

`Quotient.lift` 的假设给的是 `a ≈ b`（`Setoid` 形态），**不是** defeq 于 `a⁻¹ * b ∈ I`；
用 **`QuotientGroup.leftRel_apply.mp`** 显式转换即可（`QuotientGroup.eq` 是另一条等价形态）。

## 3 诚实边界

* **未做**：下降后的余圈**仍是余圈**（商群上的余圈恒等式）＋值仍在 `μ_p`（`Hyp632` 的两条性质
  还没搬到商群层）；**未做**送进 `H¹(I, μ_p)`。
* 本件**不**声称 `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section QuotientDescent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★ **余圈的下降**：`Γ_F ⧸ I → F̄`。

依据：R27 的右陪集恒定 ＋ `Quotient.lift`（关系用 `QuotientGroup.leftRel_apply` 转换）。 -/
noncomputable def kummerCocycleQuot {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    (SeparableClosure F ≃ₐ[F] SeparableClosure F) ⧸ (inertia W hval) → SeparableClosure F :=
  Quotient.lift (fun τ => kummerCocycle (F := F) (α := α) τ) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ inertia W hval := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    rw [hb, kummerCocycle_mul_right_mem_inertia W hO hval hp hpun hα0 hα a (a⁻¹ * b) hab'])

end QuotientDescent

end L20261018

#print axioms L20261018.kummerCocycleQuot
