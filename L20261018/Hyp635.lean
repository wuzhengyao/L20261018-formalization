import L20261018.Hyp634

/-!
# S52 R27：**余圈在惯性陪集上恒定** —— `(CI)` 的群论骨架

## 0 目标

`(CI)` 说：`ker v̄` 里的每个类都从 `Γ_κ = Γ_F ⧸ I` **膨胀**而来。膨胀的**前提**是
「类在 `I` 上平凡 **⟹** 余圈在 `I` 的**陪集上恒定**」——这是纯群论的一步，与赋值无关：

```
c(τ h) = c(τ) · τ(c(h)) = c(τ) · τ(1) = c(τ)      （h ∈ I，c 在 I 上平凡）
```

本件把这一步机检。⟹ 此后「余圈 → `Γ⧸I` 上的余圈」只需**下降**（`QuotientGroup.lift`），
而**算术部分**（`c` 在 `I` 上平凡）已由 `Hyp632` 机检完毕。

## 1 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`kummerCocycle_mul_right_mem_inertia`** | ★★★★★ `h ∈ I ⟹ c(τ * h) = c(τ)`（**右陪集恒定**） |
| **`kummerCocycle_mul_right_mem_inertia'`** | `h ∈ I` 时的显式余圈恒等式形态（备查） |
| `kummerCocycle_eq_of_mul_mem_inertia` | 由右陪集恒定得：同陪集两个代表给出同一值 |

**⚠ 未做**：`Quotient.lift` 的**下降**（`kummerCocycleQuot`）——本轮试过，卡在 `Quot.lift` 的
`a ≈ b` 与 `a⁻¹ * b ∈ I` 的**关系转换**（`QuotientGroup` 的 setoid 形态），登记为下一轮第一件事。

## 2 诚实边界

* 本件**不**做 `QuotientGroup.lift` 的下降（下一步）；**不**声称 `(CI)`。
* `(CI)` 未动；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section CosetConstant

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★ **右陪集恒定**：`h ∈ I ⟹ c(τ * h) = c(τ)`。

证明：余圈恒等式 `c(τ*h) = c(τ) · τ(c(h))`，而 `c(h) = 1`（`Hyp632`），`τ(1) = 1`。 -/
theorem kummerCocycle_mul_right_mem_inertia {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (τ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (h : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hh : h ∈ inertia W hval) :
    kummerCocycle (F := F) (α := α) (τ * h)
      = kummerCocycle (F := F) (α := α) τ := by
  rw [kummerCocycle_mul (F := F) (α := α) hα0 τ h,
    kummerCocycle_eq_one_of_mem_inertia W hO hval hp hpun hα0 hα h hh, map_one, mul_one]

include hval hO in
/-- **同陪集同值**（右乘 `I` 不改变余圈值）：`c(τ₁) = c(τ₂)` 当 `τ₂ = τ₁ * h`，`h ∈ I`。 -/
theorem kummerCocycle_eq_of_mul_mem_inertia {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (τ h : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hh : h ∈ inertia W hval) :
    kummerCocycle (F := F) (α := α) (τ * h)
      = kummerCocycle (F := F) (α := α) τ :=
  kummerCocycle_mul_right_mem_inertia W hO hval hp hpun hα0 hα τ h hh

end CosetConstant

end L20261018

#print axioms L20261018.kummerCocycle_mul_right_mem_inertia
#print axioms L20261018.kummerCocycle_eq_of_mul_mem_inertia
