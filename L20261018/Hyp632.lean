import L20261018.Hyp631

/-!
# S52 R24：**N4 的余圈层** —— Kummer 余圈 `σ ↦ σα/α` 的三条基本性质

## 0 目标

R23 的 `Hyp631.inertia_fixes_pow_root_of_unit` 给的是**点值**结论 `σ α = α`（`σ ∈ I`）。
`(CI)` 需要的是**上同调类层**的陈述（`res_I (kummerClass u) = 0`）。中间隔着一层：
把 Kummer 类**显式写成余圈** `c_u(σ) := σα/α`（`α^p = u`）。本件把这一层的三条性质机检：

| 性质 | 数学 | 用途 |
|---|---|---|
| **余圈恒等式** | `c(στ) = c(σ) · σ(c(τ))` | 它是 `Z¹(Γ_F, F̄^×)` 的元素 |
| **值在 `μ_p` 里** | `c(σ)^p = 1` | 系数可降到 `μ_p` |
| **在 `I` 上平凡** | `σ ∈ I ⟹ c(σ) = 1` | ★ **N4 的余圈形态** |

## 1 数学（两行）

* `c(στ) = (στ)α/α = σ(τα)/α`，而 `c(σ)·σ(c(τ)) = (σα/α)·(σ(τα)/σα) = σ(τα)/α` ✓；
* `c(σ)^p = σ(α^p)/α^p = σ(u)/u = u/u = 1`（`σ` 固定 `F` 的元素）✓。

⟹ `c` 的余圈性是纯群论＋域运算，**不需要 `(CI)`、不需要 Hensel、不需要赋值**。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| `kummerCocycle` | `c(σ) := σ α / α` |
| **`kummerCocycle_mul`** | ★★★★ 余圈恒等式 |
| **`kummerCocycle_pow_eq_one`** | ★★★★ `c(σ)^p = 1` |
| **`kummerCocycle_div_self`** | `c(1) = 1`（余圈的单位元条件，顺带） |
| **`kummerCocycle_eq_one_of_mem_inertia`** | ★★★★★ **N4 余圈形态** |

## 3 诚实边界

* **未做**：`c_u` 与 `GaloBase.V`／`ResH1` 层 `kummerClass` 的**载体等同**（`H¹ = Z¹/B¹` 的商），
  故**不声称**已证 `res_I(kummerClass u) = 0`；本件是其**唯一算术输入**。
* 本件**不动** `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Def

variable {F : Type} [Field F]

/-- **Kummer 余圈**：`c(σ) := σ α / α`（`α` 是 `F̄` 里的一个 `p` 次根）。 -/
noncomputable def kummerCocycle {α : SeparableClosure F}
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) : SeparableClosure F :=
  σ α / α

@[simp] theorem kummerCocycle_apply {α : SeparableClosure F}
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerCocycle (F := F) (α := α) σ = σ α / α := rfl

/-- ★★★★ **余圈恒等式**：`c(στ) = c(σ) · σ(c(τ))`。 -/
theorem kummerCocycle_mul {α : SeparableClosure F} (hα0 : α ≠ 0)
    (σ τ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerCocycle (F := F) (α := α) (σ * τ)
      = kummerCocycle (F := F) (α := α) σ
        * σ (kummerCocycle (F := F) (α := α) τ) := by
  have hσα : σ α ≠ 0 := fun h => hα0 (σ.injective (by simpa using h))
  have hmul : (σ * τ) α = σ (τ α) := rfl
  have hdiv : σ (τ α / α) = σ (τ α) / σ α := map_div₀ σ (τ α) α
  simp only [kummerCocycle_apply, hmul, hdiv]
  field_simp

/-- ★★★★ **值在 `μ_p` 里**：`α^p = u`（`u ∈ F`）⟹ `c(σ)^p = 1`。 -/
theorem kummerCocycle_pow_eq_one {p : ℕ} {α : SeparableClosure F} (hα0 : α ≠ 0) {u : F}
    (hα : α ^ p = algebraMap F (SeparableClosure F) u)
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    (kummerCocycle (F := F) (α := α) σ) ^ p = 1 := by
  have hu0 : (algebraMap F (SeparableClosure F)) u ≠ 0 := by
    rw [← hα]
    exact pow_ne_zero p hα0
  have hcomm : σ ((algebraMap F (SeparableClosure F)) u) = (algebraMap F (SeparableClosure F)) u :=
    AlgEquiv.commutes σ u
  simp only [kummerCocycle_apply]
  rw [div_pow, ← map_pow, hα, hcomm, div_self hu0]

/-- 余圈在单位元处取值 `1`（余圈的单位元条件）。 -/
theorem kummerCocycle_one {α : SeparableClosure F} (hα0 : α ≠ 0) :
    kummerCocycle (F := F) (α := α) (1 : SeparableClosure F ≃ₐ[F] SeparableClosure F) = 1 := by
  simp only [kummerCocycle_apply, AlgEquiv.one_apply, div_self hα0]

end Def

section VanishingOnInertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★ **N4 的余圈形态**：`σ ∈ I ⟹ c(σ) = 1`（`α^p = x`，`x ∈ 𝒪[F]ˣ`）。

这条就是「`c_u` 在惯性群上平凡」的**完整可机检陈述**；下一步只需把它搬进 `H¹(I, μ_p)`。 -/
theorem kummerCocycle_eq_one_of_mem_inertia {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    kummerCocycle (F := F) (α := α) σ = 1 := by
  have hfix : σ α = α :=
    inertia_fixes_pow_root_of_unit W hO hval hp hpun hα σ hσ
  simp only [kummerCocycle_apply, hfix, div_self hα0]

end VanishingOnInertia

end L20261018

#print axioms L20261018.kummerCocycle_mul
#print axioms L20261018.kummerCocycle_pow_eq_one
#print axioms L20261018.kummerCocycle_one
#print axioms L20261018.kummerCocycle_eq_one_of_mem_inertia
