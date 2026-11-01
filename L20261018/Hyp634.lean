import L20261018.Hyp633

/-!
# S52 R26：**`c_u` 的单位层形态** —— Kummer 余圈取值在 `↥𝒪_Wˣ` 里

## 0 目标

R24 的 `Hyp632.kummerCocycle` 取值在 `F̄`（一个**域**）。要把 `μ_p ↪ κ̄^×`（`Hyp613`）接进来，
必须把余圈**降到 `𝒪_W` 的单位群**：

```
c_u(σ) = σα/α  ∈  ↥𝒪_Wˣ        （W c = W(σα)/W(α) = 1）
```

本件把这件事机检，并给出单位层的三条性质。

## 1 数学（两行）

* `α^p = x`（`x ∈ 𝒪[F]ˣ`）⟹ `W α = 1`（`Hyp631` 的 `val_algMap_eq_one`）；
* 故 `W (σ α / α) = W (σ α) / W α = W α / W α = 1`（**值保持** `hval`），
  同理 `W ((σ α / α)⁻¹) = 1` ⟹ `σ α / α` 与它的逆都在 `𝒪_W` ⟹ 是 `𝒪_W` 的单位。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`kummerUnit`** | ★★★★★ **余圈的单位层形态** `c_u(σ) : ↥𝒪_Wˣ` |
| `kummerUnit_coe` | `((c_u σ : ↥𝒪_W) : F̄) = σ α / α`（`rfl`） |
| **`kummerUnit_pow_eq_one`** | ★★★★ `c_u(σ)^p = 1` |
| **`kummerUnit_eq_one_of_mem_inertia`** | ★★★★★ **单位层的 N4**：`σ ∈ I ⟹ c_u(σ) = 1` |

## 3 诚实边界

* **未做**：把 `kummerUnit` 送进 `H¹(I, μ_p)`（商层／restriction）——那是 N4 的**最后一步**。
* **未做**：`κ ↪ κ̄` 的 `hLoc`（R25 登记）与 N3 后半。
* 本件**不动** `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section KummerUnit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★ **余圈的单位层形态**：`c_u(σ) = σα/α ∈ ↥𝒪_Wˣ`。

前提：`α^p = x`（`x : 𝒪[F]ˣ`）与 `α ≠ 0`。 -/
noncomputable def kummerUnit {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ}
    {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) : (↥W.valuationSubring)ˣ := by
  classical
  have hαF : α ^ p = (algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F) := by
    rw [hα]
    rfl
  have huF : W ((algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F)) = 1 :=
    val_algMap_eq_one W hO x
  have hWα : W α = 1 := val_root_eq_one W hp hαF huF
  have hWσα : W (σ α) = W α := hval σ α
  have hdiv : W (σ α / α) = 1 := by
    rw [map_div₀, hWσα, hWα, div_self]
    exact one_ne_zero
  have hdivinv : W ((σ α / α))⁻¹ = 1 := by
    rw [map_inv₀, hdiv]
    simp
  have hne : σ α / α ≠ 0 := by
    intro h
    rw [h, map_zero] at hdiv
    exact zero_ne_one hdiv
  have hmem : (σ α / α) ∈ W.valuationSubring :=
    (Valuation.mem_valuationSubring_iff W _).mpr (by rw [hdiv])
  have hmem' : ((σ α / α))⁻¹ ∈ W.valuationSubring :=
    (Valuation.mem_valuationSubring_iff W _).mpr (by rw [hdivinv])
  exact ⟨⟨σ α / α, hmem⟩, ⟨((σ α / α))⁻¹, hmem'⟩,
    by refine Subtype.ext ?_; show σ α / α * (σ α / α)⁻¹ = 1; exact mul_inv_cancel₀ hne,
    by refine Subtype.ext ?_; show (σ α / α)⁻¹ * (σ α / α) = 1; exact inv_mul_cancel₀ hne⟩

include hval hO in
@[simp] theorem kummerUnit_coe {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ}
    {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    ((kummerUnit W (hval := hval) (hO := hO) hp hpun hα0 hα σ : ↥W.valuationSubring) : SeparableClosure F)
      = σ α / α := rfl

include hval hO in
/-- ★★★★ **单位层的 `μ_p` 性**：`c_u(σ)^p = 1`。 -/
theorem kummerUnit_pow_eq_one {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ}
    {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    kummerUnit W (hval := hval) (hO := hO) hp hpun hα0 hα σ ^ p = 1 := by
  refine Units.ext ?_
  refine Subtype.ext ?_
  show (σ α / α) ^ p = ((1 : (↥W.valuationSubring)ˣ) : ↥W.valuationSubring)
  have h1 : ((1 : (↥W.valuationSubring)ˣ) : ↥W.valuationSubring) = 1 := rfl
  rw [h1]
  show (σ α / α) ^ p = (1 : SeparableClosure F)
  -- 用 `F̄` 层的余圈结果（`Hyp632`）：`hα` 在 `↥𝒪[F]` 层，先转成 `F` 层
  have hαF : α ^ p = (algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F) := by
    rw [hα]
    rfl
  exact kummerCocycle_pow_eq_one hα0 hαF σ

include hval hO in
/-- ★★★★★ **单位层的 N4**：`σ ∈ I ⟹ c_u(σ) = 1`。 -/
theorem kummerUnit_eq_one_of_mem_inertia {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    kummerUnit W (hval := hval) (hO := hO) hp hpun hα0 hα σ = 1 := by
  refine Units.ext ?_
  refine Subtype.ext ?_
  show σ α / α = ((1 : (↥W.valuationSubring)ˣ) : ↥W.valuationSubring)
  rw [show ((1 : (↥W.valuationSubring)ˣ) : ↥W.valuationSubring) = 1 from rfl]
  show σ α / α = (1 : SeparableClosure F)
  have h := kummerCocycle_eq_one_of_mem_inertia W hO hval hp hpun hα0 hα σ hσ
  simpa [kummerCocycle_apply] using h

end KummerUnit

end L20261018

#print axioms L20261018.kummerUnit
#print axioms L20261018.kummerUnit_coe
#print axioms L20261018.kummerUnit_pow_eq_one
#print axioms L20261018.kummerUnit_eq_one_of_mem_inertia
