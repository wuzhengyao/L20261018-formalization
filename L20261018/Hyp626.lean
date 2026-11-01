import Hyp625

/-!
# S51 R19：**剩余作用的良定义性** —— `Γ_F` 在 `κ̄ = 𝒪_W/𝔪_W` 上的作用是**构造出来的**

## 0 目标

`hyp-residue-galois` 的 `φ : Γ_F → Γ_κ` 一直是**假设**。本线要让 `φ` **由 `W` 导出**。
第一步：证明「`σ ∈ Γ_F` 在 `κ̄` 上的作用**良定义**」——
即 `residue x = residue y ⟹ residue (σ x) = residue (σ y)`。

## 1 数学（三行）

`residue x = residue y`
⟹ `x − y ∈ 𝔪_W`  （`residue_eq_zero_iff`）
⟹ `W (x − y) < 1`  （`Valuation.mem_maximalIdeal_iff`）
⟹ `W (σ x − σ y) = W (σ (x − y)) = W (x − y) < 1`  （**值保持 `hval`**）
⟹ `σ x − σ y ∈ 𝔪_W` ⟹ `residue (σ x) = residue (σ y)`。

**`hval` 第四次成为唯一实质输入。**

## 2 本件交付

| 声明 | 内容 |
|---|---|
| **`residue_action_welldef`** | ★★★★★★ `σ` 在 `κ̄` 上的作用**良定义** |
| ~~`residue_action_mul`~~ | **本轮未做**：没有把作用写成**函数**（只有良定义），故无从叙复合；下一轮升级为 `Γ_F →* MulAut κ̄` |

## 3 诚实边界

* 仍**不证** `(CI)`；`FbarValuationHyp₄` 仍是假设。
* **未做**：把良定义升级为 `κ̄ ≃+* κ̄` 的 `MonoidHom`（`Γ_F →* MulAut κ̄`）——下一轮。
  **本件只有良定义**，没有把作用写成函数，故**不声称**复合相容。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section ResidueAction

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval in
/-- ★★★★★★ **剩余作用良定义**：`residue x = residue y ⟹ residue (σ x) = residue (σ y)`。 -/
theorem residue_action_welldef (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F)
    (x y : ↥W.valuationSubring)
    (h : IsLocalRing.residue ↥W.valuationSubring x
      = IsLocalRing.residue ↥W.valuationSubring y) :
    IsLocalRing.residue ↥W.valuationSubring
        ⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩
      = IsLocalRing.residue ↥W.valuationSubring
        ⟨σ (y : SeparableClosure F), hstab_of_hval W hval σ y.2⟩ := by
  -- 1. `x − y ∈ 𝔪`
  have hzero : IsLocalRing.residue ↥W.valuationSubring (x - y) = 0 := by
    rw [map_sub, h, sub_self]
  have hmem : x - y ∈ IsLocalRing.maximalIdeal ↥W.valuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hzero
  -- 2. `W (x − y) < 1`
  have hW : W ((x : SeparableClosure F) - (y : SeparableClosure F)) < 1 := by
    have h' := hmem
    rw [Valuation.mem_maximalIdeal_iff] at h'
    convert h' using 2
  -- 3. 搬到 `σ` 之后（值保持）
  have hW' : W (σ (x : SeparableClosure F) - σ (y : SeparableClosure F)) < 1 := by
    rw [← map_sub, hval]
    exact hW
  -- 4. `σ x − σ y ∈ 𝔪`
  have hmem' : (⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩
      - ⟨σ (y : SeparableClosure F), hstab_of_hval W hval σ y.2⟩)
      ∈ IsLocalRing.maximalIdeal ↥W.valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    convert hW' using 2
  -- 5. 收口
  have hzero' : IsLocalRing.residue ↥W.valuationSubring
      (⟨σ (x : SeparableClosure F), hstab_of_hval W hval σ x.2⟩
        - ⟨σ (y : SeparableClosure F), hstab_of_hval W hval σ y.2⟩) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem'
  rw [map_sub, sub_eq_zero] at hzero'
  exact hzero'

end ResidueAction

end L20261018

#print axioms L20261018.residue_action_welldef
