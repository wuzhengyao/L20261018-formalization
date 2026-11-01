import L20261018.Ch2.Hensel.UnitsCupVanish.Step033_inertia_fixed_unit_pth_root

/-!
# S52 R23：**N4 的论文形态** —— `u ∈ 𝒪[F]ˣ` 时的算术核心（两条假设全部导出）

## 0 目标

R22 的 `Hyp630.inertia_fixes_pow_root` 仍带两个**未导出**的假设：

```lean
(hu   : W (algebraMap F F̄ u) = 1)            -- u 是赋值单位
(hpun : IsUnit (p : ↥W.valuationSubring))     -- p 在 𝒪_W 里可逆
```

本件在 **`FbarValuationHyp₄` 的 `𝒪_W = 𝒪bar`**（`Hyp623`，本件以它的形态
`hO : ∀ x, x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] F̄` 传入）与 **`IsUnit (p : ↥𝒪[F])`**
之下把这两条**导出**，得到 **N4 的论文形态**：

```
x : 𝒪[F]ˣ（论文的 u）＋ α^p = x ＋ σ ∈ I   ⟹   σ α = α
```

## 1 数学（两条导出）

**(甲) `W (algebraMap x) = 1`**：`x` 与 `x⁻¹` 的像**都落在整闭包**（`isIntegral_algebraMap`）
⟹ 由 `hO` 都在 `𝒪_W` ⟹ `W y ≤ 1` 且 `W y⁻¹ = (W y)⁻¹ ≤ 1` ⟹ `W y = 1`
（`WithZero (Multiplicative ℚ)` 里 `≤ 1` 且 `⁻¹ ≤ 1` 逼出 `= 1`）。

**(乙) `IsUnit (p : ↥𝒪_W)`**：`p` 在 `↥𝒪[F]` 里可逆（`u` 为其逆）⟹ 像 `algebraMap u` 是 `F̄` 里的逆
⟹ `⟨p,_⟩ * ⟨algebraMap u,_⟩ = 1` 在 `↥𝒪_W` 里成立（两边都在 `𝒪_W`）⟹ `⟨p,_⟩` 是单位。
**注意**：不需要 `p ≠ 0` 的额外论证——`Units.mk` 显式构造只用乘积等式。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| `val_eq_one_of_inv_mem` | 辅助：`y ≠ 0`、`y, y⁻¹ ∈ 𝒪_W` ⟹ `W y = 1` |
| `isUnit_mk_of_inv_mem` | 辅助：同上 ⟹ `⟨y, _⟩` 是 `↥𝒪_W` 的单位 |
| `algebraMap_mem_integralClosure` | `x : ↥𝒪[F]` 的像在整闭包里 |
| **`val_algMap_eq_one`** | ★★★★★ **(甲)** |
| **`isUnit_algebraMap_of_isUnit`** | ★★★★★ **(乙)** |
| **`inertia_fixes_pow_root_of_unit`** | ★★★★★★★ **N4 论文形态** |

## 3 诚实边界

* **Kummer 类层仍未做**（`res_I(kummerClass u) = 0`）：本件停在点值层 `σ α = α`。
* `FbarValuationHyp₄`／`IsUnit (p : ↥𝒪[F])` 仍是假设；`(CI)` 未动；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Helpers

variable {F : Type} [Field F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))

/-- 辅助：`y ≠ 0`、`y` 与 `y⁻¹` 都在 `𝒪_W` 里 ⟹ `W y = 1`。 -/
theorem val_eq_one_of_inv_mem {y : SeparableClosure F} (hyne : y ≠ 0)
    (hy : y ∈ W.valuationSubring) (hyi : y⁻¹ ∈ W.valuationSubring) : W y = 1 := by
  have h1 : W y ≤ 1 := (Valuation.mem_valuationSubring_iff W y).mp hy
  have h2 : W y⁻¹ ≤ 1 := (Valuation.mem_valuationSubring_iff W y⁻¹).mp hyi
  rcases lt_or_eq_of_le h1 with hlt | heq
  · have hne : W y ≠ 0 := (Valuation.ne_zero_iff W).mpr hyne
    have hpos : (0 : WithZero (Multiplicative ℚ)) < W y := lt_of_le_of_ne zero_le (Ne.symm hne)
    have hgt : 1 < W y⁻¹ := by
      rw [map_inv₀]
      exact one_lt_inv_iff₀.mpr ⟨hpos, hlt⟩
    exact absurd h2 (not_le.mpr hgt)
  · exact heq

/-- 辅助：`y ≠ 0`、`y` 与 `y⁻¹` 都在 `𝒪_W` 里 ⟹ `⟨y, _⟩` 是 `↥𝒪_W` 的单位。 -/
theorem isUnit_mk_of_inv_mem {y : SeparableClosure F} (hyne : y ≠ 0)
    (hy : y ∈ W.valuationSubring) (hyi : y⁻¹ ∈ W.valuationSubring) :
    IsUnit (⟨y, hy⟩ : ↥W.valuationSubring) := by
  refine ⟨⟨⟨y, hy⟩, ⟨y⁻¹, hyi⟩, ?_, ?_⟩, rfl⟩
  · refine Subtype.ext ?_
    show y * y⁻¹ = (1 : SeparableClosure F)
    exact mul_inv_cancel₀ hyne
  · refine Subtype.ext ?_
    show y⁻¹ * y = (1 : SeparableClosure F)
    exact inv_mul_cancel₀ hyne

end Helpers

section Derive

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))

/-- `x : ↥𝒪[F]` 在 `F̄` 中的像属于 `integralClosure ↥𝒪[F] F̄`。 -/
theorem algebraMap_mem_integralClosure (x : ↥𝒪[F]) :
    (algebraMap ↥𝒪[F] (SeparableClosure F)) x ∈ integralClosure ↥𝒪[F] (SeparableClosure F) :=
  (mem_integralClosure_iff ↥𝒪[F] (SeparableClosure F)).mpr isIntegral_algebraMap

include hO in
/-- ★★★★★ **（甲）**：`x` 是 `𝒪[F]` 的单位 ⟹ `W (algebraMap x) = 1`。 -/
theorem val_algMap_eq_one (x : (↥𝒪[F])ˣ) :
    W ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) = 1 := by
  have hmul : ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
      * ((algebraMap ↥𝒪[F] (SeparableClosure F)) (((x⁻¹ : (↥𝒪[F])ˣ)) : ↥𝒪[F])) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hy : ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
      ∈ W.valuationSubring :=
    (hO _).mpr (algebraMap_mem_integralClosure ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
  have hyi : ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))⁻¹
      ∈ W.valuationSubring := by
    have heq : ((algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))⁻¹
        = ((algebraMap ↥𝒪[F] (SeparableClosure F)) (((x⁻¹ : (↥𝒪[F])ˣ)) : ↥𝒪[F])) :=
      (eq_inv_of_mul_eq_one_right hmul).symm
    rw [heq]
    exact (hO _).mpr (algebraMap_mem_integralClosure (((x⁻¹ : (↥𝒪[F])ˣ)) : ↥𝒪[F]))
  exact val_eq_one_of_inv_mem W hne hy hyi

include hO in
/-- ★★★★★ **（乙）**：`p` 在 `↥𝒪[F]` 里可逆 ⟹ `⟨p, _⟩` 在 `↥𝒪_W` 里可逆。 -/
theorem isUnit_algebraMap_of_isUnit {p : ℕ} (hpun : IsUnit (p : ↥𝒪[F])) :
    IsUnit (⟨((p : ℕ) : SeparableClosure F), (hO _).mpr (by
      rw [show ((p : ℕ) : SeparableClosure F)
        = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((p : ℕ) : ↥𝒪[F]) from (map_natCast _ p).symm]
      exact algebraMap_mem_integralClosure _)⟩ : ↥W.valuationSubring) := by
  obtain ⟨u, hu⟩ := hpun
  -- 关键：`y := (p : F̄)`、`y' := algebraMap (u⁻¹)`，且 `y * y' = 1`
  have hconv : ((p : ℕ) : SeparableClosure F)
      = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((p : ℕ) : ↥𝒪[F]) := (map_natCast _ p).symm
  have hprod : ((p : ℕ) : SeparableClosure F)
      * (algebraMap ↥𝒪[F] (SeparableClosure F)) (((u⁻¹ : (↥𝒪[F])ˣ)) : ↥𝒪[F]) = 1 := by
    rw [hconv, ← hu, ← map_mul, Units.mul_inv, map_one]
  have hyne : ((p : ℕ) : SeparableClosure F) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hy : ((p : ℕ) : SeparableClosure F) ∈ W.valuationSubring :=
    (hO _).mpr (by rw [hconv]; exact algebraMap_mem_integralClosure _)
  have hy' : (((p : ℕ) : SeparableClosure F))⁻¹ ∈ W.valuationSubring := by
    have h : (((p : ℕ) : SeparableClosure F))⁻¹
        = (algebraMap ↥𝒪[F] (SeparableClosure F)) (((u⁻¹ : (↥𝒪[F])ˣ)) : ↥𝒪[F]) :=
      (eq_inv_of_mul_eq_one_right hprod).symm
    rw [h]
    exact (hO _).mpr (algebraMap_mem_integralClosure _)
  exact isUnit_mk_of_inv_mem W hyne hy hy'

end Derive

/-! ### 三、N4 的**论文形态** -/

section PaperForm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★★★ **N4 的论文形态**：`x : 𝒪[F]ˣ`（论文的 `u`）、`α^p = x`、`σ ∈ I` ⟹ `σ α = α`。

两条原本的假设（`W u = 1` 与 `IsUnit (p : ↥𝒪_W)`）现在**由 `hO` ＋ `IsUnit (p : ↥𝒪[F])` 导出**。 -/
theorem inertia_fixes_pow_root_of_unit {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    σ α = α := by
  have hα' : α ^ p = (algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F) := by
    rw [hα]
    rfl
  have hu' : W ((algebraMap F (SeparableClosure F)) (((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) : F)) = 1 :=
    val_algMap_eq_one W hO x
  exact inertia_fixes_pow_root W hval hp (isUnit_algebraMap_of_isUnit W hO hpun) hα' hu' σ hσ

end PaperForm

end L20261018

#print axioms L20261018.val_eq_one_of_inv_mem
#print axioms L20261018.isUnit_mk_of_inv_mem
#print axioms L20261018.val_algMap_eq_one
#print axioms L20261018.isUnit_algebraMap_of_isUnit
#print axioms L20261018.inertia_fixes_pow_root_of_unit
