import L20261018.Ch2.Hensel.UnitsCupVanish.Step040_cocycle_on_quotient
import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# S53 R30：**N4 的类层收口** —— `res_I(kummerClass u) = 0`（`Hyp638`）

## 0 目标（`PROMPT-S53` §① 的 **B**，按侦察修正后的形态）

`Hyp632`–`Hyp637` 把 Kummer 余圈的**算术**全部机检，但一直停在 `F̄` 值函数的层面；
「把它搬进 `H¹`」（`LESSONS` D10 的最后一步）本轮完成。

**⚠ 侦察修正了 B 的形态**（见 `CH4-COVERAGE-AUDIT.md` §S53-R29 侦察命中）：
`H¹` 侧的 Kummer 机器**全在库**，本题**不需要自建 `Z¹`／`H¹`／restriction**：

| 库内件 | 位置（`raw/TauCeti`） | 作用 |
|---|---|---|
| `TauCeti.kummerCocycle` | `FieldTheory/GaloisCohomology/Kummer.lean:150` | **与我们 `Hyp632.kummerCocycle` 同一个对象** |
| `TauCeti.kummerCocycle_mem_Z1` | 同上 `:180` | 它是连续 `1`-余圈 |
| `TauCeti.kummerCocycleClass` | 同上 `:187` | 它在 `H¹(Γ_F, μ_p)` 里的类 |
| `TauCeti.kummerCocycle_eq_zero_iff` | 同上 `:174` | `c(σ) = 0 ↔ σ α = α` |
| `explicitRes1_mk` | `ContCohomology/ExplicitFunctoriality.lean:613` | **`res_I` 把类送到「限制后余圈」的类** |

⟹ 路线：**把我们的余圈认成库内的余圈**（`kummerCoeffCocycle_toMul_coe`），
于是 `mem_Z1`／类／`res_I` 全部**运输**而来；再消费 `Hyp631`（`σ ∈ I ⟹ σ α = α`）得「限制后余圈 ≡ 0」，
最后 `H1pi_eq_zero_iff`／`zero_mem` 收口。

## 1 本件交付（全机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| `unitBase` | `x : 𝒪[F]ˣ` 在基域里的像 `Fˣ` |
| `rootUnit` | `α ∈ F̄` 作为 `(F̄)ˣ`（用 `hα0 : α ≠ 0`） |
| `rootUnit_pow_eq` | `rootUnit^p = Units.map (algebraMap F F̄) (unitBase x)`（把 `hα` 换成库内形态） |
| **`kummerCoeffCocycle`** | ★★★★★ **库内余圈** `Γ_F → μ_p`（`= TauCeti.kummerCocycle`） |
| `kummerCoeffCocycle_toMul_coe` | ★★★★ **与 `Hyp632.kummerCocycle` 逐点一致**（`σ α / α`） |
| **`kummerCoeffCocycle_mem_Z1`** | ★★★★★ `∈ Z¹(Γ_F, μ_p)` |
| **`kummerCoeffCocycle_eq_zero_of_mem_inertia`** | ★★★★★ `σ ∈ I ⟹ c(σ) = 0` |
| **`kummerCoeffClass`** | ★★★★★ `H¹(Γ_F, μ_p)` 里的 Kummer 类 |
| **`kummerCoeffClass_res_eq_zero`** | ★★★★★★★ **N4 的类层收口**：`res_I(kummerClass u) = 0` |

## 2 数学

`α^p = x`（`x ∈ 𝒪[F]ˣ`）⟹ `σ ∈ I ⟹ σ α = α`（`Hyp631`）
⟹ 余圈在 `I` 上恒为 `0` ⟹ 限制后的余圈是零余圈 ⟹ 其类 `= 0`。

**没有新的算术**：本件的全部数学输入是 `Hyp631`，其余是库内运输。

## 3 诚实边界

* **载体仍是库内 `H1`**（`Z¹/B¹`）。战役主线的载体是 `GaloBase.V`（**规范** `continuousCohomology`），
  两者之间的桥（`explicitH1AddEquiv` 一族）**未做** ⟹ 本件**不**声称战役的 `hCI` 已解。
* **未做**：`explicitInfRes_exact` 一侧（`res = 0 ⟹ ∈ range infl`）——那是 `(CI)` 的**反向**装配。
* **未做**：`hLoc`（**C**）／`κ ↪ κ̄`（**D**）／N3 后半（**E**）。
* 不声称 `(CI)`；**不增覆盖率**（`(R2)` 仍 `∅-open`，**不得读作「否」**）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Setup

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- `x : 𝒪[F]ˣ` 映到基域 `F` 的单位群。 -/
noncomputable def unitBase (x : (↥𝒪[F])ˣ) : Fˣ :=
  Units.map (algebraMap ↥𝒪[F] F).toMonoidHom x

/-- `α ∈ F̄`（`α ≠ 0`）作为 `(F̄)ˣ` 的元素。 -/
noncomputable def rootUnit {α : SeparableClosure F} (hα0 : α ≠ 0) : (SeparableClosure F)ˣ :=
  Units.mk0 α hα0

@[simp] theorem unitBase_coe (x : (↥𝒪[F])ˣ) :
    ((unitBase x : Fˣ) : F) = ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]) := rfl

@[simp] theorem rootUnit_coe {α : SeparableClosure F} (hα0 : α ≠ 0) :
    ((rootUnit hα0 : (SeparableClosure F)ˣ) : SeparableClosure F) = α := rfl

/-- 把战役形态的 `α^p = x` 换成库内形态 `αᵘ^p = Units.map (algebraMap F F̄) xᵘ`。 -/
theorem rootUnit_pow_eq {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    rootUnit hα0 ^ p = Units.map (algebraMap F (SeparableClosure F)).toMonoidHom (unitBase x) := by
  refine Units.ext ?_
  show ((rootUnit hα0 : (SeparableClosure F)ˣ) : SeparableClosure F) ^ p
    = ((Units.map (algebraMap F (SeparableClosure F)).toMonoidHom (unitBase x) :
        (SeparableClosure F)ˣ) : SeparableClosure F)
  simp only [rootUnit_coe, Units.coe_map, MonoidHom.coe_coe, unitBase_coe]
  rw [hα]
  rfl

end Setup

section Cocycle

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★ **库内形态的 Kummer 余圈**：`Γ_F → μ_p`（`TauCeti.kummerCocycle` 的特化）。

它的值是 `Additive.ofMul ⟨σ • α * α⁻¹, _⟩`；`kummerCoeffCocycle_toMul_coe` 说其底值就是
`Hyp632.kummerCocycle`（即 `σ α / α`）。 -/
noncomputable def kummerCoeffCocycle {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    (SeparableClosure F ≃ₐ[F] SeparableClosure F) → TauCeti.KummerCoeff F p :=
  TauCeti.kummerCocycle (rootUnit_pow_eq hα0 hα)

/-- ★★★★ **与战役形态逐点一致**：库内余圈的底值就是 `σ α / α`（`Hyp632.kummerCocycle`）。 -/
theorem kummerCoeffCocycle_toMul_coe {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    (((kummerCoeffCocycle hα0 hα σ).toMul : (SeparableClosure F)ˣ) : SeparableClosure F)
      = kummerCocycle (F := F) (α := α) σ := by
  rw [kummerCoeffCocycle, TauCeti.toMul_kummerCocycle, AlgEquiv.smul_units_def]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
    rootUnit_coe, kummerCocycle_apply, div_eq_mul_inv]

/-- ★★★★★ **它是连续 `1`-余圈**（库内 `TauCeti.kummerCocycle_mem_Z1` 的直接特化）。 -/
theorem kummerCoeffCocycle_mem_Z1 {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    kummerCoeffCocycle hα0 hα
      ∈ Z1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p) :=
  TauCeti.kummerCocycle_mem_Z1 _

/-- ★★★★★ **`H¹(Γ_F, μ_p)` 里的 Kummer 类**。 -/
noncomputable def kummerCoeffClass {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    H1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p) :=
  TauCeti.kummerCocycleClass (rootUnit_pow_eq hα0 hα)

theorem kummerCoeffClass_def {p : ℕ} {x : (↥𝒪[F])ˣ} {α : SeparableClosure F}
    (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    kummerCoeffClass hα0 hα
      = H1pi (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p)
          ⟨kummerCoeffCocycle hα0 hα, kummerCoeffCocycle_mem_Z1 hα0 hα⟩ :=
  (rfl)

end Cocycle

/-! ## `I` 上恒为零 ＋ 类层收口 -/

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hO : ∀ x : SeparableClosure F,
    x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval hO in
/-- ★★★★★ **余圈在惯性群上恒为零**（库内形态）：`σ ∈ I ⟹ c(σ) = 0`。

消费 `Hyp631.inertia_fixes_pow_root_of_unit`（`σ α = α`）＋ 库内
`TauCeti.kummerCocycle_eq_zero_iff`（`c(σ) = 0 ↔ σ • α = α`）。 -/
theorem kummerCoeffCocycle_eq_zero_of_mem_inertia {p : ℕ} (hp : p ≠ 0)
    (hpun : IsUnit (p : ↥𝒪[F])) {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F]))
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    kummerCoeffCocycle hα0 hα σ = 0 := by
  rw [kummerCoeffCocycle, TauCeti.kummerCocycle_eq_zero_iff, AlgEquiv.smul_units_def]
  refine Units.ext ?_
  simp only [rootUnit_coe]
  exact inertia_fixes_pow_root_of_unit W hO hval hp hpun hα σ hσ

include hval hO in
/-- ★★★★★★★ **N4 的类层收口**：`res_I(kummerClass u) = 0`。

`res_I` 取库内 `explicitRes1`（`ContCohomology/ExplicitFunctoriality.lean:607`），
其类层计算 `explicitRes1_mk` 把「类」送到「限制后余圈」的类；
限制后的余圈由本件上一条恒为零 ⟹ 零余圈的类为 `0`。 -/
theorem kummerCoeffClass_res_eq_zero {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥𝒪[F]))
    {x : (↥𝒪[F])ˣ} {α : SeparableClosure F} (hα0 : α ≠ 0)
    (hα : α ^ p = (algebraMap ↥𝒪[F] (SeparableClosure F)) ((x : (↥𝒪[F])ˣ) : ↥𝒪[F])) :
    explicitRes1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p)
        (inertia W hval) (kummerCoeffClass hα0 hα) = 0 := by
  -- 限制后的余圈恒为零 ⟹ 它是零余圈
  have hz : (cocyclesMap1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p)
        ↥(inertia W hval) (TauCeti.KummerCoeff F p)
        (ContinuousMonoidHom.subgroupSubtype (inertia W hval)) (AddMonoidHom.id _)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul _ _)
        ⟨kummerCoeffCocycle hα0 hα, kummerCoeffCocycle_mem_Z1 hα0 hα⟩ :
        Z1 ↥(inertia W hval) (TauCeti.KummerCoeff F p)) = 0 := by
    refine Subtype.ext (funext fun t => ?_)
    rw [cocyclesMap1_apply]
    simp only [AddMonoidHom.id_apply, AddSubgroup.coe_zero, Pi.zero_apply]
    exact kummerCoeffCocycle_eq_zero_of_mem_inertia W hO hval hp hpun hα0 hα t t.2
  have hcls : kummerCoeffClass hα0 hα
      = ((⟨kummerCoeffCocycle hα0 hα, kummerCoeffCocycle_mem_Z1 hα0 hα⟩ :
          Z1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p)) :
        H1 (SeparableClosure F ≃ₐ[F] SeparableClosure F) (TauCeti.KummerCoeff F p)) := rfl
  rw [hcls, explicitRes1_mk, hz]
  simp

end Inertia

end L20261018

#print axioms L20261018.kummerCoeffCocycle
#print axioms L20261018.kummerCoeffCocycle_toMul_coe
#print axioms L20261018.kummerCoeffCocycle_mem_Z1
#print axioms L20261018.kummerCoeffClass
#print axioms L20261018.kummerCoeffCocycle_eq_zero_of_mem_inertia
#print axioms L20261018.kummerCoeffClass_res_eq_zero
