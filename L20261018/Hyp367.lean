import L20261018.Hyp366

/-!
# R1278（S36 C 项）：**论文 4.3(1) 在 `𝔽₇((t))`／`p = 3` 上机检成立**

照 `Hyp337`（`ℚ_[7]` 版）逐条搬，取 `Δ := ⊤`。两件非平凡输入已由 `Hyp365`／`Hyp366` 给出
（`hne43_F`／`hval43_F`）。

| 假设 | `𝔽₇((t))` 的供给 |
|---|---|
| `[(powMonoidHom 3).range.IsFiniteRelIndex ⊤]` | `finiteIndex_cubes_F`（由 `Hyp361` 的 `Finite (Fˣ/(Fˣ)³)`）＋ `relIndex_top_right` |
| `[FiniteDimensional F (Efield ⊤)]` | `Efield_top_eq_F` ＋ `TauCeti.finiteDimensional_kummerField` |
| `[IsGalois F (Efield ⊤)]` | `TauCeti.isAbelianGalois_kummerField` |
| `hU` | `IntermediateField.fixingSubgroup_isOpen` |
| `hroots` | `IsSepClosed.exists_pow_nat_eq` |
| `ha1`／`ha2` | `Subgroup.mem_top` |
| `hne`／`hval` | **`hne43_F`**／**`hval43_F`**（`Hyp366`） |
| `hp`／`hpF`／`hv`／`hπ`／`hp2` | `three_isUnit_O`／`three_isUnit_laurentSeries`／`valCompat_O`／`pi_hπ`／`by decide` |
| `[FiniteDimensional (ZMod p) (GaloBase.V F p)]` | `finiteDimensional_galoBaseV_F`（`Hyp362`） |

| 声明 | 内容 |
|---|---|
| `finiteIndex_cubes_F` | `(Fˣ)³` 有限指数 |
| `inst_finiteRelIndex_top_F` | `IsFiniteRelIndex ⊤` |
| `hroots_top_F` | 每元在可分闭包里有立方根 |
| `Efield_top_eq_F` | `Efield ⊤ = kummerField (SepCl) 3 ⊤` |
| `hU_F` | 固定子群开 |
| **`thm_ramified_1_F`** | ★★★★★★★ **4.3(1) 本身** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity (LaurentSeries (ZMod 7)) 3 :=
  hasEnoughRootsOfUnity_laurentSeries_zmod7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- 立方子群在 `𝔽₇((t))ˣ` 中指数有限（由 `Finite (Fˣ/(Fˣ)³)`）。 -/
instance finiteIndex_cubes_F :
    ((powMonoidHom 3 : (LaurentSeries (ZMod 7))ˣ →* (LaurentSeries (ZMod 7))ˣ).range).FiniteIndex := by
  rw [← TauCeti.powerSubgroup_eq_range_powMonoidHom]
  haveI := finite_powerClassQuotient
  refine ⟨?_⟩
  rw [Subgroup.index_eq_card]
  exact Nat.card_pos.ne'

end FqXt
end L20261018

#print axioms L20261018.FqXt.finiteIndex_cubes_F
