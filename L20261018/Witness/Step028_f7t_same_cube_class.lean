import L20261018.Witness.Step027_f7t_unit_cube_from_residue

/-!
# R1269（S36 C 项 末步之三）：同剩余 ⟹ 同立方类（`Fˣ/(Fˣ)³` 中）

`HANDOFF` §S36 计划**(H-A)** 在 `Fˣ` 层的核心：`𝒪` 的两个单位若剩余类相同，
则它们在 `Fˣ/(Fˣ)³` 中同类 —— 因为 `u v⁻¹` 的剩余类为 `1`，由 `Hyp357.isCube_of_residue_one`
它是立方。

| 声明 | 内容 |
|---|---|
| **`finite_residueUnits`** | `Finite 𝓀[𝔽₇((t))]ˣ`（由 `Hyp352.finite_residueField`） |
| **`unitsResidue_surjective`** | `↥𝒪ˣ ↠ 𝓀ˣ`（`IsLocalRing.residue_surjective` ＋ 非 `𝔪` ⟹ 单位） |
| **`powerClass_eq_of_unitsResidue_eq`** | ★★★★★ 同剩余 ⟹ `unitsToF u` 与 `unitsToF v` 在 `Fˣ/(Fˣ)³` 中同类 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LaurentSeries ValuativeRel IsLocalRing Polynomial
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 局部记号：`↥𝒪[𝔽₇((t))]` 的极大理想。 -/
noncomputable abbrev mF'' : Ideal ↥𝒪[LaurentSeries (ZMod 7)] := IsLocalRing.maximalIdeal _

/-- ★★★★ **剩余域的单位群有限**。 -/
instance finite_residueUnits :
    Finite (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ :=
  Finite.of_injective
    (fun c : (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ =>
      (c : IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)]))
    (fun _ _ hab => Units.ext hab)

/-- ★★★★ **`↥𝒪ˣ ↠ 𝓀ˣ` 满射**（剩余映射满射，且剩余非零的元素是单位）。 -/
theorem unitsResidue_surjective : Function.Surjective (unitsResidue) := by
  intro c
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := ↥𝒪[LaurentSeries (ZMod 7)])
    (c : IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])
  have hx0 : x ∉ mF'' := by
    intro hmem
    have hzero : IsLocalRing.residue ↥𝒪[LaurentSeries (ZMod 7)] x = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      exact hmem
    rw [hx] at hzero
    exact c.ne_zero hzero
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hx0
  refine ⟨u, ?_⟩
  ext
  change IsLocalRing.residue ↥𝒪[LaurentSeries (ZMod 7)] (u : ↥𝒪[LaurentSeries (ZMod 7)])
    = (c : IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])
  rw [hu]
  exact hx

/-- ★★★★★ **同剩余 ⟹ 同立方类**（`Fˣ/(Fˣ)³` 中）。

`residue u = residue v` ⟹ `residue (u v⁻¹) = 1` ⟹ 由 `Hyp357.isCube_of_residue_one`
有 `c³ = unitsToF (u v⁻¹) = unitsToF u · (unitsToF v)⁻¹`，
故 `(c⁻¹)³ = (unitsToF u)⁻¹ · unitsToF v`，即两个类相差一个立方。 -/
theorem powerClass_eq_of_unitsResidue_eq (u v : (↥𝒪[LaurentSeries (ZMod 7)])ˣ)
    (h : unitsResidue u = unitsResidue v) :
    (QuotientGroup.mk (unitsToF u) :
        TauCeti.powerClassQuotient (LaurentSeries (ZMod 7))ˣ 3)
      = QuotientGroup.mk (unitsToF v) := by
  rw [QuotientGroup.eq, TauCeti.mem_powerSubgroup_iff]
  have h1 : unitsResidue (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, h]
    simp
  obtain ⟨c, hc⟩ := isCube_of_residue_one (u * v⁻¹) h1
  have hmul : unitsToF (u * v⁻¹) = unitsToF u * (unitsToF v)⁻¹ := by
    rw [map_mul, map_inv]
  refine ⟨c⁻¹, ?_⟩
  rw [inv_pow, hc, hmul, mul_inv_rev, inv_inv]
  exact mul_comm (unitsToF v) _

end FqXt
end L20261018

#print axioms L20261018.FqXt.unitsResidue_surjective
#print axioms L20261018.FqXt.powerClass_eq_of_unitsResidue_eq
