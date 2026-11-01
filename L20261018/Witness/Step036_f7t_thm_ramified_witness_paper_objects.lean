import L20261018.Witness.Step035_f7t_thm_ramified_witness

/-!
# R1279（S36 C 项）：**论文 4.3(1) 在 `𝔽₇((t))`／`p = 3` 上机检成立**

照 `Hyp337`（`ℚ_[7]` 版）逐条搬，取 `Δ := ⊤`。非平凡输入由 `Hyp365`／`Hyp366` 给出
（`hne43_F`／`hval43_F`），载体维度由 `Hyp362` 给出，立方子群的有限指数由 `Hyp367` 给出。

| 声明 | 内容 |
|---|---|
| `inst_finiteRelIndex_top_F` | `[(powMonoidHom 3).range.IsFiniteRelIndex ⊤]`（字段 `relIndex_ne_zero` 显式给） |
| `hroots_top_F` | 每元在可分闭包里有立方根（`IsSepClosed.exists_pow_nat_eq`） |
| `Efield_top_eq_F` | `Efield ⊤ = kummerField (SepCl) 3 ⊤`（`fieldRange_val`） |
| `inst_finiteDimensional_Efield_top_F` | `[FiniteDimensional F (Efield ⊤)]`（`TauCeti.finiteDimensional_kummerField`） |
| `inst_isGalois_Efield_top_F` | `[IsGalois F (Efield ⊤)]`（`TauCeti.isAbelianGalois_kummerField`） |
| `hU_F` | 固定子群开（`fixingSubgroup_isOpen`） |
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

/-- `[(powMonoidHom 3).range.IsFiniteRelIndex ⊤]`（`Hyp337` 的同款，`FiniteIndex` 由 `Hyp367`）。 -/
instance inst_finiteRelIndex_top_F :
    ((powMonoidHom 3 : (LaurentSeries (ZMod 7))ˣ →* (LaurentSeries (ZMod 7))ˣ).range).IsFiniteRelIndex
      (⊤ : Subgroup (LaurentSeries (ZMod 7))ˣ) where
  relIndex_ne_zero := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero

/-- `Efield ⊤` 就是 `kummerField (SepCl) 3 ⊤`。 -/
theorem Efield_top_eq_F :
    Theo352.Efield (F := LaurentSeries (ZMod 7)) (p := 3) ⊤
      = TauCeti.kummerField (SeparableClosure (LaurentSeries (ZMod 7))) 3 ⊤ :=
  IntermediateField.fieldRange_val _

/-- `[FiniteDimensional F (Efield ⊤)]`（沿 `Efield_top_eq_F` 运输）。 -/
instance inst_finiteDimensional_Efield_top_F :
    FiniteDimensional (LaurentSeries (ZMod 7))
      ↥(Theo352.Efield (F := LaurentSeries (ZMod 7)) (p := 3) ⊤) := by
  haveI := inst_finiteRelIndex_top_F
  haveI : FiniteDimensional (LaurentSeries (ZMod 7))
      ↥(TauCeti.kummerField (SeparableClosure (LaurentSeries (ZMod 7))) 3 ⊤) :=
    TauCeti.finiteDimensional_kummerField (K := LaurentSeries (ZMod 7))
      (E := SeparableClosure (LaurentSeries (ZMod 7))) (n := 3) (Δ := ⊤)
  exact Module.Finite.equiv (IntermediateField.equivOfEq Efield_top_eq_F.symm).toLinearEquiv

/-- `[IsGalois F (Efield ⊤)]`（`TauCeti.isAbelianGalois_kummerField` 沿 `Efield_top_eq_F` 运输）。 -/
instance inst_isGalois_Efield_top_F :
    IsGalois (LaurentSeries (ZMod 7))
      ↥(Theo352.Efield (F := LaurentSeries (ZMod 7)) (p := 3) ⊤) := by
  haveI : IsAbelianGalois (LaurentSeries (ZMod 7))
      ↥(TauCeti.kummerField (SeparableClosure (LaurentSeries (ZMod 7))) 3 ⊤) :=
    TauCeti.isAbelianGalois_kummerField (K := LaurentSeries (ZMod 7))
      (E := SeparableClosure (LaurentSeries (ZMod 7))) (n := 3) (Δ := ⊤)
  exact IsGalois.of_algEquiv (IntermediateField.equivOfEq Efield_top_eq_F.symm)

/-- 每元在可分闭包里有立方根（`NeZero (3 : SepCl F)` 需显式给：`char F = 7` 使 `3 ≠ 0`）。 -/
theorem hroots_top_F :
    ∀ b ∈ (⊤ : Subgroup (LaurentSeries (ZMod 7))ˣ),
      ∃ x : SeparableClosure (LaurentSeries (ZMod 7)),
        x ^ 3 = algebraMap (LaurentSeries (ZMod 7)) (SeparableClosure (LaurentSeries (ZMod 7)))
          (b : LaurentSeries (ZMod 7)) := by
  intro b _
  haveI : NeZero (3 : SeparableClosure (LaurentSeries (ZMod 7))) :=
    ⟨fun h => three_ne_zero_laurentSeries
      ((algebraMap (LaurentSeries (ZMod 7))
          (SeparableClosure (LaurentSeries (ZMod 7)))).injective
        ((map_natCast (algebraMap (LaurentSeries (ZMod 7))
            (SeparableClosure (LaurentSeries (ZMod 7)))) 3).symm.trans
          (h.trans (map_zero _).symm)))⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap (LaurentSeries (ZMod 7)) (SeparableClosure (LaurentSeries (ZMod 7)))
      (b : LaurentSeries (ZMod 7))) 3
  exact ⟨x, hx⟩

/-- `hU`：`Efield ⊤` 的固定子群开。 -/
theorem hU_F :
    IsOpen ((Theo352.Efield (F := LaurentSeries (ZMod 7)) (p := 3) ⊤).fixingSubgroup
      : Set (TauCeti.AbsoluteGaloisGroup (LaurentSeries (ZMod 7)))) :=
  IntermediateField.fixingSubgroup_isOpen _

/-- ★★★★★★★ **论文 4.3(1) 在 `𝔽₇((t))`／`p = 3` 上成立**（`Δ := ⊤`）。 -/
-- @source file=raw/L20261018.tex locator=line:1636 quote="共同正交空间及范数像均消失，即 $U^\perp=N=0$；"
theorem thm_ramified_1_F :
    (Theo352.Bex (F := LaurentSeries (ZMod 7)) (p := 3) three_isUnit_laurentSeries hne43_F).Uperp = ⊥ ∧
      Theo352.Nsub (F := LaurentSeries (ZMod 7)) (p := 3)
        (⊤ : Subgroup (LaurentSeries (ZMod 7))ˣ) = ⊥ :=
  thm_ramified_1_noBridge (F := LaurentSeries (ZMod 7)) (p := 3)
    (v := vCompatHom) (π := pi) (ζ := zetaF) (a1 := twoUnitF) (a2 := pi)
    zetaF_spec three_isUnit_O three_isUnit_laurentSeries valCompat_O pi_hπ (by decide)
    (⊤ : Subgroup (LaurentSeries (ZMod 7))ˣ) hroots_top_F hU_F
    (Subgroup.mem_top twoUnitF) (Subgroup.mem_top _) hne43_F hval43_F

end FqXt
end L20261018

#print axioms L20261018.FqXt.inst_finiteRelIndex_top_F
#print axioms L20261018.FqXt.inst_finiteDimensional_Efield_top_F
#print axioms L20261018.FqXt.inst_isGalois_Efield_top_F
#print axioms L20261018.FqXt.hroots_top_F
#print axioms L20261018.FqXt.thm_ramified_1_F
