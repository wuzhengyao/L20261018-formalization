import Hyp330

/-!
# R1237（S34 第 9 轮）：**`ℚ_[7]` 上存在非零杯积**（`hne` 的落地）

用 `Hyp328`（`kc 2 ≠ 0`）、`Hyp329`（`v̄ (kc 2) = 0`）、`Hyp327`（`ker v̄ = range inf`）、
`Hyp326`／`Hyp325`（`tame_u_pi`）与 `H2Bridge.redEquiv_cup`，造出

```
∃ a₁ a₂ : GaloBase.V ℚ_[7] 3,  GaloBase.cup a₁ a₂ ≠ 0
```

**证明骨架**（全部零额外假设，`F = ℚ_[7]`, `p = 3`）：

```
kc_T 2 ≠ 0（Hyp328 的 muNRep 侧）且 v̄ (kc_T 2) = 0（Hyp329）
  ⟹ 由 ker v̄ = range inf（Hyp327）取 y 使 inf y = kc_T 2，且 y ≠ 0
  ⟹ tame_u_pi：∂(cup (inf y) π) = y ≠ 0  ⟹ cup (kc_T 2) π ≠ 0
  ⟹ redEquiv_cup：redEquiv (cup a₁ a₂) = cup (kc_T 2) π ≠ 0  （aᵢ := redEquiv1.symm …）
  ⟹ cup a₁ a₂ ≠ 0
```

## 本轮

| 声明 | 内容 |
|---|---|
| `kc_two_ne_zero_muNRep_Q7` | `ClassFieldTheory.kummerClass (2) ≠ 0` |
| **`exists_galoCup_ne_zero_Q7`** | ★★★★★★ **`∃ a₁ a₂, GaloBase.cup a₁ a₂ ≠ 0`** |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section Q7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `2` 作为 `ℚ_[7]ˣ` 的元素。 -/
noncomputable def twoUnit : ℚ_[7]ˣ := Units.mk0 (2 : ℚ_[7]) (by norm_num)

/-- ★★★ **`muNRep` 侧的 `kc 2` 非零**（由 `2` 不是立方）。 -/
theorem kc_two_ne_zero_muNRep_Q7 :
    ClassFieldTheory.kummerClass ℚ_[7] three_isUnit_F twoUnit ≠ 0 := by
  intro hzero
  rw [ClassFieldTheory.kummerClass_eq_zero_iff] at hzero
  rw [TauCeti.powerSubgroup_eq_range_powMonoidHom, MonoidHom.mem_range] at hzero
  obtain ⟨c, hc⟩ := hzero
  apply not_exists_cube_two_Q7
  refine ⟨(c : ℚ_[7]), ?_⟩
  have h := congrArg (fun u : ℚ_[7]ˣ => (u : ℚ_[7])) hc
  simpa [twoUnit, powMonoidHom] using h

/-- ★★★★★★ **`ℚ_[7]` 上存在非零杯积**（`hne` 的落地，零额外假设）。 -/
theorem exists_galoCup_ne_zero_Q7 :
    ∃ a1 a2 : GaloBase.V ℚ_[7] 3,
      GaloBase.cup (K := ℚ_[7]) (p := 3) a1 a2 ≠ 0 := by
  -- 一致化元与 Hensel 数据
  obtain ⟨π, hzπ, hnotpow⟩ :=
    exists_uniformizer_not_pow (F := ℚ_[7]) (p := 3) (Fact.out : Nat.Prime 3).ne_one
  haveI hIrred : Fact (Irreducible (X ^ 3 - C (π : ℚ_[7]))) :=
    ⟨(capelli_irreducible_iff (F := ℚ_[7]) (p := 3) (by decide)).mpr hnotpow⟩
  haveI hFin : Module.Finite ℚ_[7] (AdjoinRoot (X ^ 3 - C (π : ℚ_[7]))) :=
    moduleFinite_adjoinRoot (p := 3) (π : ℚ_[7])
  have hπ : vCompatHom (F := ℚ_[7]) π = Multiplicative.ofAdd (1 : ℤ) := by
    rw [show vCompatHom (F := ℚ_[7]) π = Multiplicative.ofAdd (zval (F := ℚ_[7]) π) from rfl, hzπ]
  obtain ⟨D, hDval⟩ := exists_henselResidueData_noBridge (F := ℚ_[7]) (p := 3)
    (v := vCompatHom) (π := π) zeta3_spec three_isUnit_O three_isUnit_F
    valCompat_of_dvr hπ (by decide) (kummerCup_skew zeta3_spec)
  -- `x := kc_T 2`，它在 `ker v̄` 中
  set x : ↑(continuousCohomology 1 (ClassFieldTheory.muNRep 3 ℚ_[7])).toModuleCat :=
    ClassFieldTheory.kummerClass ℚ_[7] three_isUnit_F twoUnit with hxdef
  have hxval : D.val x = 0 := by
    rw [hDval]
    show valH1Gen (p := 3) vCompatHom three_isUnit_F x = 0
    rw [hxdef, valH1Gen_kummerClass]
    have hz : zval (F := ℚ_[7]) twoUnit = 0 := zval_unit_eq_zero (F := ℚ_[7]) two_isUnit_O
    rw [show vCompatHom (F := ℚ_[7]) twoUnit
      = Multiplicative.ofAdd (zval (F := ℚ_[7]) twoUnit) from rfl, hz]
    simp
  -- 取 `y` 使 `inf y = x`，则 `y ≠ 0`
  obtain ⟨y, hy⟩ := (exact_infl_val D x).mp hxval
  have hxne : x ≠ 0 := kc_two_ne_zero_muNRep_Q7
  have hyne : y ≠ 0 := by
    intro h0
    exact hxne (by rw [← hy, h0, map_zero])
  -- `tame_u_pi` ⟹ `cup x π ≠ 0`
  have hcupT : ((ClassFieldTheory.kummerCupPairing zeta3 zeta3_spec).cup 1 1) x D.pi ≠ 0 := by
    intro h0
    have h1 := D.tame_u_pi y
    rw [hy, h0, map_zero] at h1
    exact hyne h1.symm
  -- 沿 `redEquiv` 搬回 `GaloBase` 载体
  refine ⟨(H2Bridge.redEquiv1 zeta3_spec).symm x,
    (H2Bridge.redEquiv1 zeta3_spec).symm D.pi, ?_⟩
  intro h0
  have h1 := congrArg (H2Bridge.redEquiv zeta3_spec) h0
  simp only [map_zero, H2Bridge.redEquiv_cup, AddEquiv.apply_symm_apply] at h1
  exact hcupT h1

end Q7

end L20261018

#print axioms L20261018.kc_two_ne_zero_muNRep_Q7
#print axioms L20261018.exists_galoCup_ne_zero_Q7
