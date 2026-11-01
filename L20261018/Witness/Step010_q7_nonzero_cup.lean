import L20261018.Witness.Step009_q7_non_cube_unit

/-!
# R1235（S34 第 7 轮）：**`ℚ_[7]` 的非零杯积类**（`hne` 的第二、三块）

路线：`2` 是单位（`v 2 = 0`）其 Kummer 类非零（`Hyp328`）⟹ `kc 2 ∈ ker v̄`
⟹ 由 `HenselResidueData.tame_u_pi`（`∂(inf y ∪ π) = y`）⟹ `cup (kc 2) π ≠ 0`。

本轮补两块：

| 声明 | 内容 |
|---|---|
| `znat_eq_zero_of_isUnit` | `𝒪[F]` 的单位在 `znat` 上取 `0`（`znat_le_iff_dvd` ＋ `znat_one`） |
| `zval_unit_eq_zero` | ★ `𝒪[F]` 的单位在 `zval` 上取 `0`（`zval_spec` 于 `x := u`, `y := 1`） |
| `two_isUnit_O` | `IsUnit (2 : ↥𝒪[ℚ_[7]])` |
| **`kc_two_mem_ker_Q7`** | ★★★★ `v̄ (kc 2) = 0`，即 `kc 2 ∈ ker v̄` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ZnatUnit

variable {F : Type} [Field F] [ValuativeRel F]
  [IsDiscreteValuationRing ↥𝒪[F]]

/-- **`𝒪[F]` 的单位在 `znat` 上取 `0`**：`u ∣ 1` ⟹ `znat u ≤ znat 1 = 0`。 -/
theorem znat_eq_zero_of_isUnit {x : ↥𝒪[F]} (hx : x ≠ 0) (hu : IsUnit x) :
    znat (F := F) x = 0 := by
  have h1 : znat (F := F) x ≤ znat (F := F) (1 : ↥𝒪[F]) :=
    (znat_le_iff_dvd (F := F) hx one_ne_zero).mpr (isUnit_iff_dvd_one.mp hu)
  rw [znat_one] at h1
  omega

/-- ★ **`𝒪[F]` 的单位在 `zval` 上取 `0`**。 -/
theorem zval_unit_eq_zero {u : ↥𝒪[F]} (hu : IsUnit u) :
    zval (F := F) (Units.mk0 (u : F) (by
      intro h
      exact hu.ne_zero (Subtype.coe_injective (by simp [h])))) = 0 := by
  have h := zval_spec (F := F) (a := Units.mk0 (u : F) (by
      intro h
      exact hu.ne_zero (Subtype.coe_injective (by simpa using h))))
    (x := u) (y := 1) one_ne_zero (by simp)
  rw [h, znat_eq_zero_of_isUnit hu.ne_zero hu, znat_one]
  simp

end ZnatUnit

section Q7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity ℚ_[7] 3 := hasEnoughRootsOfUnity_Q7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `2` 是 `𝒪[ℚ_[7]]` 的单位（`7 ∤ 2`）。 -/
theorem two_isUnit_O : IsUnit (2 : ↥𝒪[ℚ_[7]]) :=
  Padic.isUnit_intCast_integerRing (p := 7) (m := 2) (by decide)

/-- ★★★★ **`kc 2 ∈ ker v̄`**：`v̄ (kc a) = v a mod p`，而 `v 2 = 0`。 -/
theorem kc_two_mem_ker_Q7 :
    valLinOf (F := ℚ_[7]) (p := 3) vCompatHom three_isUnit_F
      (KummerBridge.kummerClass ℚ_[7] 3 three_isUnit_F
        (Units.mk0 (2 : ℚ_[7]) (by norm_num))) = 0 := by
  rw [valLinOf_kummerClass]
  show ((vCompatHom (F := ℚ_[7]) (Units.mk0 (2 : ℚ_[7]) (by norm_num))).toAdd : ZMod 3) = 0
  show ((Multiplicative.ofAdd (zval (F := ℚ_[7])
    (Units.mk0 (2 : ℚ_[7]) (by norm_num)))).toAdd : ZMod 3) = 0
  rw [show (Multiplicative.ofAdd (zval (F := ℚ_[7])
      (Units.mk0 (2 : ℚ_[7]) (by norm_num)))).toAdd = zval (F := ℚ_[7])
        (Units.mk0 (2 : ℚ_[7]) (by norm_num)) from rfl,
    show Units.mk0 (2 : ℚ_[7]) (by norm_num) =
      Units.mk0 (((2 : ↥𝒪[ℚ_[7]]) : ℚ_[7])) (by
        intro h
        exact two_isUnit_O.ne_zero (Subtype.coe_injective (by simpa using h))) from rfl,
    zval_unit_eq_zero (F := ℚ_[7]) two_isUnit_O]
  simp

end Q7

end L20261018

#print axioms L20261018.znat_eq_zero_of_isUnit
#print axioms L20261018.zval_unit_eq_zero
#print axioms L20261018.two_isUnit_O
#print axioms L20261018.kc_two_mem_ker_Q7
