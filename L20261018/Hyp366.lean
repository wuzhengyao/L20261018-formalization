import L20261018.Hyp365

/-!
# R1277（S36 C 项）：`GaloBase` 层 `(kc 2) ∪ (kc π) ≠ 0`

照 `Hyp336.hcupG_Q7` 的路线，把 `Hyp365.hcupT_pi`（muNRep 载体）沿
`H2Bridge.redEquiv_cup` ＋ **(R1-σ)**（`scaled_bridge_uncond`）搬回 `GaloBase` 载体。

| 声明 | 内容 |
|---|---|
| **`hcupG_F`** | ★★★★★★ `GaloBase.cup (kc 2) (kc π) ≠ 0` |
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

/-- ★★★★★★ **`GaloBase` 载体的非零杯积**：`(kc 2) ∪ (kc π) ≠ 0`。

由 `(R1-σ)`：`redEquiv1 (kc a) = c • kc_T a`；故
`redEquiv (cup (kc 2) (kc π)) = c² • ((kc_T 2) ∪ (kc_T π)) ≠ 0`（`Hyp365.hcupT_pi`）。 -/
theorem hcupG_F :
    GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3)
      (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF)
      (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
        (pi : (LaurentSeries (ZMod 7))ˣ)) ≠ 0 := by
  obtain ⟨c, hc0, hsc⟩ := scaled_bridge_uncond (F := LaurentSeries (ZMod 7)) (p := 3)
    three_isUnit_laurentSeries zetaF_spec
  intro h0
  have h1 : H2Bridge.redEquiv zetaF_spec
      (GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3)
        (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF)
        (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
          (pi : (LaurentSeries (ZMod 7))ˣ))) = 0 := by
    rw [h0, map_zero]
  rw [H2Bridge.redEquiv_cup, hsc twoUnitF, hsc (pi : (LaurentSeries (ZMod 7))ˣ)] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_smul] at h1
  exact hcupT_pi ((smul_eq_zero.mp h1).resolve_left (mul_ne_zero hc0 hc0))

/-- ★★★★★★ **4.3(1) 的 `hne`**：`(kummerExplicit 2) ∪' (kummerExplicit π) ≠ 0`（`H¹` 层）。

由 `Hyp364.cup_compat_theta_F`（θ-桥）＋ `theta1_kummerClass_F` ＋ `theta2g` 是线性等价 ⟹
从 `hcupG_F` 搬运。 -/
theorem hne43_F :
    Theo352.cupLin (F := LaurentSeries (ZMod 7)) (p := 3)
      (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
        three_isUnit_laurentSeries twoUnitF)
      (GaloCup.kummerExplicit (F := LaurentSeries (ZMod 7)) (p := 3)
        three_isUnit_laurentSeries (pi : (LaurentSeries (ZMod 7))ˣ)) ≠ 0 := by
  intro h0
  have hcompat := cup_compat_theta_F
    (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF)
    (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
      (pi : (LaurentSeries (ZMod 7))ˣ))
  rw [theta1_kummerClass_F twoUnitF, theta1_kummerClass_F (pi : (LaurentSeries (ZMod 7))ˣ)] at hcompat
  rw [h0] at hcompat
  exact hcupG_F ((theta2g (F := LaurentSeries (ZMod 7)) 3).injective (by rw [hcompat, map_zero]))

/-- ★★★★★ **4.3(1) 的 `hval`**：取 `u = kc π`，`v̄ (kc π) = 1 ≠ 0`。 -/
theorem hval43_F :
    ∃ u ∈ ResidueCupData.plane (k := ZMod 3)
      (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries twoUnitF)
      (KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
        (pi : (LaurentSeries (ZMod 7))ˣ)),
      valLinOf (F := LaurentSeries (ZMod 7)) (p := 3)
        (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries u ≠ 0 := by
  refine ⟨KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries
    (pi : (LaurentSeries (ZMod 7))ˣ), Submodule.subset_span (by simp), ?_⟩
  rw [valLinOf_kummerClass]
  show ((Multiplicative.toAdd (vCompatHom (F := LaurentSeries (ZMod 7))
    (pi : (LaurentSeries (ZMod 7))ˣ)) : ℤ) : ZMod 3) ≠ 0
  rw [pi_hπ]
  simp

end FqXt
end L20261018

#print axioms L20261018.FqXt.hcupG_F
#print axioms L20261018.FqXt.hne43_F
#print axioms L20261018.FqXt.hval43_F
