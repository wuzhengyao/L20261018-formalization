import L20261018.Witness.Step010_q7_nonzero_cup

/-!
# R1236（S34 第 8 轮）：**`FiniteDimensional (ZMod 3) (GaloBase.V ℚ_[7] 3)`** —— `L1` 残余的最后硬缺口

`Hyp321` 三条的 `L1` 见证需要 `[FiniteDimensional (ZMod p) (GaloBase.V F p)]`（4.2／4.3(1) 的
载体维度假设）。本轮在 `F = ℚ_[7]`、`p = 3` 上把它造出来，链条全部在库内：

```
finiteIndex_range_powMonoidHom      (TauCeti，[IsNonarchimedeanLocalField K])
  ⟹ (powerSubgroup Kˣ 3).FiniteIndex ⟹ Finite (powerClassQuotient Kˣ 3)
finite_H1_kummerCoeff                ⟹ Finite (H¹(G, KummerCoeff))
kummerH1Equiv (AddEquiv)             ⟹ Finite (H¹(G, ZMod 3))
h1ToVEquiv    (AddEquiv)             ⟹ Finite (GaloBase.V)
Module.Finite.of_finite              ⟹ FiniteDimensional
```

## 本轮

| 声明 | 内容 |
|---|---|
| `finite_powerClassQuotient_Q7` | `Finite (powerClassQuotient ℚ_[7]ˣ 3)` |
| `finite_H1_kummerCoeff_Q7` | `Finite (H¹(G, KummerCoeff))` |
| `finite_H1_zmod_Q7` | `Finite (H¹(G, ZMod 3))` |
| **`finite_galoBaseV_Q7`** | ★★★★ `Finite (GaloBase.V ℚ_[7] 3)` |
| **`finiteDimensional_galoBaseV_Q7`** | ★★★★★★ `FiniteDimensional (ZMod 3) (GaloBase.V ℚ_[7] 3)` |
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

/-- `ℚ_[7]^×/(ℚ_[7]^×)^3` 有限（`ℚ_[7]` 是非阿基米德局部域）。 -/
theorem finite_powerClassQuotient_Q7 : Finite (TauCeti.powerClassQuotient ℚ_[7]ˣ 3) := by
  haveI : (TauCeti.powerSubgroup ℚ_[7]ˣ 3).FiniteIndex := by
    rw [TauCeti.powerSubgroup_eq_range_powMonoidHom]
    exact TauCeti.finiteIndex_range_powMonoidHom (n := 3) (by norm_num)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- `H¹(G, μ_3)` 有限。 -/
theorem finite_H1_kummerCoeff_Q7 :
    Finite (ContCohomology.H1 (AbsoluteGaloisGroup ℚ_[7]) (KummerCoeff ℚ_[7] 3)) := by
  haveI := finite_powerClassQuotient_Q7
  exact TauCeti.finite_H1_kummerCoeff ℚ_[7] 3 three_isUnit_F

/-- `H¹(G, ZMod 3)` 有限（沿系数识别）。 -/
theorem finite_H1_zmod_Q7 :
    Finite (ContCohomology.H1 (AbsoluteGaloisGroup ℚ_[7]) (ZMod 3)) := by
  haveI := finite_H1_kummerCoeff_Q7
  exact Finite.of_equiv _ (KummerBridge.kummerH1Equiv ℚ_[7] 3 three_isUnit_F).toEquiv

/-- ★★★★ `GaloBase.V ℚ_[7] 3 = H¹(G, μ_3)` 有限（沿模型比较）。 -/
theorem finite_galoBaseV_Q7 : Finite (GaloBase.V ℚ_[7] 3) := by
  haveI := finite_H1_zmod_Q7
  exact Finite.of_equiv _ (KummerBridge.h1ToVEquiv ℚ_[7] 3).toEquiv

/-- ★★★★★★ **`FiniteDimensional (ZMod 3) (GaloBase.V ℚ_[7] 3)`** —— `L1` 见证的维度输入。 -/
instance finiteDimensional_galoBaseV_Q7 : FiniteDimensional (ZMod 3) (GaloBase.V ℚ_[7] 3) := by
  haveI := finite_galoBaseV_Q7
  exact Module.Finite.of_finite

end Q7

end L20261018

#print axioms L20261018.finite_powerClassQuotient_Q7
#print axioms L20261018.finite_H1_kummerCoeff_Q7
#print axioms L20261018.finite_H1_zmod_Q7
#print axioms L20261018.finite_galoBaseV_Q7
