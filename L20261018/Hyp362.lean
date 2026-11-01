import L20261018.Hyp361
import L20261018.Hyp355

/-!
# R1273（S36 C 项）：`FiniteDimensional (GaloBase.V 𝔽₇((t)) 3)` ⟹ **4.2 无条件**

`HANDOFF` §S36 第 6 轮的收尾：把 `Hyp361.finite_powerClassQuotient`（`Finite (Fˣ/(Fˣ)³)`）
沿 **`Hyp330` 的链条**（一般域，只需换 `F`）传成 `Finite (GaloBase.V F 3)`：

```
Finite (powerClassQuotient Fˣ 3)                      [Hyp361]
  → TauCeti.finite_H1_kummerCoeff                     ⟹ Finite (H¹(G, μ_3))
  → KummerBridge.kummerH1Equiv                        ⟹ Finite (H¹(G, ZMod 3))
  → KummerBridge.h1ToVEquiv                           ⟹ Finite (GaloBase.V F 3)
  → Module.Finite.of_finite                           ⟹ FiniteDimensional
```

⟹ **`orth_eq_bot_F`（论文 4.2 `lem:ramified-vanishing`）在 `𝔽₇((t))`／`p = 3` 上无条件成立**
（`ℚ_[7]` 之外的第一个 `L1` 见证）。

| 声明 | 内容 |
|---|---|
| `finite_H1_kummerCoeff_F` | `Finite (H¹(G, τ.1))` |
| `finite_H1_zmod_F` | `Finite (H¹(G, ZMod 3))` |
| `finite_galoBaseV_F` | ★★★★ `Finite (GaloBase.V F 3)` |
| **`finiteDimensional_galoBaseV_F`** | ★★★★★ `FiniteDimensional (ZMod 3) (GaloBase.V F 3)` |
| **`orth_eq_bot_F_uncond`** | ★★★★★★ **论文 4.2 在 `𝔽₇((t))` 上无条件** |
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

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `H¹(G, μ_3)` 有限（`F = 𝔽₇((t))`）。 -/
theorem finite_H1_kummerCoeff_F :
    Finite (ContCohomology.H1 (AbsoluteGaloisGroup (LaurentSeries (ZMod 7)))
      (TauCeti.KummerCoeff (LaurentSeries (ZMod 7)) 3)) := by
  haveI := finite_powerClassQuotient
  exact TauCeti.finite_H1_kummerCoeff (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries

/-- `H¹(G, ZMod 3)` 有限。 -/
theorem finite_H1_zmod_F :
    Finite (ContCohomology.H1 (AbsoluteGaloisGroup (LaurentSeries (ZMod 7))) (ZMod 3)) := by
  haveI := finite_H1_kummerCoeff_F
  exact Finite.of_equiv _
    (KummerBridge.kummerH1Equiv (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries).toEquiv

/-- ★★★★ **`GaloBase.V 𝔽₇((t)) 3` 有限**。 -/
theorem finite_galoBaseV_F : Finite (GaloBase.V (LaurentSeries (ZMod 7)) 3) := by
  haveI := finite_H1_zmod_F
  exact Finite.of_equiv _ (KummerBridge.h1ToVEquiv (LaurentSeries (ZMod 7)) 3).toEquiv

/-- ★★★★★ **载体维度**（`Hyp355` 三条的最后一个假设）。 -/
instance finiteDimensional_galoBaseV_F :
    FiniteDimensional (ZMod 3) (GaloBase.V (LaurentSeries (ZMod 7)) 3) := by
  haveI := finite_galoBaseV_F
  exact Module.Finite.of_finite

/-- ★★★★★★ **论文 4.2（`lem:ramified-vanishing`）在 `𝔽₇((t))`／`p = 3` 上无条件成立**
（`L1` 非空见证：假设类全部可满足 —— `char = 7 ≠ 3`、`μ_3 ⊂ 𝔽₇`、Hensel、有限剩余域）。 -/
-- @source file=raw/L20261018.tex locator=line:1608 quote="若模 $p$ 赋值映射 $\bar v:U\to\Fp$ 非零，则 $U^\perp=0$。"
theorem orth_eq_bot_F_uncond :
    ResidueCupData.orth (GaloBase.cup (K := LaurentSeries (ZMod 7)) (p := 3)) a1F a2F = ⊥ :=
  orth_eq_bot_F

end FqXt
end L20261018

#print axioms L20261018.FqXt.finite_H1_kummerCoeff_F
#print axioms L20261018.FqXt.finite_galoBaseV_F
#print axioms L20261018.FqXt.finiteDimensional_galoBaseV_F
#print axioms L20261018.FqXt.orth_eq_bot_F_uncond
