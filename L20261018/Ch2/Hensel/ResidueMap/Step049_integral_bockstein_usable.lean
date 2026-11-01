import L20261018.Ch2.Hensel.ResidueMap.Step048_integral_bockstein_range_complete

/-!
# S40 R24：`integralBockstein` range 引理的**可用形式**（`n • x = 0`）＋ A4 机件登记

## 本轮

R23 的 `integralBockstein_one_range` 的右端是 `nsmulAddMonoidHom n x = 0`；
本轮给出下游真正要用的 **`n • x = 0`** 形式，并登记 A4 需要的、**库内已有**的两件。

## 侦察（R17 纪律）

| 件 | 内容 | 出处 |
|---|---|---|
| **`ContinuousCohomology.coeffMap_nsmulAddMonoidHom (k) (n)`** | ★★★★ `coeffMap (nsmulAddMonoidHom k) n = k • 𝟙` | `ContCohomology/Functoriality.lean` 一族 |
| **`TauCeti.h2KummerToUnits_range`** | ★★★★★ `(∃ y, h2KummerToUnits K n y = x) ↔ n • x = 0`（像 = `n`-挠，`UnitsCoeff` 层） | `BrauerTorsion.lean` |
| `TauCeti.integralBockstein_one_range` | （R23）`↔ nsmulAddMonoidHom n x = 0` | `Hyp483` |

## 机检件

| 声明 | 内容 |
|---|---|
| **`integralBockstein_one_range_nsmul`** | ★★★★★ `(∃ y, δ y = x) ↔ n • x = 0` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- `G` 在 `ULift ℤ` 上的平凡作用。 -/
local instance integralTrivialAction'' : DistribMulAction G (ULift.{0} ℤ) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用连续（离散）。 -/
local instance integralContinuousSMul'' : ContinuousSMul G (ULift.{0} ℤ) := ⟨continuous_snd⟩

/-- ★★★★★ **`integralBockstein` 的像 = `n`-挠**（`n • x = 0` 形式，下游直接可用）。 -/
theorem integralBockstein_one_range_nsmul (n : ℕ) [NeZero n]
    (x : ↑(continuousCohomology 2
      (TauCeti.ofDiscreteModule ℤ G (ULift.{0} ℤ))).toModuleCat) :
    (∃ y, ⇑(ConcreteCategory.hom (TauCeti.integralBockstein G n 1)) y = x) ↔ n • x = 0 :=
  integralBockstein_one_range (G := G) n x

/-- ★★★★★ **可用性锁定**：`h2KummerToUnits` 的像 = `n`-挠（`UnitsCoeff` 层）。
A4 的「`p`-挠性」一步的直接工具。 -/
theorem h2KummerToUnits_range_available {K : Type} [Field K] (n : ℕ) (hn : IsUnit (n : K))
    (x : ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup K) (TauCeti.UnitsCoeff K))).toModuleCat) :
    (∃ y, (TopModuleCat.Hom.hom (TauCeti.h2KummerToUnits K n)) y = x) ↔ n • x = 0 :=
  TauCeti.h2KummerToUnits_range hn x

end L20261018

#print axioms L20261018.integralBockstein_one_range_nsmul
#print axioms L20261018.h2KummerToUnits_range_available
