import L20261018.Hyp125
import L20261018.Hyp45
set_option maxHeartbeats 2000000
open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField
namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]

/-- **载体桥第 3 段的复合映射**：`muNRep` 载体的 Kummer 类 → `GaloBase.V`。

路径：`muNRepCohomologyEquivTrivialFp` → `cohomFpMap (restrictEquiv.symm)` → `coeffMap (iso.hom)`。

**与 `KummerBridge.kummerClass` 的相等性是第 3 段剩余的唯一内容**（两条约 Kummer 类路线的比较）。
本定义已**类型检查通过** ⟹ 该路线可行、无载体错配。 -/
noncomputable def bridgeKc {ζ : F} (hζ : IsPrimitiveRoot ζ p) (a : Fˣ) :
    GaloBase.V F p :=
  ContinuousCohomology.coeffMap (GaloTrivialFp.iso F p).hom 1
    ((TauCeti.cohomFpMap p (TauCeti.absoluteGaloisGroupRestrictEquiv F).symm 1).hom
      ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp p F hζ 1)
        (ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit a)))

/-- **一致性检查**：`bridgeKc` 在平凡类上给 `0`（`(1) = 0`）。 -/
theorem bridgeKc_one {ζ : F} (hζ : IsPrimitiveRoot ζ p) : bridgeKc (F := F) p hζ 1 = 0 := by
  have h1 : ClassFieldTheory.kummerClass F hζ.neZero'.out.isUnit (1 : Fˣ) = 0 := by
    rw [ClassFieldTheory.kummerClass_eq_zero_iff]
    exact one_mem _
  simp only [bridgeKc, h1, map_zero]

end L20261018
#print axioms L20261018.bridgeKc_one
