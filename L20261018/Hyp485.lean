import Hyp484

/-!
# S40 R26：`H²(G, μ_p)` 是 `p`-挠（A4a）

`G` 特化为 `TauCeti.AbsoluteGaloisGroup F`（`DistribMulAction` 实例只在那里有）。
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

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **系数层 `p`-乘映射为零**。 -/
theorem nsmulAddMonoidHom_kummerCoeff_eq_zero :
    (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p) = 0 := by
  refine AddMonoidHom.ext (fun m => ?_)
  exact kummerCoeff_nsmul_eq_zero (K := F) p m

/-- ★★★★★ **`H²(G, μ_p)` 是 `p`-挠**（A4a 的 `p`-挠性）。

`hEq` 先作为独立 `have`、完整标注 `∀`-类型，再传给 `ofDiscreteModuleMap` ——
这是 R26 §105.2 定的修法（lambda 内联会让 `g` 的类型不确定）。 -/
theorem kummerCoeffH2_nsmul_eq_zero
    (x : ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat) :
    p • x = 0 := by
  have hEq : ∀ (g : TauCeti.AbsoluteGaloisGroup F) (m : KummerCoeff F p),
      (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p) (g • m)
        = g • (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p) m := by
    intro g m
    rw [nsmulAddMonoidHom_kummerCoeff_eq_zero]
    simp
  have hmap : TauCeti.ofDiscreteModuleMap
      (f := (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p).toIntLinearMap)
      hEq = 0 := by
    apply TopRep.hom_ext
    ext m
    show (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p) m = 0
    exact kummerCoeff_nsmul_eq_zero (K := F) p m
  calc p • x = (ContinuousCohomology.coeffMap (TauCeti.ofDiscreteModuleMap
        (f := (nsmulAddMonoidHom p : KummerCoeff F p →+ KummerCoeff F p).toIntLinearMap) hEq) 2) x := by
        rw [ContinuousCohomology.coeffMap_nsmulAddMonoidHom]
        rfl
    _ = 0 := by
        rw [hmap, ContinuousCohomology.coeffMap_def]
        simp

end L20261018

#print axioms L20261018.nsmulAddMonoidHom_kummerCoeff_eq_zero
#print axioms L20261018.kummerCoeffH2_nsmul_eq_zero
