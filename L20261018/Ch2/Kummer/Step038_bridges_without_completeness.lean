import L20261018.Ch2.Kummer.Step031_t1_model_comparison
import L20261018.Ch2.Kummer.Step037_kc_scalar_transfer

/-!
# R1215（`Hyp221` 的两条桥**去掉完备性**）

`Hyp221` 的 `h1ToVEquiv_eq_muP`（模型桥）与 `kummerClass_eq_muP`（Kummer 类的具体形态）
都在 `[IsNonarchimedeanLocalField F]` 的 section 里，但**证明体完全不用完备性**
（`AddEquiv.ext` ＋ `rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply]` ＋ `rfl`）。

本文件把**模型桥** `h1ToVEquiv_eq_muP` 搬到**一般 Hensel 离散赋值域**
（仅 `[ValuativeRel F] [TopologicalSpace F]`）。这正是 `PLAN-HBRIDGE.md` §4.1 所说的
「`h1ToVEquiv` 实例路径不 defeq」那条障碍的**解除**。
（`kummerClass_eq_muP` 的搬移还差一个 `Continuous` 实例，下一轮补。）
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section GeneralHensel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **战役侧的 `h1ToVEquiv` 就是 `muP.OfDiscrete`** —— **无需完备性**。 -/
theorem h1ToVEquiv_eq_muP' :
    KummerBridge.h1ToVEquiv F p
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete := by
  refine AddEquiv.ext fun x => ?_
  show ContCohomology.restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 1
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) x)
    = ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv (GaloBase.muP F p) 1
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (GaloBase.muP F p).V x)
  rw [ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv_apply]
  rfl

/-- `kummerH1Equiv` 的具体形态 —— **无需完备性**（原 `Hyp216` 版在完备 section 内）。 -/
theorem kummerH1Equiv_apply_eq' (hp : IsUnit (p : F))
    (x : ContCohomology.H1 (AbsoluteGaloisGroup F) (KummerCoeff F p)) :
    KummerBridge.kummerH1Equiv F p hp x
      = explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (eCoeffHom (F := F) p hp)
          continuous_of_discreteTopology x := by
  rw [KummerBridge.kummerH1Equiv, ContCohomology.explicitCoeff1Equiv_apply]
  rfl

/-- `kummerClass` 的具体形态 —— **无需完备性**。 -/
theorem kummerClass_eq_thetaOne' (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = KummerBridge.h1ToVEquiv F p
          (explicitCoeff1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (eCoeffHom (F := F) p hp)
            continuous_of_discreteTopology (TauCeti.kummerMap F p hp a).toAdd) := by
  rw [KummerBridge.kummerClass, kummerH1Equiv_apply_eq']

/-- ★★★★★ **Kummer 类的 `muP` 具体形态** —— **无需完备性**。

这是块 5（`kcCanonical = c • bridgeKc`）的第二个前置：
把 `KummerBridge.kummerClass` 完全展开到 `(muP).OfDiscrete ∘ explicitMap1 (eCoeffHom) ∘ kummerMap`。 -/
theorem kummerClass_eq_muP' (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (ZMod p)
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            (eCoeffHom (F := F) p hp) continuous_of_discreteTopology
            (fun g m => (eCoeffHom (F := F) p hp).map_smul g m)
            (TauCeti.kummerMap F p hp a).toAdd) := by
  rw [kummerClass_eq_thetaOne', h1ToVEquiv_eq_muP']
  rfl

end GeneralHensel

end L20261018

#print axioms L20261018.h1ToVEquiv_eq_muP'
#print axioms L20261018.kummerClass_eq_muP'
