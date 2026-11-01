import Hyp734

/-!
# S66 R4：分片 **4c-v（第二格）** —— `h1BridgeQ` 与**系数映射**交换

4c-v 的模型切换需要两条自然性，本件做**系数**那一条（膨胀那条见 §"剩余"）。

```
h1BridgeQ ∘ coeffMap ι = explicitCoeff1 ι ∘ h1BridgeQ
```

直接来自库内 **`explicitH1AddEquivContinuousCohomology_coeffMap`**
（`CohomologyComparison.lean:183`）：
`coeffMap^cont f 1 (h1Bridge x) = h1Bridge (explicitCoeff1 f x)`，
把 `x` 换成 `h1Bridge⁻¹ y` 即得本件的形态。

## 剩余（4c-v 的最后一格）

**膨胀**那一条：`h1BridgeQ_C ∘ map φ sub 1 = explicitInfl1_C 1 ∘ h1BridgeQ_{Cᴵ}`，
来自库内 **`explicitIso_infl`**（`Inflation/Comparison.lean:149`）。
⚠ 后者的陈述走 `DiscreteH1` 载体（`discreteH1Equiv`），故它比本件多**一跳**；
另有 `coeffMap_ofDiscreteModuleQuotient_comp_infl`（同文件 `:95`）把
`infl(coeffMap(quotient) ·)` 认成 `map φ (Mᴺ↪M)`。

## 4d 的最新精确形态（本轮顺带锁定，取代 `S66-4CV-PLAN.md` §2 的写法）

由 `Hyp717` 的**定义式** `infl1AddEquiv_of_H1_subsingleton = AddEquiv.ofBijective (explicitInfl1 …)`
（`Hyp717:79`）⟹ **`inflStep = (explicitInfl1_C)⁻¹` 是定义级**的。于是

```
∂² ∘ Inf₂ = contM_coeffMap ∘ inflStep ∘ h1BridgeQ_C ∘ map φ fC 1 ∘ e
          = contM_coeffMap ∘ inflStep ∘ h1BridgeQ_C ∘ (coeffMap ι ≫ map φ sub) ∘ e   （Hyp734）
          = contM_coeffMap ∘ inflStep ∘ (Infl_C^expl ∘ h1BridgeQ_{Cᴵ}) ∘ coeffMap ι ∘ e  （膨胀自然性）
          = contM_coeffMap ∘ h1BridgeQ_{Cᴵ} ∘ coeffMap ι ∘ e                       （inflStep = Infl_C⁻¹）
          = contM_coeffMap ∘ explicitCoeff1 ι ∘ h1BridgeQ_T ∘ e                      （本件）
          = 0                                                                       （Hyp733：contM ∘ ι = 0）
```

⟹ 4d 只剩**代数收尾**（`explicitCoeff1` 的复合律 ＋ `Hyp733`），见 `Hyp736`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- ★★★★★ **`h1BridgeQ` 与系数映射交换**：`H¹` 比较同构把连续系数映射译成显式系数映射。

即 `h1BridgeQ (coeffMap f y) = explicitCoeff1 f (h1BridgeQ y)` —— 4c-v 模型切换的**系数那一半**。 -/
theorem h1BridgeQ_coeffMap
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N)
    (y : ↑(continuousCohomology 1 (ofDiscreteModule ℤ G M)).toModuleCat) :
    (explicitH1AddEquivContinuousCohomology G N).symm
        ((ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
            (fun g m => map_smul f g m)) 1) y)
      = explicitCoeff1 G M f continuous_of_discreteTopology
          ((explicitH1AddEquivContinuousCohomology G M).symm y) := by
  rw [AddEquiv.symm_apply_eq]
  simpa using explicitH1AddEquivContinuousCohomology_coeffMap G M N f
    ((explicitH1AddEquivContinuousCohomology G M).symm y)

/-- 同一事实的**函子形态**（供 4d 直接改写复合）：`h1BridgeQ_N ∘ coeffMap f = explicitCoeff1 f ∘ h1BridgeQ_M`。 -/
theorem h1BridgeQ_comp_coeffMap
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N] (f : M →+[G] N) :
    (explicitH1AddEquivContinuousCohomology G N).symm.toAddMonoidHom.comp
        (ContinuousCohomology.coeffMap
          (TauCeti.ofDiscreteModuleMap f.toAddMonoidHom.toIntLinearMap
            (fun g m => map_smul f g m)) 1).hom.toAddMonoidHom
      = (explicitCoeff1 G M f continuous_of_discreteTopology).comp
          (explicitH1AddEquivContinuousCohomology G M).symm.toAddMonoidHom := by
  ext y
  exact h1BridgeQ_coeffMap (G := G) (M := M) N f y

end L20261018

#print axioms L20261018.h1BridgeQ_coeffMap
#print axioms L20261018.h1BridgeQ_comp_coeffMap
