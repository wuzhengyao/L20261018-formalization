import L20261018.Hyp782

/-!
# S74 R9：`∂²` 单射的机检归约 —— **只需 `ker contM_coeffMap = 0`**

`GAP3-PLAN` §12 读出：`∂²` 单射 ⟺ `ker contM = im(coeffMap (B^H → C^H))`，而后者经
`longExact_exact₃` ＋ `H¹(G,B)=0` 塌成 `0`。本件机检其中"复合"的那一半：
`∂² = contM_coeffMap ∘ deltaTwoShift ∘ (标量限制同构)`，后两者是 `AddEquiv`，故

```
ker contM_coeffMap = 0  ⟹  ∂² 单射
```

## 诚实边界

* `[CompactSpace ↥(inertiaLoc F)]` 是**技术实例**（本战役既有口径；`Hyp719` 的 `deltaTwoShift` 需要），
  不是数学假设。
* 本件**仍是归约**（不含 GS 6.8.4 的数学）。R9 的数学目标 —— 连续模型 Leibniz
  `δ₁(Inf z₀ ⌣ Inf a) = δ₀(Inf z₀) ⌣ Inf a` —— **本轮未动工**（上下文预算）。
* 若 Leibniz 成功，`∂²` 的**值**即 `explicitCup01 x₀ a`，非零性自动 ⟹ 本件的条件**可能不必要**
  （`GAP3-PLAN` §12.1）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti.ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (q : ℕ) [Fact q.Prime]
  [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- ★★★★★ **`∂²` 的中间段单射 ⟸ `ker contM_coeffMap = 0`**。 -/
theorem deltaTwoCarrierInertia_injective_of_contM_injective
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [CompactSpace ↥(inertiaLoc F)]
    (h : Function.Injective (contM_coeffMap (F := F) p (inertiaLoc F))) :
    Function.Injective (deltaTwoCarrierInertia (F := F) p q hcop) := by
  intro a b hab
  exact (deltaTwoShift (H := inertiaLoc F) (C := contC (F := F) p)
      (contCoindSES (F := F) p)
      (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
        (AbsoluteGaloisGroup F) (ZMod p) 0)
      (TauCeti.ContCohomology.subsingleton_continuousCohomology_discreteCoind_bot_int
        (AbsoluteGaloisGroup F) (ZMod p) 1)
      (inertiaLoc_subsingleton_H1_contC (F := F) p q hcop)).injective
    (h hab)

/-- ★★★★★ **`∂²` 单射 ⟸ `ker contM_coeffMap = 0`**。 -/
theorem deltaTwoGaloBase'_injective_of_contM_injective
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [CompactSpace ↥(inertiaLoc F)]
    (h : Function.Injective (contM_coeffMap (F := F) p (inertiaLoc F))) :
    Function.Injective (deltaTwoGaloBase' (F := F) p q hcop) := by
  have hmid := deltaTwoCarrierInertia_injective_of_contM_injective
    (F := F) (p := p) (q := q) (hcop := hcop) h
  intro a b hab
  have h1 : (deltaTwoCarrierInertia (F := F) p q hcop)
      ((restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm a)
      = (deltaTwoCarrierInertia (F := F) p q hcop)
        ((restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm b) := by
    rw [deltaTwoGaloBase'_apply, deltaTwoGaloBase'_apply] at hab
    exact hab
  exact (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2).symm.injective
    (hmid h1)

end L20261018

#print axioms L20261018.deltaTwoCarrierInertia_injective_of_contM_injective
#print axioms L20261018.deltaTwoGaloBase'_injective_of_contM_injective
