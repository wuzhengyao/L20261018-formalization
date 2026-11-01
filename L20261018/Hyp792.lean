import Hyp791

/-!
# S76 R5：`contDelta_res_naturality` 的**逐点形态**（第 5 步 (a) 的第二块）

`Hyp551.contDelta_res_naturality` 给的是 `TopModuleCat` 里的 `≫` 等式：

```
(contCoindSES p).delta 0 ≫ res_T μ_p 1 = res_T C 0 ≫ contDeltaZeroBar T
```

下游（`contM z = explicitRes1 (kummerClass π)`）需要在**元素**上用它，故本件取
`congrArg (fun f => ConcreteCategory.hom f w)` 落到逐点等式。

## 交付

| 声明 | 内容 |
|---|---|
| **`res_delta_zero_apply`** | ★★★★ `res_I(δ⁰_Γ w) = δ⁰_I(res_I w)`（逐点） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance instClosedInertiaLocS76R5 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
local instance instNormalInertiaLocS76R5 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- ★★★★ **`δ` 与限制的交换（逐点）**：

```
res_I ( δ⁰_Γ w ) = δ⁰_I ( res_I w )          w ∈ H⁰(Γ, C)
```

`Hyp551.contDelta_res_naturality`（`≫` 等式）取逐点。 -/
theorem res_delta_zero_apply
    (w : continuousCohomology 0
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p))) :
    (ConcreteCategory.hom
        (ContinuousCohomology.res (inertiaLoc F)
          (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) 1))
        (((contCoindSES (F := F) p).delta 0).hom w)
      = (ConcreteCategory.hom (contDeltaZeroBar (F := F) p (inertiaLoc F)))
          ((ConcreteCategory.hom
            (ContinuousCohomology.res (inertiaLoc F)
              (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) 0)) w) := by
  have h := contDelta_res_naturality (F := F) p (inertiaLoc F)
  have h2 := congrArg (fun f => (ConcreteCategory.hom f) w) h
  exact h2

end L20261018

#print axioms L20261018.res_delta_zero_apply
