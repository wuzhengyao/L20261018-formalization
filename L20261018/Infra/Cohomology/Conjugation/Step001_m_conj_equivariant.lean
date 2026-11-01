import L20261018.Infra.Cohomology.ResidueLES.Step033_restricted_coind_acyclic_nonempty
import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.ConnectingMap

/-!
# S47 R2：★★★ **`M` 的共轭等变性**（`∂₂` 第三因子的等变骨架）

`∂₂ := δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M`，其中
`M : Cᴵ → H¹(I, μ_p)` 必须是 **`(Γ⧸I)`-等变的**（GS (6.17) 之后的
`H^{i-1}(G/H, C^H) → H^{i-1}(G/H, H¹(H,A))`）。

`M` 的**载体**是 `Hyp549` 的 `contDeltaZeroBar I = (contDimShiftSES p I).delta 0`：
```
contDeltaZeroBar I : H⁰(I, C) → H¹(I, μ_p)          （C = CoindQuotient Γ ⊥ μ_p）
```
本件交付它作为**共轭作用**下的等变映射——即 GS 5.2 的 `lemma-conjugation-long-exact`
在 `M` 这一格上的落地。机件全在库内：`Conjugation/ConnectingMap.lean:106 delta_conjNormalMap`
（"共轭在正规子群上与连结映射交换"）。

**这一条把 `M` 的等变性从"要证"降成"要实例化"**（S47 R2 侦察结论）：`S46` 的
`(II)`/`M` 难点不在等变性本身，而在
① 把 `H⁰(I,C)` 换成载体 `contInvC = Cᴵ`（须 `explicitH0IsoContinuousCohomology`，见下节计划）；
② 把 `H¹(I,μ_p)` 换到可喂给 `H¹(Γ⧸I, ·)` 的**离散**载体（`H1 ↥I (ZMod p)`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [CompactSpace ↥I]

/-- ★★★★ **`M` 的共轭等变性**：`contDeltaZeroBar I` 与两端的共轭作用交换。

`g` 在 `H⁰(I, C)` 上作用经 `conjNormalMap I (contC p) g 0`，在 `H¹(I, μ_p)` 上经
`conjNormalMap I (ZMod p) g 1`。这正是 GS Lemma 5.2 给的"长正合列是 `G/H`-模的正合列"
在连结映射这一格上的内容。 -/
theorem contDeltaZeroBar_conjNormal (g : AbsoluteGaloisGroup F) :
    (contDimShiftSES (F := F) p I).delta 0 ≫
        ContinuousCohomology.conjNormalMap I (ZMod p) g 1 =
      ContinuousCohomology.conjNormalMap I (contC (F := F) p) g 0 ≫
        (contDimShiftSES (F := F) p I).delta 0 :=
  DiscreteShortExact.delta_conjNormalMap (contCoindSES (F := F) p) I g 0

/-- 同一件事的**应用形态**（下游 `map`/`coeffMap` 更好用）：`M` 把共轭类送到共轭类。 -/
theorem contDeltaZeroBar_conjNormal_apply (g : AbsoluteGaloisGroup F)
    (x : continuousCohomology 0
      (ofDiscreteModule ℤ ↥I (contC (F := F) p))) :
    ContinuousCohomology.conjNormalMap I (ZMod p) g 1
        ((contDimShiftSES (F := F) p I).delta 0 x) =
      (contDimShiftSES (F := F) p I).delta 0
        (ContinuousCohomology.conjNormalMap I (contC (F := F) p) g 0 x) := by
  have h := contDeltaZeroBar_conjNormal (F := F) p I g
  exact congrArg (fun (f : continuousCohomology 0
      (ofDiscreteModule ℤ ↥I (contC (F := F) p)) ⟶
        continuousCohomology 1 (ofDiscreteModule ℤ ↥I (ZMod p))) => f x) h

end L20261018

#print axioms L20261018.contDeltaZeroBar_conjNormal
#print axioms L20261018.contDeltaZeroBar_conjNormal_apply
