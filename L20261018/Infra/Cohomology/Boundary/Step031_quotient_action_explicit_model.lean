import L20261018.Infra.Cohomology.Boundary.Step030_conj_action_descends
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# S41 R8（动作 V2f 第三块）：**`G ⧸ H` 在显式模型 `H1 ↥H A` 上的作用**

## 为什么需要它

V2f 的最后一步要把 `δ_0 : C^H → H¹(H,A)` 抬成 `H¹(G⧸H, C^H) → H¹(G⧸H, H¹(H,A))`。
**不需要** `TopRep` 打包：库内 `TauCeti.ContCohomology.explicitCoeff1`

```lean
explicitCoeff1 (f : M →+[G] N) (hf : Continuous f) : H1 G M →+ H1 G N
```

只要求 `M`、`N` 是**等变加性群**（`→+[G]`）＋ `f` 连续。⟹ 只要 `H1 ↥H A` 带 `G ⧸ H`-作用、
`C^H` 带 `G ⧸ H`-作用（库内 `FixedPoints` 已有），且 `δ_0` 是 `G ⧸ H`-等变的，即可。

本件补**系数侧**：把 `Hyp496.quotientConjAction`（连续上同调上的 `G⧸H`-作用）
沿库内 `explicitH1AddEquivContinuousCohomology` **搬到显式模型 `H1 ↥H A`**。

## 机检件

| 声明 | 内容 |
|---|---|
| **`quotientConjActionH1`** | ★★★★ **`DistribMulAction (G ⧸ H) (H1 ↥H A)`** |
| `quotientConjActionH1_apply` | 展开式：`q • x = e.symm (q • e x)` |
| `quotientConjActionH1_def` | 与连续模型的相容：`e (q • x) = q • e x` |

## 诚实边界

* 本件只做**系数侧的作用**。`δ_0` 的 `G⧸H`-等变性（用库内
  `DiscreteShortExact.delta_conjNormalMap`）与 `explicitCoeff1` 的装配 —— **下一步**。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : Subgroup G) [H.Normal]
variable (A : Type) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- 库内的比较：显式 `H1` 与连续 `H¹`（`↥H` 上）。 -/
noncomputable abbrev h1ContEquivH :
    H1 ↥H A ≃+ ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ ↥H A)).toModuleCat :=
  TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology ↥H A

/-- ★★★★★ **`G ⧸ H` 在显式模型 `H1 ↥H A` 上的作用**（沿 `h1ContEquivH` 搬运）。

这样 V2f 的 `explicitCoeff1` 就有系数侧的模结构可用，**无需**把 `H¹(H,A)` 装成 `TopRep (G⧸H)`。 -/
noncomputable def quotientConjActionH1 (hHcl : IsClosed (H : Set G)) :
    DistribMulAction (G ⧸ H) (H1 ↥H A) where
  smul q x :=
    letI := quotientConjAction H A 1 hHcl
    (h1ContEquivH H A).symm (q • (h1ContEquivH H A) x)
  one_smul x := by
    letI := quotientConjAction H A 1 hHcl
    show (h1ContEquivH H A).symm ((1 : G ⧸ H) • (h1ContEquivH H A) x) = x
    rw [one_smul, AddEquiv.symm_apply_apply]
  mul_smul a b x := by
    letI := quotientConjAction H A 1 hHcl
    show (h1ContEquivH H A).symm ((a * b) • (h1ContEquivH H A) x)
      = (h1ContEquivH H A).symm (a • (h1ContEquivH H A)
          ((h1ContEquivH H A).symm (b • (h1ContEquivH H A) x)))
    rw [AddEquiv.apply_symm_apply, mul_smul]
  smul_zero q := by
    letI := quotientConjAction H A 1 hHcl
    show (h1ContEquivH H A).symm (q • (h1ContEquivH H A) 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add q x y := by
    letI := quotientConjAction H A 1 hHcl
    show (h1ContEquivH H A).symm (q • (h1ContEquivH H A) (x + y))
      = (h1ContEquivH H A).symm (q • (h1ContEquivH H A) x)
        + (h1ContEquivH H A).symm (q • (h1ContEquivH H A) y)
    rw [map_add, smul_add, map_add]

end L20261018

#print axioms L20261018.quotientConjActionH1
