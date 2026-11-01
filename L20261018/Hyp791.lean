import L20261018.Hyp790

/-!
# S76 R4：**限制的两个桥** —— 显式 `explicitRes1` ↔ 连续 `res`（第 5 步 (a) 的第一块）

## 为什么需要

第 5 步（非零性）要先证 **`contM z` 是 `H¹(I, μ_p)` 的生成元**。路线（`GAP3-PLAN` §19.4）：

```
δ⁰(Inf z) = kummerClass π
  ⟹ res_I(e₁ (kummerClass π)) = contDeltaZeroBar I (res_I (e₀ (Inf z)))      ← Hyp551.contDelta_res_naturality
  = e₁ (contM z)                                                             ← Hyp576.contM_eq
  ⟹ contM z = explicitRes1 (kummerClass π)                                   ← 本件的桥 ＋ e₁ 单射
  ⟹ contM z = res₁V (kummerClass π)                                          ← Hyp746.res1V 定义
  ⟹ 生成元（Hyp746.res1V_kummerClass_eq ＋ Hyp780）
```

本件交付**第一块**：`e₁ ∘ explicitRes1 = res ∘ e₁`（库内 `explicitIso_res`
的 `AddEquiv` 形态）。

## 交付

| 声明 | 内容 |
|---|---|
| **`e1_explicitRes1`** | `e₁ (explicitRes1 x) = res_I (e₁ x)`（一般群情形 ＋ 惯性特化） |
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

/-! ## 1 一般形 -/

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- ★★★★ **`explicitRes1` 与连续 `res` 的交换**（`e₁ ∘ explicitRes1 = res ∘ e₁`）。

由库内 `explicitIso_res`（`CohomologyComparison.lean`）＋
`explicitH1IsoContinuousCohomology_hom_apply`，并把 `discreteH1Equiv` 展开（它是 `AddEquiv.refl`）。 -/
theorem e1_explicitRes1 (S : Subgroup G) [CompactSpace ↥S] (x : H1 G M) :
    explicitH1AddEquivContinuousCohomology (↥S) M (explicitRes1 G M S x)
      = (ConcreteCategory.hom
          (ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 1))
          (explicitH1AddEquivContinuousCohomology G M x) := by
  obtain ⟨x', rfl⟩ := (discreteH1Equiv G M).surjective x
  have h := explicitIso_res (G := G) (M := M) S x'
  rw [explicitH1IsoContinuousCohomology_hom_apply] at h
  rw [explicitH1IsoContinuousCohomology_hom_apply] at h
  simp only [discreteH1Equiv, AddEquiv.refl_symm] at h
  exact h.symm

end L20261018
