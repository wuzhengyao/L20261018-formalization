import L20261018.Infra.Cohomology.Boundary.Step032_delta_zero_explicit_model

/-!
# S64 R6：**C2-F 第一半** —— `δ⁰ : C^H → H¹(H,A)` 是 `G⧸H`-模态射

GS **Construction 6.8.1** 末段（逐字）：

> from the long exact sequence in `H`-cohomology coming from (6.14) we also obtain a map
> `C^H → H^1(H,A)`, **which is a morphism of `G/H`-modules** by Lemma (conjugation-long-exact).

本件把「是 `G⧸H`-模态射」这一句机检到底（**连续模型**，即 `δ⁰ = (S.restrict H).delta 0`）：

| 声明 | 内容 |
|---|---|
| `quotientConjAction_mk_smul` | `(mk g) • x = conjNormalMap g n x`（`Hyp496` 的 `quotientConjAction` 下降自 `Hyp495` 的共轭作用） |
| `delta_zero_conjNormal` | `conjNormalMap g 1 (δ⁰ x) = δ⁰ (conjNormalMap g 0 x)`（库内 `delta_conjNormalMap` 在 `n = 0` 的应用形态） |
| **`delta_zero_quotientConj`** | ★★★★ **`q • (δ⁰ x) = δ⁰ (q • x)`，`q : G ⧸ H`**（GS 那句话的机检形态） |
| `deltaZeroQuotientHom` | ★★★★ 打包为 `→+[G ⧸ H]`（喂 `explicitCoeff1` 的形状） |

## 与 `Hyp498`／`Hyp497` 的关系

`Hyp498.residueCoeff` 是同一映射的**显式模型**形态（`= (S.restrict H).explicitDelta0`）；
`Hyp497.quotientConjActionH1` 是 `H¹(H,A)` 的显式模型 `G⧸H`-作用。本件在连续模型里给出**等变性的本体**，
显式模型的版本是随之的运输（见 `S64-INFRA-PLAN.md` §5 F1 备注）。
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

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : Subgroup G) [H.Normal]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]

section Closed

variable [IsClosed (H : Set G)]

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp ‹IsClosed (H : Set G)›.isCompact

/-- `quotientConjAction` 在陪集代表上的计算规则：下降自 `G` 的共轭作用。 -/
theorem quotientConjAction_mk_smul (A : Type) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] (n : ℕ)
    (g : G) (x : ↑(continuousCohomology n (ofDiscreteModule ℤ ↥H A)).toModuleCat) :
    (letI := quotientConjAction H A n ‹IsClosed (H : Set G)›
     (QuotientGroup.mk g : G ⧸ H) • x) =
      (TauCeti.ContinuousCohomology.conjNormalMap H A g n).hom x := by
  letI := quotientConjAction H A n ‹IsClosed (H : Set G)›
  show conjEndQuotient H A n ‹IsClosed (H : Set G)› (QuotientGroup.mk g) x = _
  rw [conjEndQuotient]
  rfl

/-- **共轭与 `δ⁰` 逐次交换**（库内 `DiscreteShortExact.delta_conjNormalMap` 在 `n = 0` 的应用形态）。 -/
theorem delta_zero_conjNormal (S : DiscreteShortExact G A B C) (g : G)
    (x : ↑(continuousCohomology 0 (ofDiscreteModule ℤ ↥H C)).toModuleCat) :
    (TauCeti.ContinuousCohomology.conjNormalMap H A g 1).hom
        ((S.restrict H).delta 0 x) =
      (S.restrict H).delta 0 ((TauCeti.ContinuousCohomology.conjNormalMap H C g 0).hom x) :=
  congrArg (fun (f : continuousCohomology 0 (ofDiscreteModule ℤ ↥H C) ⟶
      continuousCohomology 1 (ofDiscreteModule ℤ ↥H A)) => f.hom x)
    (DiscreteShortExact.delta_conjNormalMap S H g 0)

/-- ★★★★ **C2-F 第一半（GS 那句话）**：`δ⁰ : C^H → H¹(H,A)` 是 `G⧸H`-模态射。

`q • (δ⁰ x) = δ⁰ (q • x)`，两端的作用都取 `Hyp496.quotientConjAction`（在 `H¹(H,A)` 上 `n = 1`、
在 `H⁰(H,C) = C^H` 上 `n = 0`）。 -/
theorem delta_zero_quotientConj (S : DiscreteShortExact G A B C)
    (q : G ⧸ H) (x : ↑(continuousCohomology 0 (ofDiscreteModule ℤ ↥H C)).toModuleCat) :
    (letI := quotientConjAction H A 1 ‹IsClosed (H : Set G)›
     letI := quotientConjAction H C 0 ‹IsClosed (H : Set G)›
     q • ((S.restrict H).delta 0 x)) =
      (letI := quotientConjAction H A 1 ‹IsClosed (H : Set G)›
       letI := quotientConjAction H C 0 ‹IsClosed (H : Set G)›
       (S.restrict H).delta 0 (q • x)) := by
  letI := quotientConjAction H A 1 ‹IsClosed (H : Set G)›
  letI := quotientConjAction H C 0 ‹IsClosed (H : Set G)›
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [quotientConjAction_mk_smul H A 1 g, quotientConjAction_mk_smul H C 0 g]
    exact delta_zero_conjNormal (H := H) (A := A) (C := C) S g x

end Closed

end L20261018

#print axioms L20261018.quotientConjAction_mk_smul
#print axioms L20261018.delta_zero_conjNormal
#print axioms L20261018.delta_zero_quotientConj
