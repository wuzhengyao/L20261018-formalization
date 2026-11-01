import L20261018.Hyp493
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# S41 R5（动作 V2e）：**膨胀在 1 次是同构**（`H¹(N,M) = 0` 时）—— GS (6.15) 的第二个同构

## 本件在 GS §6.8 的哪一格

GS **Construction 6.8.1** 的第二步：由 `0 → A → M^G(A) → C → 0`（(6.14)）在 `H` 上的
长正合得 `H^j(H,C) = 0`（`j ≥ 1`；因 `H^j(H,M^G(A)) = 0` 且 `H^{j+1}(H,A) = 0`），
于是**膨胀** `H^{i-1}(G/H, C^H) → H^{i-1}(G,C)` 是同构。原文：

> This shows that for `i > 2` the assumptions of Proposition (inflation-restriction) are
> satisfied … and therefore the inflation maps `Inf : H^{i-1}(G/H,C^H) → H^{i-1}(G,C)` are
> isomorphisms.

本件把 `i = 2` 的那一格机检**（模 `H¹(N,M) = 0` 这一条假设）**：

```
Subsingleton (H¹(N,M))  ⟹  H¹(G⧸N, M^N) ≃+ H¹(G, M)     -- 显式模型
Subsingleton (H¹(N,M))  ⟹  H¹(G⧸N, M^N) ≃+ H¹(G, M)     -- 连续上同调（经库内 equiv）
```

## 机制（全部库内件）

| 件 | 内容 |
|---|---|
| `explicitInfl1 G M N` | 膨胀 `H1 (G ⧸ N) (M^N) →+ H1 G M` |
| `explicitInfl1_injective` | **单射**（库内） |
| `explicitInfRes_exact` | `range infl1 = ker res1`（膨胀-限制正合，库内） |
| `explicitRes1 G M N` | 限制 `H1 G M →+ H1 ↥N M` |
| `explicitH1AddEquivContinuousCohomology` | `H1 G M ≃+ H¹_cont(G,M)`（库内） |

⟹ `Subsingleton (H1 ↥N M)` ⟹ `res1 = 0` ⟹ `ker res1 = ⊤` ⟹ `range infl1 = ⊤` ⟹ 满射。
连同库内单射性即得双射。

## 诚实边界

* 本件的那条假设 `Subsingleton (H¹(H,M))` 在目标实例上是 **`H¹(I,C) = 0`**，
  而 `C = coker(μ_p ↪ Coind)` ⟹ `H¹(I,C) ≅ H²(I,μ_p)`（由 (6.14) 在 `I` 上的长正合）。
  故本件把 V2e **归约到 `H²(惯性群, μ_p) = 0`**（GS `cd_ℓ(I) ≤ 1`，GS A.6.9）——**唯一未解的数学输入**。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G]
variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable (N : Subgroup G) [N.Normal]
variable [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)]

/-- ★★★★ **膨胀是满射**（`H¹(N,M)` 单点时）：`range infl1 = ker res1 = ⊤`。 -/
theorem explicitInfl1_surjective_of_subsingleton (hN : Subsingleton (H1 ↥N M)) :
    Function.Surjective (TauCeti.ContCohomology.explicitInfl1 G M N) := by
  have hr : (TauCeti.ContCohomology.explicitInfl1 G M N).range = ⊤ := by
    rw [TauCeti.ContCohomology.explicitInfRes_exact G M N]
    rw [eq_top_iff]
    intro x _
    rw [AddMonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  intro y
  have hy : y ∈ (TauCeti.ContCohomology.explicitInfl1 G M N).range := by
    rw [hr]
    exact AddSubgroup.mem_top y
  exact hy

/-- ★★★★★ **膨胀在 1 次是双射**（`H¹(N,M)` 单点时）。 -/
theorem explicitInfl1_bijective_of_subsingleton (hN : Subsingleton (H1 ↥N M)) :
    Function.Bijective (TauCeti.ContCohomology.explicitInfl1 G M N) :=
  ⟨TauCeti.ContCohomology.explicitInfl1_injective G M N,
    explicitInfl1_surjective_of_subsingleton N hN⟩

/-- ★★★★★ **V2e（显式模型）**：`H¹(G⧸N, M^N) ≃+ H¹(G, M)`（`H¹(N,M)` 单点时）。 -/
noncomputable def explicitInfl1AddEquiv_of_subsingleton (hN : Subsingleton (H1 ↥N M)) :
    H1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M) ≃+ H1 G M :=
  AddEquiv.ofBijective (TauCeti.ContCohomology.explicitInfl1 G M N)
    (explicitInfl1_bijective_of_subsingleton N hN)

section Continuous

variable [IsTopologicalGroup G] [DiscreteTopology M]

/-- ★★★★★ **V2e（连续上同调）**：`H¹(G⧸N, M^N) ≃+ H¹(G, M)`（`H¹(N,M)` 单点时）。

这是 `Hyp493.h1_coker_addEquiv_h2` 的另一半：合起来给出
`H²(G,μ_p) ≃ H¹(G, C) ≃ H¹(G⧸N, C^N)`。 -/
noncomputable def h1_inflation_addEquiv_of_subsingleton
    (hN : Subsingleton (continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ ↥N M)).toModuleCat) :
    ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ (G ⧸ N)
        ↥(FixedPoints.addSubgroup (↥N) M))).toModuleCat ≃+
      ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ G M)).toModuleCat :=
  (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology (G ⧸ N)
      ↥(FixedPoints.addSubgroup (↥N) M)).symm.trans
    ((explicitInfl1AddEquiv_of_subsingleton (M := M) N
      (@Function.Injective.subsingleton _ _
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology ↥N M)
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology ↥N M).injective
        hN)).trans
      (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G M))

end Continuous

/-! ## 非空实例义务（L1 ＋ L10①）

假设 `Subsingleton (H¹(N,M))` **不是空类**：`M` 本身是单点模时它自动成立。 -/

/-- ★★★★ **非空见证**：`[Subsingleton M]` 时假设成立，定理给出真正的双射。 -/
noncomputable def explicitInfl1AddEquiv_of_subsingleton_witness [Subsingleton M] :
    H1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M) ≃+ H1 G M :=
  explicitInfl1AddEquiv_of_subsingleton (M := M) N inferInstance

/-! ## ★★★★★ 与 `Hyp493` 合成：**(6.15) 的完整形态** -/

section Composite

variable [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- ★★★★★★ **(6.15) 的完整形态**：**`H²(G, A) ≃+ H¹(G⧸H, C^H)`**，其中
`C = Coind_1^G A ⧸ im(A ↪ Coind_1^G A)`，唯一假设是 **`H¹(H, C) = 0`**。

这就是 GS Construction 6.8.1 的 `(6.15)` 端点：`∂²` 的**定义域与（未识别系数的）值域已接通**。 -/
noncomputable def h2_addEquiv_h1_fixedPoints
    (H : Subgroup G) [H.Normal]
    [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) (coindCoker (G := G) (A := A)))]
    (hH : Subsingleton ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ ↥H
      (coindCoker (G := G) (A := A)))).toModuleCat) :
    ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G A)).toModuleCat ≃+
      ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ (G ⧸ H)
        ↥(FixedPoints.addSubgroup (↥H) (coindCoker (G := G) (A := A))))).toModuleCat :=
  (h1_coker_addEquiv_h2 (G := G) (A := A)).symm.trans
    (h1_inflation_addEquiv_of_subsingleton (G := G) (M := coindCoker (G := G) (A := A)) H hH).symm

end Composite

end L20261018

#print axioms L20261018.h2_addEquiv_h1_fixedPoints
#print axioms L20261018.explicitInfl1AddEquiv_of_subsingleton_witness
#print axioms L20261018.explicitInfl1_surjective_of_subsingleton
#print axioms L20261018.explicitInfl1_bijective_of_subsingleton
#print axioms L20261018.explicitInfl1AddEquiv_of_subsingleton
#print axioms L20261018.h1_inflation_addEquiv_of_subsingleton
