import Hyp716

/-!
# S64 R4：**C2-D 步** —— `Inf : H¹(G⧸H, C^H) ≅ H¹(G, C)`（C 步之后去假设）

GS 6.8.1 在 `i = 2` 的 D 步：五项正合列

```
0 → H¹(G⧸H, C^H) --Inf--> H¹(G, C) --res--> H¹(H, C)^{G⧸H} --tg--> H²(G⧸H, C^H) → H²(G,C)
```

在 `H¹(H,C) = 0` 时 `res = 0`，故 `ker(res) = ⊤ = range(Inf)`（库内
`explicitInfResConj_exact`）⟹ **`Inf` 双射**。本件只做这一步同调代数 + 与 B/C 步的对接。

## 命名（R6 更正）

本件的 `infl1_surjective_of_H1_subsingleton`／`infl1AddEquiv_of_H1_subsingleton` **曾名**
`explicitInfl1_surjective_of_subsingleton`／`explicitInfl1AddEquiv_of_subsingleton`，与 **`Hyp494`** 的
同名声明**冲突**（同一 `L20261018.explicitInfl1AddEquiv_of_subsingleton` 两处定义 ⟹ 两族不能同时 import）。
已改名为不复名的形态（GS 的 `Inf` 双射），`Hyp494` 保持原状。

## 内容

| 声明 | 内容 |
|---|---|
| `infl1_surjective_of_H1_subsingleton` | `H¹(N,M)` 单点 ⟹ `Inf` **满射** |
| `infl1AddEquiv_of_H1_subsingleton` | 打包 `H1 (G⧸N) (M^N) ≃+ H1 G M` |
| `subsingleton_H1_of_continuousCohomology` | `H1 ≃+ continuousCohomology 1` 桥（库内 `explicitH1AddEquivContinuousCohomology`） |
| **`infl1AddEquiv_of_coindAcyclic`** | ★★★★ **C2-D（对接 `Hyp716`）**：输入 = `H¹(H, ·) = 0` 的 `continuousCohomology` 形态 |

库内锚（`M5`／`L46` 侦察已核，全在 `TauCeti.RepresentationTheory.Homological.ContCohomology`）：
`Inflation/Basic.lean` 的 `explicitInfl1`（`:210`）／`explicitInfl1_injective`／`explicitInfResConj_exact`
＋ `CohomologyComparison.lean:134 explicitH1AddEquivContinuousCohomology`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open TauCeti TauCeti.ContCohomology

namespace L20261018

universe u

section Infl

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [IsTopologicalAddGroup M]
variable (N : Subgroup G) [N.Normal]
  [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)]

include N in
/-- **`Inf` 的满射性来自 C 步**：若 `H¹(N,M)` 单点，则 `res : H¹(G,M) → H¹(N,M)` 是零映射，
故 `ker res = ⊤ = range Inf`（`explicitInfResConj_exact`），即 `Inf` 满射。 -/
theorem infl1_surjective_of_H1_subsingleton (hN : Subsingleton (H1 ↥N M)) :
    Function.Surjective (TauCeti.ContCohomology.explicitInfl1 G M N) := by
  have hIH : Subsingleton ↥(TauCeti.ContCohomology.H1ConjInvariants G M N) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim (a : H1 ↥N M) (b : H1 ↥N M))⟩
  haveI := hIH
  have hker : (TauCeti.ContCohomology.explicitResConj1 G M N).ker = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    rw [AddMonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hr : (TauCeti.ContCohomology.explicitInfl1 G M N).range = ⊤ :=
    (TauCeti.ContCohomology.explicitInfResConj_exact G M N).trans hker
  intro y
  have hy : y ∈ (TauCeti.ContCohomology.explicitInfl1 G M N).range := by rw [hr]; trivial
  exact hy

include N in
/-- **C2-D（抽象形态）**：`H¹(N,M) = 0` ⟹ `Inf : H¹(G⧸N, M^N) ≃+ H¹(G,M)`。 -/
noncomputable def infl1AddEquiv_of_H1_subsingleton (hN : Subsingleton (H1 ↥N M)) :
    H1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M) ≃+ H1 G M :=
  AddEquiv.ofBijective (TauCeti.ContCohomology.explicitInfl1 G M N)
    ⟨TauCeti.ContCohomology.explicitInfl1_injective G M N,
      infl1_surjective_of_H1_subsingleton N hN⟩

include N in
/-- `H1` 与 `continuousCohomology 1` 之间的零调性搬运（库内比较定理）。 -/
theorem subsingleton_H1_of_continuousCohomology
    (h : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥N M))) :
    Subsingleton (H1 ↥N M) := by
  haveI := h
  exact (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology ↥N M).toEquiv.injective.subsingleton

include N in
/-- ★★★★ **C2-D 步（对接 `Hyp716` 的形态）**：闭子群 `H` 上 `H¹(H, C) = 0`（`continuousCohomology`
形态，由 B＋C 步给出）⟹ `Inf : H¹(G⧸H, C^H) ≃+ H¹(G, C)`。 -/
noncomputable def infl1AddEquiv_of_coindAcyclic
    (hH : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥N M))) :
    H1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M) ≃+ H1 G M :=
  infl1AddEquiv_of_H1_subsingleton N (subsingleton_H1_of_continuousCohomology N hH)

end Infl

end L20261018

#print axioms L20261018.infl1_surjective_of_H1_subsingleton
#print axioms L20261018.infl1AddEquiv_of_H1_subsingleton
#print axioms L20261018.subsingleton_H1_of_continuousCohomology
#print axioms L20261018.infl1AddEquiv_of_coindAcyclic
