import L20261018.Hyp737

/-!
# S66 R8：**补上 `explicitCoeff1_zero`**（库内缺件）—— 4d 代数收尾格**无条件化**

`Hyp738` 把 4d 的最后一行搭好了，但条件于一条库内缺口
（"零映射的 `explicitCoeff1` 是零"，`ExplicitFunctoriality.lean` 只有 `_comp`／`_id`）。
本件**补上它**，于是 4d 的代数部分**无开口**。

## 路线（`Hyp738` docstring 定下的那条，本轮落实）

1. `explicitCoeff1 f hf = explicitMap1 … (id) f hf …`（`:739` 定义式）；
2. `explicitCoeff1_mk`（`:746`，`[c] ↦ [cocyclesMap1 … c]`）把目标降到余链层；
3. `cocyclesMap1_apply`（`:258`）给出**逐点公式** `(cocyclesMap1 … c) h = f (c (φ h))`
   ⟹ `f = 0`（或 `f` 逐点为 0）时该 `Z1` 元素**就是零**；
4. `H1 = Z1 ⧸ B1.addSubgroupOf Z1` 且 **`H1pi : Z1 →+ H1` 是 `AddMonoidHom`**（`LowDegree.lean:836`）
   ⟹ 零余链的类为零（`map_zero`）。

**本轮的关键侦察**：第 4 步上一轮被误判为难点（曾想用 `Subsingleton.elim`，`H1` 显然不是单点集）；
正解是 `H1pi` 是 `AddMonoidHom` ⟹ `map_zero` 一行。**「卡住先查刻画引理」**（`D40`／`M11`）。

## 一般化

本件证的是**逐点形态**（`∀ x, g x = 0` ⟹ `explicitCoeff1 g = 0`），比 `g = 0` 更强，
正好覆盖 4d 需要的 `g := M' ∘ ι`（`M'.comp ι` 与字面 `0` 只是命题相等，不是定义相等 ——
这也正是 `Hyp738` 那条 `rw` 撞上 `motive is not type correct` 的原因）。
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

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type u} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]

/-- ★★★★★ **补库内缺口（逐点形态）**：若系数映射逐点为 `0`，则其 `explicitCoeff1` 是零映射。

比 `explicitCoeff1 zero = 0` 更强，且正好是 4d 需要的形状（`g = M' ∘ ι` 只是**逐点**为零）。 -/
theorem explicitCoeff1_eq_zero_of_apply_eq_zero (f : M →+[G] N) (hf : Continuous f)
    (h : ∀ x : M, f x = 0) :
    TauCeti.ContCohomology.explicitCoeff1 G M f hf = 0 := by
  refine AddMonoidHom.ext fun y => ?_
  induction y using QuotientAddGroup.induction_on with
    | H c =>
    rw [TauCeti.ContCohomology.explicitCoeff1_mk]
    have hz : TauCeti.ContCohomology.cocyclesMap1 G M G N (ContinuousMonoidHom.id G)
        (f : M →+ N) hf (fun g m => map_smul f g m) c = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      rw [TauCeti.ContCohomology.cocyclesMap1_apply]
      exact h _
    rw [hz]
    show TauCeti.ContCohomology.H1pi (G := G) (M := N) (0 : Z1 G N) = 0
    exact map_zero _

/-- ★★★★★ **补库内缺口**：零系数映射的 `explicitCoeff1` 是零映射（`STARTUP.md` 坑 17 的闭合）。 -/
theorem explicitCoeff1_zero :
    TauCeti.ContCohomology.explicitCoeff1 G M (0 : M →+[G] N) continuous_zero = 0 :=
  explicitCoeff1_eq_zero_of_apply_eq_zero (0 : M →+[G] N) continuous_zero (fun _ => rfl)

variable {P : Type u} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]

/-- ★★★★★ **4d 的代数收尾格（无条件）**：`M' ∘ ι = 0` ⟹ `coeffMap ι ≫ coeffMap M' = 0`。

证明：`explicitCoeff1_comp` 把复合收成 `explicitCoeff1 (M' ∘ ι)`，
再用**逐点**形态 `explicitCoeff1_eq_zero_of_apply_eq_zero`（避开 `Hyp738` 撞上的
`motive is not type correct`）。 -/
theorem coeffMap_comp_coeffMap_eq_zero (ι : M →+[G] N) (hι : Continuous ι)
    (M' : N →+[G] P) (hM' : Continuous M')
    (hzero : ∀ x : M, M' (ι x) = 0) :
    (TauCeti.ContCohomology.explicitCoeff1 G N M' hM').comp
      (TauCeti.ContCohomology.explicitCoeff1 G M ι hι) = 0 := by
  rw [← TauCeti.ContCohomology.explicitCoeff1_comp G M ι M' hι hM']
  exact explicitCoeff1_eq_zero_of_apply_eq_zero (M'.comp ι) (hM'.comp hι)
    (fun x => hzero x)

end L20261018

#print axioms L20261018.explicitCoeff1_eq_zero_of_apply_eq_zero
#print axioms L20261018.explicitCoeff1_zero
#print axioms L20261018.coeffMap_comp_coeffMap_eq_zero
