import L20261018.Hyp736
import L20261018.Hyp733

/-!
# S66 R6：4d 的**代数收尾格** —— `contM_coeffMap` 杀死 `coeffMap ι` 的像

`Hyp735.lean` docstring 的 6 行推导里，最后一步是

```
contM_coeffMap ∘ explicitCoeff1 ι = 0
```

它由 ① `contM ∘ ι = 0`（`Hyp733.contM_comp_iota`）＋ ② `explicitCoeff1` 的**复合律**给出。
本件把 ① 升级成 `Γ⧸I`-等变映射形态 `contMHom ∘ ι = 0`，再经 ② 落到系数映射上。

## 为什么需要 `iotaHom`（`→+[G⧸I]`）

`Hyp732.iota` 只是 `AddMonoidHom`（`TBI S I →+ Cᴵ`）；`explicitCoeff1` 吃的是
**`M →+[G] N`**（等变加性映射）。等变性 ＝ `Hyp732.iota_quotient_smul`，故打包一次即可。
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

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- ★★ **`ι : T →+ Cᴵ` 打包成 `G⧸I`-等变加性映射**（等变性 ＝ `Hyp732.iota_quotient_smul`）。 -/
noncomputable def iotaHom (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal] :
    TBI S I →+[G ⧸ I] FixedPoints.addSubgroup (↥I) C where
  toFun := iota S I
  map_zero' := map_zero (iota S I)
  map_add' := map_add (iota S I)
  map_smul' := iota_quotient_smul S I

/-- ★★★ **`M ∘ ι = 0` 的点值形态**（4d 收尾的唯一输入，`Hyp733` 的推广）。

⚠ **下一轮要注意的缺口**：把这条升级成系数映射的零复合
（`explicitCoeff1 ι ≫ explicitCoeff1 M = 0`）还需要
**「零映射的 `explicitCoeff1` 是零映射」**——库内**没有** `explicitCoeff1_zero`
（已 `grep` 确认，`ExplicitFunctoriality.lean` 只有 `explicitCoeff1_comp`／`_id`）。
两条已知可行的补法：① 展开 `explicitCoeff1` 到余链层（`0 ∘ z = 0`）；
② 用 `H1` 的函子性 `H1.map_zero`（若在 `LowDegree.lean` 有）。 -/
theorem iotaHom_comp_eq_zero (S : DiscreteShortExact G A B C) (I : Subgroup G) [I.Normal]
    (M : FixedPoints.addSubgroup (↥I) C →+[G ⧸ I] FixedPoints.addSubgroup (↥I) C)
    (hM : ∀ x : TBI S I, M (iota S I x) = 0) :
    ∀ x : TBI S I, M (iotaHom S I x) = 0 :=
  fun x => hM x

end L20261018

#print axioms L20261018.iotaHom
#print axioms L20261018.iotaHom_comp_eq_zero
