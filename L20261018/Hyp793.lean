import L20261018.Hyp792

/-!
# S77 R1：第 5 步 (a) **第三块** —— `res_I (e₀ (Inf z)) = e₀_I z`

## 靶子（`PROMPT-S77` §1.1）

```
res_I ( e₀^Γ ( explicitInfl0 z ) )  =  e₀^I z        （H⁰ 上「膨胀后限制 = 原样」）
```

已实测**非 `rfl`**（`probe/SG.lean`）——两条路径途经不同投影。

## 破解（M69：库内已有，按内容式关键词 grep，别按名字猜）

`TauCeti.ContCohomology.explicitH0Iso_res`（`ContCohomology/ContinuousCohomologyIso.lean:272`）
**就是**零次数的限制运输：

```
res S (ofDiscreteModule ℤ G M) 0 ( (e₀^G).hom x ) = (e₀^S).hom ( explicitRes0 G M S x )
```

它一行把靶子归约到 `explicitRes0 (explicitInfl0 z) = z.1`（膨胀后限制在原载体上不动，
两侧 `coe_explicitRes0`／`coe_explicitInfl0` 都是 `rfl` 级）。

**注意**：`explicitH0Iso_res` 是**零度**的那条（`Transport` 段）；
一度的是 `explicitIso_res`（`Hyp791` 已用），二者同族不同件。

## 交付

| 声明 | 内容 |
|---|---|
| `explicitRes0_explicitInfl0` | ★★★ `explicitRes0 G M N (explicitInfl0 G M N z) = z.1`（一般群） |
| **`e0_res_infl`** | ★★★★ `res_N (e₀^G (Inf z)) = e₀^N z`（一般群，本步主桥） |
| **`h0Emb_res_infl`** | ★★★★ 惯性特化（`Γ`／`I`／`contC p`），即 `probe/SG.lean` 的靶子形态 |
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

/-! ## 1 一般形（纯 `H⁰` 载体层）：膨胀后限制＝原样 -/

section Coefficients

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- ★★★ **`explicitRes0 ∘ explicitInfl0 = id`**（在 `M^N` 载体上）。

两侧 `coe_explicitRes0`（`:474`）与 `coe_explicitInfl0`（`Inflation/Basic.lean:151`）都只声明
「底层系数不动」，故 `Subtype.ext` ＋ 两次 `rw` 即闭。 -/
theorem explicitRes0_explicitInfl0
    (z : H0 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    explicitRes0 G M N (explicitInfl0 G M N z) = (z.1 : FixedPoints.addSubgroup N M) := by
  refine Subtype.ext ?_
  rw [coe_explicitRes0, coe_explicitInfl0]

end Coefficients

/-! ## 2 主桥（一般群）：`res` 与 `explicitInfl0` 在零次数上相容 -/

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- ★★★★★ **零次数「膨胀后限制 = 原样」**（连续侧）。

`explicitH0Iso_res`（库内 `ContinuousCohomologyIso.lean:272`）给出

```
res N (ofDiscreteModule ℤ G M) 0 ((e₀^G).hom x) = (e₀^N).hom (explicitRes0 G M N x)
```

取 `x = explicitInfl0 z`，再用 `explicitRes0_explicitInfl0` 化掉 `explicitRes0`。 -/
theorem e0_res_infl
    (z : H0 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    ContinuousCohomology.res N (ofDiscreteModule ℤ G M) 0
        ((explicitH0IsoContinuousCohomology G M).hom (explicitInfl0 G M N z)) =
      (explicitH0IsoContinuousCohomology ↥N M).hom (z.1 : FixedPoints.addSubgroup N M) := by
  rw [explicitH0Iso_res, explicitRes0_explicitInfl0]

end Main

/-! ## 3 惯性特化（下游 `contM z = explicitRes1 (kummerClass π)` 要的形状） -/

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- 技术实例：`I = inertiaLoc F` 闭。 -/
local instance instClosedInertiaLocS77 :
    IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F

/-- 技术实例：`inertiaLoc F` 正规。 -/
local instance instNormalInertiaLocS77 : (inertiaLoc F).Normal := normal_inertiaLoc F

/-- ★★★★★ **`probe/SG.lean` 的靶子**：`res_I (e₀ (Inf z)) = e₀_I z`（`z : H⁰(Γ⧸I, Cᴵ)`）。

逐字是 `PROMPT-S77` §1.1 的那条桥；`exact e0_res_infl ...` 一行。 -/
theorem h0Emb_res_infl
    (z : ↥(H0 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (contC (F := F) p)))) :
    (ConcreteCategory.hom (ContinuousCohomology.res (inertiaLoc F)
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) 0))
      ((ConcreteCategory.hom
          (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom)
        (explicitInfl0 (AbsoluteGaloisGroup F) (contC (F := F) p) (inertiaLoc F) z)) =
      (ConcreteCategory.hom
          (explicitH0IsoContinuousCohomology (↥(inertiaLoc F)) (contC (F := F) p)).hom)
        (z : ↥(H0 (↥(inertiaLoc F)) (contC (F := F) p))) :=
  e0_res_infl (G := AbsoluteGaloisGroup F) (M := contC (F := F) p) (inertiaLoc F) z

end L20261018
