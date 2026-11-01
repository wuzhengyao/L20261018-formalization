import Hyp234

/-!
# R1105（**共轭作用的地基三条：底层映射公式 ＋ `conjSubtypeHom` 的乘法 ＋ `conjMap` 的因子性方向**）

## 背景

`PLAN-R2` §H-12：具名假设已修正为 `innerConjTrivialIn`（`g : S`）。
要把 `H¹(S,A)` 变成 `G ⧸ S`-模，还需 **`conjMap` 的因子性**（`groupCohomology.map_comp`）。
而任何合成的第一步是**底层映射公式** —— R1102 曾试图用 `show … _ _ (A.ρ g) _` 得到它而失败；
本轮查明**纯 `rfl` 即过**（`intertwiningMap_of_isIntertwiningMap` 的 `toLinearMap` 就是 `A.ρ g`）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`conjCoeffHom_apply`** | ★ 底层映射公式 `(conjCoeffHom A S g) a = A.ρ g a`（`rfl`） |
| **`conjSubtypeHom_one`** | `conjSubtypeHom S 1 = MonoidHom.id S` |
| **`conjSubtypeHom_mul`** | ★ **反**同态性：`(conjSubtypeHom S g).comp (conjSubtypeHom S h) = conjSubtypeHom S (h * g)` |
| **`conjMap_comp`** | ★ 因子性（`map_comp` 特化）：`conjMap g ≫ conjMap h` 的左边形式 ⟹ `g ↦ conjMap g` 是**反**同态 |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **底层映射公式**：共轭系数映射的作用就是 `A.ρ g`。 -/
@[simp]
theorem conjCoeffHom_apply (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) (a : A.V) :
    (conjCoeffHom A S g) a = A.ρ g a :=
  (rfl)

/-- `conjSubtypeHom` 在 `g = 1` 处是恒等同态。 -/
theorem conjSubtypeHom_one (S : Subgroup G) [S.Normal] :
    conjSubtypeHom S 1 = MonoidHom.id S := by
  ext s
  simp [conjSubtypeHom_coe]

/-- ★ **`conjSubtypeHom` 的反同态性**：`conj_g ∘ conj_h = conj_{h * g}`。 -/
theorem conjSubtypeHom_mul (S : Subgroup G) [S.Normal] (g h : G) :
    (conjSubtypeHom S g).comp (conjSubtypeHom S h) = conjSubtypeHom S (h * g) := by
  ext s
  simp only [MonoidHom.comp_apply, conjSubtypeHom_coe]
  group

/-- ★ **`conjMap` 的因子性（`Gᵐᵒᵖ`-方向）**：`groupCohomology.map_comp` 的直接特化。
配合 `conjSubtypeHom_mul`（`conj_g ∘ conj_h = conj_{h*g}`），此式表明 `g ↦ conjMap A S g` 是
**反**同态（`Gᵐᵒᵖ → Aut`），这正是 `G ⧸ S`-模结构所需的因子性内容。 -/
theorem conjMap_comp (A : Rep k G) (S : Subgroup G) [S.Normal] (g h : G) (n : ℕ) :
    groupCohomology.map ((conjSubtypeHom S g).comp (conjSubtypeHom S h))
        ((Rep.resFunctor (conjSubtypeHom S h)).map (conjCoeffHom A S g) ≫
          conjCoeffHom A S h) n
      = conjMap A S g n ≫ conjMap A S h n :=
  groupCohomology.map_comp _ _ _ _ n

end L20261018

#print axioms L20261018.conjCoeffHom_apply
#print axioms L20261018.conjSubtypeHom_one
#print axioms L20261018.conjSubtypeHom_mul
#print axioms L20261018.conjMap_comp
