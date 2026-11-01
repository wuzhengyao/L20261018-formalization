import L20261018.Hyp236

/-!
# R1108（**★★★ (R2)-1 第二块：`δ₀` 在共轭作用下的自然性 —— GS `lemma-conjugation-long-exact` 的抽象侧**）

## 目标

GS 6.8.5（`raw/GilleSzamuely2017.tex:9497`）说 `C^H → H¹(H,A)` 是 **`G/H`-模映射**，
依据是 GS `lemma-conjugation-long-exact`（`raw/…:3573`）：

> The long exact sequence `… H⁰(H,C) → H¹(H,A) → …` **is an exact sequence of `G/H`-modules**,
> where the groups `H^i(H,A)` are equipped with the conjugation action.
> **Proof.** This follows immediately from the fact that the conjugation action … induces an
> isomorphism of the exact sequence of complexes `0 → Hom_H(P_•,A) → …` onto itself.

**照原文**：本轮就把「共轭作用诱导余链短复形的**自同态**」机检成
`Hyp237.conjCochainsSES`，再用 mathlib 的
`HomologicalComplex.HomologySequence.δ_naturality` 得自然性方块 `deltaZero_conj`。

## 数学（为什么是「自同态」而不是「换群」）

`conjCoeffHom A S g : res (conj_g) (res S.subtype A) ⟶ res S.subtype A`（底层 `A.ρ g`）。
`groupCohomology.cochainsMap (conj_g) (conjCoeffHom A S g)` 的源/靶复形**都是**
`inhomogeneousCochains (res S.subtype A)`（因为 `cochainsMap f φ` 的两个复形分别由
`A : Rep k H`、`B : Rep k G` 给出，此处 `H = G = S`）⟹ 它是该复形的**自同态**。
这正是 GS 说的「诱导自身的一个同构」。

## 🔧 本轮的三处工艺发现（都是「静默失败」型，登记供后续复用）

1. **`ShortComplex.map` 的对象不句法归约** ⟹ 在 `X.map F` 上做 `hom_ext`／`rw` 时，
   Lean 报「target expression is not type-correct under the `implicit` transparency level」，
   于是 `simp`／`rw` **静默不推进**（`simp made no progress`），而 `comp_f` 明明句法在场。
   **破法**：自己用 `ShortComplex.mk` 把复形**写成句法形式**（`dimShiftSES_S`／`cochainSES_S`），
   并机检它们与库内形式**逐字 `rfl` 相等**（`dimShiftSES_S_eq`／`cochainSES_S_eq`）。
2. **`change` 是解开 `rfl`-可归约对象的好工具**：`Rep.resMap f X` 与
   `(Rep.resFunctor f).map X` 句法不同，`rw [← Functor.map_comp]` 找不到模式；
   先 `change` 成 `Functor.map` 形式即过。
3. **`ext a` 会连带 `funext`**：当靶模是函数空间（`coindBot` 的载体）时，`ext a` 之后仍有
   一个隐式变元 ⟹ 改用 `refine LinearMap.ext fun a => ?_` 再 `exact LinearMap.congr_fun …`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`dimShiftSES_S`** | 限制后维数平移 SES 的**句法**形式（对象 `Rep.res S.subtype _`） |
| **`dimShiftSES_S_eq`** | 与库内 `(dimensionShiftUpSES A).map (resFunctor S.subtype)` **逐字 `rfl`** 相等 |
| **`cochainSES_S`** | 余链层级的**句法**形式（对象 `inhomogeneousCochains (Rep.res S.subtype _)`） |
| **`cochainSES_S_eq`** | 与 `(dimShiftSES_S A S).map (cochainsFunctor k S)` **逐字 `rfl`** 相等 |
| **`cochainSES_S_shortExact`** | 短正合性（承自 `Rep.dimensionShiftUpSES_res_shortExact`） |
| **`conjCochainsSES`** | ★★ **共轭自同态**（`τ₁/τ₂/τ₃` 都是 `conjCoeffHom`） |
| **`deltaZero_conj`** | ★★★ **自然性方块**：`δ₀ ≫ conjMap A = conjMap C ≫ δ₀` |

**下一轮**：把 `deltaZero_conj` 组装成 `δ₀` 的 `Rep k (G ⧸ S)`-线性（经 `H0Iso`），
再作 `H¹(G⧸S, C^S) → H¹(G⧸S, H¹(S,A))`，得 `deltaTwo`。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- 限制后维数平移短复形的**句法**形式：三个对象分别是
`Rep.res S.subtype A`、`Rep.res S.subtype (coindBot k G A.V)`、`Rep.res S.subtype (dimensionShiftUp A)`。
（用 `abbrev` 使 `.X₁` 在 `reducible` 透明度下即归约。） -/
noncomputable abbrev dimShiftSES_S (A : Rep k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (Rep k S) :=
  ShortComplex.mk (Rep.resMap S.subtype (Rep.coindBotUnit A))
    (Rep.resMap S.subtype (Rep.dimensionShiftUpπ A))
    (by
      change (Rep.resFunctor S.subtype).map (Rep.coindBotUnit A) ≫
        (Rep.resFunctor S.subtype).map (Rep.dimensionShiftUpπ A) = 0
      rw [← Functor.map_comp, Rep.coindBotUnit_comp_dimensionShiftUpπ, Functor.map_zero])

/-- `dimShiftSES_S` 与库内形式**逐字相等**（`rfl`）。 -/
theorem dimShiftSES_S_eq (A : Rep k G) (S : Subgroup G) [S.Normal] :
    dimShiftSES_S A S = (Rep.dimensionShiftUpSES A).map (Rep.resFunctor S.subtype) := rfl

/-- 余链层级的**句法**形式：对象是 `inhomogeneousCochains (Rep.res S.subtype _)`。 -/
noncomputable abbrev cochainSES_S (A : Rep k G) (S : Subgroup G) [S.Normal] :
    ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk
    (groupCohomology.cochainsMap (MonoidHom.id S) (dimShiftSES_S A S).f)
    (groupCohomology.cochainsMap (MonoidHom.id S) (dimShiftSES_S A S).g)
    (by
      change (groupCohomology.cochainsFunctor k S).map (dimShiftSES_S A S).f ≫
        (groupCohomology.cochainsFunctor k S).map (dimShiftSES_S A S).g = 0
      rw [← Functor.map_comp, (dimShiftSES_S A S).zero, Functor.map_zero])

/-- `cochainSES_S` 与 `(dimShiftSES_S A S).map (cochainsFunctor k S)` **逐字相等**（`rfl`）。 -/
theorem cochainSES_S_eq (A : Rep k G) (S : Subgroup G) [S.Normal] :
    cochainSES_S A S = (dimShiftSES_S A S).map (groupCohomology.cochainsFunctor k S) := rfl

/-- `cochainSES_S` 短正合（承自 `Rep.dimensionShiftUpSES_res_shortExact`）。 -/
theorem cochainSES_S_shortExact (A : Rep k G) (S : Subgroup G) [S.Normal] :
    (cochainSES_S A S).ShortExact :=
  groupCohomology.map_cochainsFunctor_shortExact
    (Rep.dimensionShiftUpSES_res_shortExact A S.subtype)

/-- ★★ **共轭自同态**：短复形 `0 → A|_S → M|_S → C|_S → 0`（余链层级）的**自同态**，
三个分量都是 `conjCoeffHom`（底层 `ρ g`）。GS `lemma-conjugation-long-exact` 的证明内容即此：
「the conjugation action … induces an isomorphism of the exact sequence of complexes onto itself」。 -/
noncomputable def conjCochainsSES (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) :
    cochainSES_S A S ⟶ cochainSES_S A S where
  τ₁ := groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g)
  τ₂ := groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom (Rep.coindBot k G A.V) S g)
  τ₃ := groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom (Rep.dimensionShiftUp A) S g)
  comm₁₂ := by
    rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
    refine groupCohomology.cochainsMap_congr rfl ?_
    refine LinearMap.ext fun a => ?_
    exact LinearMap.congr_fun ((Rep.coindBotUnit A).hom.isIntertwining' g) a
  comm₂₃ := by
    rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
    refine groupCohomology.cochainsMap_congr rfl ?_
    refine LinearMap.ext fun a => ?_
    exact LinearMap.congr_fun ((Rep.dimensionShiftUpπ A).hom.isIntertwining' g) a

/-- `conjCochainsSES` 的 `τ₁` 就是 `conjMap A S g 1` 的余链映射（记录定义）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:3585 quote="This follows immediately from the fact that the conjugation action as defined above induces an isomorphism of the exact sequence of complexes"
theorem conjCochainsSES_τ₁ (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) :
    (conjCochainsSES A S g).τ₁
      = groupCohomology.cochainsMap (conjSubtypeHom S g) (conjCoeffHom A S g) :=
  (rfl)

/-- `conjCochainsSES` 的 `τ₃`。 -/
theorem conjCochainsSES_τ₃ (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) :
    (conjCochainsSES A S g).τ₃
      = groupCohomology.cochainsMap (conjSubtypeHom S g)
        (conjCoeffHom (Rep.dimensionShiftUp A) S g) :=
  (rfl)

/-- ★★★ **自然性方块（GS `lemma-conjugation-long-exact` 的抽象侧核心）**：

`δ₀ ≫ conjMap A S g 1 = conjMap C S g 0 ≫ δ₀`，其中 `C = Rep.dimensionShiftUp A`。

按函数读作：`conjMap A S g (δ₀ x) = δ₀ (ρ_C g x)`（`x ∈ C^S`）——正是 `δ₀` 关于
`G ⧸ S`-结构的**线性**。

证明 = `HomologicalComplex.HomologySequence.δ_naturality` 作用在
`conjCochainsSES`（短复形的自同态）上，取 `(i, j) = (0, 1)`。 -/
theorem deltaZero_conj (A : Rep k G) (S : Subgroup G) [S.Normal] (g : G) :
    deltaZero_coindBot A S ≫ conjMap A S g 1
      = conjMap (Rep.dimensionShiftUp A) S g 0 ≫ deltaZero_coindBot A S := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (conjCochainsSES A S g)
    (cochainSES_S_shortExact A S) (cochainSES_S_shortExact A S) 0 1 (by decide)
  -- `h` 的两端 `δ` 就是 `deltaZero_coindBot`；两个 `homologyMap` 就是 `conjMap`
  convert h using 2 <;> rfl

end L20261018

#print axioms L20261018.dimShiftSES_S
#print axioms L20261018.dimShiftSES_S_eq
#print axioms L20261018.cochainSES_S
#print axioms L20261018.cochainSES_S_eq
#print axioms L20261018.cochainSES_S_shortExact
#print axioms L20261018.conjCochainsSES
#print axioms L20261018.conjCochainsSES_τ₁
#print axioms L20261018.conjCochainsSES_τ₃
#print axioms L20261018.deltaZero_conj
