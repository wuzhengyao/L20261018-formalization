import Hyp235

/-!
# R1107（**★★ (R2)-1 第一块：`Rep k (G ⧸ S)` 结构 —— 由 `innerConjTrivialIn` 导出**）

## 数学（`PLAN-R2` §H-10 (3)-模层；GS `cons-residue-map-finite-coefficients`）

GS 6.8.5（`raw/GilleSzamuely2017.tex:9494–9500`）：
「But from the long exact sequence in `H`-cohomology coming from (6.14) we also obtain a map
`C^{H} → H^{1}(H,A)`, which is a morphism of `G/H`-modules by Lemma `lemma-conjugation-long-exact`.
Hence there are induced maps `H^{i-1}(G/H, C^{H}) → H^{i-1}(G/H, H^{1}(H,A))`.」

要作 `H^{i-1}(G/H, H¹(H,A))`，`H¹(S,A)` 必须**先是** `Rep k (G ⧸ S)`。
库内该模结构（抽象侧）**没有**（R1100 已内容式扫过 `conj`／`ConjAct`／`smulConj`）；
本轮把它造出来，入口只有 `innerConjTrivialIn`（`Hyp234`）。

## 方向问题（本轮的主要技术内容）

`conjMap` 的合成律**是反的**：`Hyp235.conjMap_comp` ＋ `conjSubtypeHom_mul` 给

```
conjMap A S (h * g) n = conjMap A S g n ≫ conjMap A S h n .
```

在 `ModuleCat` 里 `(f ≫ g).hom = g.hom ∘ f.hom`，两端一合就得

```
(conjMap (h * g) n).hom = (conjMap h n).hom * (conjMap g n).hom
```

⟹ **它就是正向的** `g ↦ (conjMap A S g n).hom` 是一个 `MonoidHom`
`G →* Module.End k (H^n(S,A))`（`conjEndHom`）——**不需要** `MulOpposite`。
（此前 `ASSUMPTIONS` 记录的「须经 `MulOpposite`」是对**两重反**的误判：`conjSubtypeHom` 反、
`≫` 反，两次反转抵消。）

## 本轮

| 声明 | 内容 |
|---|---|
| **`conjCoeffHom_comp_toLinearMap`** | 复合系数映射的底层公式（`map_congr` 用件） |
| **`conjMap_mul`** | ★ 合成律 `conjMap (h * g) = conjMap g ≫ conjMap h` |
| **`conjMap_one`** | `conjMap A S 1 n = 𝟙` |
| **`conjEndHom`** | ★★ `G →* Module.End k (H^n(S,A))`（共轭作用的乘性形式） |
| **`conjEndHom_ker`** | ★ `innerConjTrivialIn ⟹ S ≤ ker` |
| **`h1RepQuot`** | ★★ **`(R2)-1` 第一块**：`Rep k (G ⧸ S)`，底层 `H^n(S,A)` |
| **`h1RepQuot_ρ_mk`** | 取值公式：`(h1RepQuot …).ρ (g : G ⧸ S) = (conjMap g n).hom` |
| **`h1RepQuot_ρ_mk_eq_one`** | 一致性：`h` 生效处 `h1RepQuot` 的作用确经 `G ⧸ S` 分解 |

**下一轮**：`δ₀`（`Hyp230.deltaZero_coindBot`）的 `G ⧸ S`-线性性
（GS `lemma-conjugation-long-exact` 的抽象侧对应物：`δ` 在共轭作用下的自然性）。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- **复合系数映射的底层公式**：`(resFunctor …).map (conjCoeffHom g) ≫ conjCoeffHom h`
与 `conjCoeffHom (h * g)` 的底层线性映射相同（都是 `A.ρ (h * g)`）。

`groupCohomology.map_congr` 需要这种**底层**等式（因为 `res f A` 随 `f` 变，
不能直接 `rw` 换 `f`——那会报 "motive is not type correct"，见 `Hyp235` 记录）。 -/
theorem conjCoeffHom_comp_toLinearMap (A : Rep k G) (S : Subgroup G) [S.Normal] (g h : G) :
    ((Rep.resFunctor (conjSubtypeHom S h)).map (conjCoeffHom A S g) ≫
        conjCoeffHom A S h).hom.toLinearMap
      = (conjCoeffHom A S (h * g)).hom.toLinearMap := by
  ext a
  show A.ρ h (A.ρ g a) = A.ρ (h * g) a
  rw [map_mul]
  rfl

/-- ★ **`conjMap` 的合成律**：`conjMap A S (h * g) n = conjMap A S g n ≫ conjMap A S h n`。

这是 `Hyp235.conjMap_comp` ＋ `conjSubtypeHom_mul` 的合成（中间过 `map_congr`，
把 `(conjSubtypeHom S g).comp (conjSubtypeHom S h)` 换成 `conjSubtypeHom S (h * g)`）。 -/
theorem conjMap_mul (A : Rep k G) (S : Subgroup G) [S.Normal] (g h : G) (n : ℕ) :
    conjMap A S (h * g) n = conjMap A S g n ≫ conjMap A S h n := by
  have key := groupCohomology.map_congr (f := (conjSubtypeHom S g).comp (conjSubtypeHom S h))
    (g := conjSubtypeHom S (h * g)) (conjSubtypeHom_mul S g h)
    (conjCoeffHom_comp_toLinearMap A S g h) n
  rw [conjMap, ← key]
  exact conjMap_comp A S g h n

/-- ★ **`conjMap` 在一元处为恒等**。 -/
theorem conjMap_one (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    conjMap A S 1 n = 𝟙 (groupCohomology (Rep.res S.subtype A) n) := by
  have key := groupCohomology.map_congr (f := conjSubtypeHom S (1 : G)) (g := MonoidHom.id S)
    (conjSubtypeHom_one S) (φ := conjCoeffHom A S 1) (ψ := 𝟙 (Rep.res S.subtype A)) ?_ n
  · rw [conjMap, key, groupCohomology.map_id]
  · ext a
    show A.ρ (1 : G) a = a
    rw [map_one]
    rfl

/-- ★★ **共轭作用的乘性形式**：`g ↦ (conjMap A S g n).hom` 是 `MonoidHom`
`G →* Module.End k (H^n(S,A))`。

（`conjMap_mul` 给 `conjMap (h * g) = conjMap g ≫ conjMap h`；在 `ModuleCat` 里
`(f ≫ g).hom = g.hom ∘ f.hom` ＝ `g.hom * f.hom` ⟹ `(conjMap (h*g)).hom = h.hom * g.hom`，
即正向乘法。） -/
noncomputable def conjEndHom (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    G →* Module.End k (groupCohomology (Rep.res S.subtype A) n) where
  toFun g := (conjMap A S g n).hom
  map_one' := by rw [conjMap_one]; rfl
  map_mul' u v := by
    have h := conjMap_mul A S v u n
    rw [h]
    rfl

/-- `conjEndHom` 的取值公式。 -/
@[simp]
theorem conjEndHom_apply (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) (g : G) :
    conjEndHom A S n g = (conjMap A S g n).hom :=
  (rfl)

/-- ★ **`innerConjTrivialIn` 就是 `S ≤ ker (conjEndHom)`**：假设的唯一用途。 -/
theorem conjEndHom_ker (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : innerConjTrivialIn A S n) : S ≤ (conjEndHom A S n).ker := by
  intro s hs
  simp only [MonoidHom.mem_ker]
  change (conjMap A S s n).hom = 1
  rw [h ⟨s, hs⟩]
  rfl

/-- ★★ **`(R2)-1` 第一块：由 `innerConjTrivialIn` 导出 `Rep k (G ⧸ S)`**，底层 `H^n(S,A)`。

`innerConjTrivialIn A S n`（`Hyp234`）说 `S` 的内自同构在 `H^n(S,A)` 上平凡 ⟹
共轭作用 `conjEndHom` 经 `G ⧸ S` 分解（`QuotientGroup.lift`）。

取 `n = 1` 即 GS 6.8.5 所需的 `H¹(S,A)` 的 `G ⧸ S`-模结构。 -/
noncomputable def h1RepQuot (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : innerConjTrivialIn A S n) : Rep k (G ⧸ S) :=
  Rep.of (ρ := QuotientGroup.lift S (conjEndHom A S n) (conjEndHom_ker A S n h))

/-- `h1RepQuot` 的底层模就是 `H^n(S,A)`。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9497 quote="obtain a map $C^{H}\to H^{1}(H,A)$, which is a morphism of $G/H$-modules by Lemma \ref{lemma-conjugation-long-exact}."
@[simp]
theorem h1RepQuot_V (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : innerConjTrivialIn A S n) :
    (h1RepQuot A S n h).V = ↥(groupCohomology (Rep.res S.subtype A) n) :=
  (rfl)

/-- ★ **`h1RepQuot` 的作用取值公式**：在 `g : G ⧸ S` 处作用就是共轭作用 `conjMap g`。 -/
@[simp]
theorem h1RepQuot_ρ_mk (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : innerConjTrivialIn A S n) (g : G) :
    (h1RepQuot A S n h).ρ (g : G ⧸ S) = (conjMap A S g n).hom :=
  (rfl)

/-- 一致性检查：`innerConjTrivialIn` 保证 `s ∈ S` 在商上的作用确为恒等
（即该作用是**良定义**地经 `G ⧸ S` 分解，不是把 `G` 的作用硬塞进商）。 -/
theorem h1RepQuot_ρ_mk_coe (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : innerConjTrivialIn A S n) (s : S) :
    (h1RepQuot A S n h).ρ ((s : G) : G ⧸ S) = 1 := by
  rw [h1RepQuot_ρ_mk, h s]
  rfl

end L20261018

#print axioms L20261018.conjCoeffHom_comp_toLinearMap
#print axioms L20261018.conjMap_mul
#print axioms L20261018.conjMap_one
#print axioms L20261018.conjEndHom
#print axioms L20261018.conjEndHom_apply
#print axioms L20261018.conjEndHom_ker
#print axioms L20261018.h1RepQuot
#print axioms L20261018.h1RepQuot_V
#print axioms L20261018.h1RepQuot_ρ_mk
#print axioms L20261018.h1RepQuot_ρ_mk_coe
