import L20261018.Hyp232

/-!
# R1103（**(R2)：把缺口收敛为单条具名假设 `InnerConjTrivial`**）

## 背景

`PLAN-R2` §H-10：`∂₂` 五段机检，只剩 (3) 的**模层**——`H¹(S,A)` 上的 `G ⧸ S`-模结构，
即「内自同构在 `H¹` 上作用平凡」。R1101／R1102 已把共轭作用本身落成
（`conjSubtypeHom`／`conjCoeffHom`／`conjMap`）。本轮把该缺口**收敛为单条具名假设**：

```
InnerConjTrivial A S n  :≡  ∀ g : G, conjMap A S g n = 𝟙 _
```

配 `wiki/hyp-inner-conj-trivial.md`（假设陈述／类型锁定／非空性审计／解除路径）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`InnerConjTrivial`** | ★ 具名假设（唯一入口；下游 `G⧸S`-模结构只经它进入） |
| **`innerConjTrivial_iff`** | 其等价写法（`∀ g, ∀ x, conjMap A S g n x = x`） |
| **`innerConjTrivial_of_subsingleton`** | **非空性见证**：`H^n(S,A)` 为子单集时假设自动成立 |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **具名假设**：内自同构（＝共轭）在 `H^n(S,A)` 上作用平凡。

这是 `G ⧸ S`-模结构（从而 GS 6.8.5 的 `∂₂` 全长）的唯一缺口；
连续侧同型件为 `TauCeti.ContinuousCohomology.map_eq_id_of_inner`。 -/
def InnerConjTrivial (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) : Prop :=
  ∀ g : G, conjMap A S g n = 𝟙 (groupCohomology (Rep.res S.subtype A) n)

/-- 等价写法：逐点固定。 -/
theorem innerConjTrivial_iff (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    InnerConjTrivial A S n ↔
      ∀ (g : G), ∀ x : groupCohomology (Rep.res S.subtype A) n, (conjMap A S g n) x = x := by
  constructor
  · intro h g x
    rw [h g]
    rfl
  · intro h g
    ext x
    exact h g x

/-- **非空性见证**：`H^n(S,A)` 为子单集时，假设自动成立（`L1`／`L10①` 的可实现性一侧）。 -/
theorem innerConjTrivial_of_subsingleton (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    [Subsingleton (groupCohomology (Rep.res S.subtype A) n)] :
    InnerConjTrivial A S n := by
  intro g
  ext x
  exact Subsingleton.elim _ _

end L20261018

#print axioms L20261018.InnerConjTrivial
#print axioms L20261018.innerConjTrivial_iff
#print axioms L20261018.innerConjTrivial_of_subsingleton
