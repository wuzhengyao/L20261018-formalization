import L20261018.Infra.Cohomology.Boundary.Step012_inner_conj_trivial_hyp

/-!
# R1104（**★★ 修正 R1103 的具名假设：`InnerConjTrivial` 只能对 `g ∈ S` 陈述**）

## 为什么要改（复查原文）

`R1103` 把假设写成 `∀ g : G, conjMap A S g n = 𝟙`。复查后发现它**过强、且很可能为假**：

- 若对**一切** `g : G` 都平凡，则 `H¹(S,A)` 上的 `G`-作用平凡 ⟹ 它作为 `G ⧸ S`-模是**平凡模**；
- 但 GS 6.8.5 的 `δ₀ : C^S → H¹(S,A)` 被 GS 断言为 **`G/H`-模映射**，而 `C^S` 的 `G/H`-作用
  **一般非平凡**（否则 `H^i(G/H, C^H)` 全为 0，GS 的整段构造失去内容）⟹ 矛盾。

**正确的陈述**（NSW I §5，`g_*` 的定义）：内自同构平凡性是对**群自己的元素**说的——
「`(x ↦ g⁻¹ x g, ρ g)` 合成的 `g_*` 在 `H^n(G,X)` 上是恒等，`g : G`」。
用在 `S ◁ G` 上，即**只对 `g : S`** 断言。

## 本轮

| 声明 | 内容 |
|---|---|
| **`innerConjTrivialIn`** | ★ **修正后的具名假设**：`∀ g : S, conjMap A S (g : G) n = 𝟙` |
| **`innerConjTrivialIn_iff`** | 等价写法（逐点固定） |
| **`innerConjTrivialIn_of_subsingleton`** | **非空性见证** |
| **`innerConjTrivialIn_of_forall`** | ★ R1103 的强形式 **⟹** 修正形式（记录两者的关系） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **修正后的具名假设**：`S` 的**内**自同构（`g ∈ S`）与 `ρ g` 合成的共轭作用在 `H^n(S,A)` 上平凡。

这正是 NSW I §5 的 `g_* = id`（`g` 取在群 `S` 内），连续侧同型件为
`TauCeti.ContinuousCohomology.map_eq_id_of_inner`（取群 `S`）。
⟹ `H^n(S,A)` 上的 `G`-作用**经 `G ⧸ S` 分解**（这才是 GS 需要的）。 -/
def innerConjTrivialIn (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) : Prop :=
  ∀ g : S, conjMap A S (g : G) n = 𝟙 (groupCohomology (Rep.res S.subtype A) n)

/-- 等价写法：逐点固定。 -/
theorem innerConjTrivialIn_iff (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    innerConjTrivialIn A S n ↔
      ∀ (g : S) (x : groupCohomology (Rep.res S.subtype A) n), (conjMap A S (g : G) n) x = x := by
  constructor
  · intro h g x
    rw [h g]
    rfl
  · intro h g
    ext x
    exact h g x

/-- **非空性见证**：`H^n(S,A)` 为子单集时假设自动成立。 -/
theorem innerConjTrivialIn_of_subsingleton (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    [Subsingleton (groupCohomology (Rep.res S.subtype A) n)] :
    innerConjTrivialIn A S n := by
  intro g
  ext x
  exact Subsingleton.elim _ _

/-- ★ **R1103 的强形式 ⟹ 修正形式**（记录两者关系；强形式对 `g ∈ S` 的特例即修正形式）。 -/
theorem innerConjTrivialIn_of_forall (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ)
    (h : InnerConjTrivial A S n) : innerConjTrivialIn A S n :=
  fun g => h (g : G)

end L20261018

#print axioms L20261018.innerConjTrivialIn
#print axioms L20261018.innerConjTrivialIn_iff
#print axioms L20261018.innerConjTrivialIn_of_subsingleton
#print axioms L20261018.innerConjTrivialIn_of_forall
