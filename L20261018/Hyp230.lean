import L20261018.Hyp229

/-!
# R1100（**(R2)：`∂₂` 第 (3) 段的**可做部分** ＋ 一处库内缺口的精确定位**）

## 本轮侦察（内容式，`L46`／`L47`，记路径）

| 关键词 | 扫过的目录 | 结论 |
|---|---|---|
| `conj`／`ConjAct`／`smulConj` | `Homological/GroupCohomology/**`（抽象侧） | **无**：抽象侧**没有** `H^n(S,A)` 的 `G⧸S`-模结构 |
| 同上 | `Homological/ContCohomology/{InnerConjugation,ConjInvariants}.lean`（连续侧） | **有**：`ContinuousCohomology.map_eq_id_of_inner`（内自同构在上同调上作用平凡）、`H1ConjInvariants`、`H1ConjInvariantsEquivOfSmulEqSelf` |

## 缺口（`∅-formalization-gap`，按基建任务处理）

GS 6.8.5 在 `C^H → H¹(H,A)` 之后还要把它当作 **`G/H`-模映射**（GS 引 `Lemma conjugation-long-exact`），
才能作 `H^{i-1}(G/H, C^H) → H^{i-1}(G/H, H¹(H,A))`。这一步需要 **`H¹(H,A)` 上的 `G/H`-模结构**，
即「内自同构在 `H¹` 上作用平凡」。库内该事实**只在连续侧**（`map_eq_id_of_inner`），抽象侧缺。
⟹ 抽象路线在 (3) 的**模结构**这一半上遇基建缺口（不是数学缺口）。

## 本轮可做的部分（不需要模结构）

`0 → A → M → C → 0` 在 `S` 上的长正合列的**连接映射**：
`δ₀ : H⁰(S, C) ⟶ H¹(S, A)`，即 GS 的「`C^H → H¹(H,A)`」，作为一个**普通加法映射**（`AddCommGrpCat` 态射）。

| 声明 | 内容 |
|---|---|
| **`deltaZero_coindBot`** | ★ `δ₀ : H^0(S, C) → H^1(S,A)`（`C = Rep.dimensionShiftUp A`；`S` 侧 LES 的连接映射） |
| **`deltaZero_coindBot_eq`** | 它就是 `groupCohomology.δ` 在 `(0, 1)` 处的取值（记录定义） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **GS 的 `C^H → H^1(H,A)`**（作为普通加法映射）：`0 → A → M^G(A) → C → 0` 限制到 `S`
所得短正合列的长正合列连接映射 `δ : H^0(S,C) → H^1(S,A)`。

GS 原文（tex `:9496–9499`）：「But from the long exact sequence in `H`-cohomology coming from (6.14)
we also obtain a map `C^H → H^{1}(H,A)`, which is a morphism of `G/H`-modules …」——
本文件给出该映射的**加法层**；「`G/H`-模」那一半见文件头的缺口说明。 -/
noncomputable def deltaZero_coindBot (A : Rep k G) (S : Subgroup G) :
    groupCohomology (Rep.res S.subtype (Rep.dimensionShiftUp A)) 0 ⟶
      groupCohomology (Rep.res S.subtype A) 1 :=
  groupCohomology.δ (Rep.dimensionShiftUpSES_res_shortExact A S.subtype) 0 1 rfl

/-- 记录定义：`δ₀` 就是 `groupCohomology.δ` 在 `(0, 1)` 处的取值。 -/
theorem deltaZero_coindBot_eq (A : Rep k G) (S : Subgroup G) :
    deltaZero_coindBot A S =
      groupCohomology.δ (Rep.dimensionShiftUpSES_res_shortExact A S.subtype) 0 1 rfl :=
  (rfl)

/-- `δ₀` 的全等式（供下游把类写成具体代表）：它由 `groupCohomology.δ` 的 `epi` 性质刻画。 -/
theorem epi_deltaZero_coindBot (A : Rep k G) (S : Subgroup G) :
    Epi (deltaZero_coindBot A S) := by
  have h := groupCohomology.epi_δ_of_isZero
    (Rep.dimensionShiftUpSES_res_shortExact A S.subtype) 0
    (groupCohomology.isZero_res_coindBot_succ (k := k) (G := G) S A.V 0)
  exact h

end L20261018

#print axioms L20261018.deltaZero_coindBot
#print axioms L20261018.deltaZero_coindBot_eq
#print axioms L20261018.epi_deltaZero_coindBot
