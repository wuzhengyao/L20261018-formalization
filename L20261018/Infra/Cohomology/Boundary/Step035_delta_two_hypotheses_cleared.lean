import L20261018.Infra.Cohomology.Boundary.Step034_hcd_empty_hypothesis
import L20261018.Infra.Cohomology.Boundary.Step025_inner_conj_trivial_in_discharged

/-!
# S44 R1：★★★★★ **`∂₂` 的假设面清零** —— 只剩 `H²(S,A) = 0`，且等变性无条件

## 本件在 GS §6.8 的哪一格

GS **Construction 6.8.1**（`raw/GilleSzamuely2017.tex:9475`，逐字）构造

> `∂^i : H^i(G,A) → H^{i-1}(G/H, H^1(H,A))` for all torsion `G`-modules `A` and all `i > 0`

其装配是**三段**：

| 段 | 内容 | 出处 |
|---|---|---|
| ① | `H^i(G,A) ≅ H^{i-1}(G/H, C^H)`（`i ≥ 2`） | GS (6.15) |
| ② | `C^H → H^1(H,A)`（`G/H`-模态射） | GS `lemma-conjugation-long-exact` |
| ③ | `H^{i-1}(G/H, C^H) → H^{i-1}(G/H, H^1(H,A))` | 由 ② 诱导 |

## 本轮把 ①②③ 的**假设面**合起来清零

| 段 | 历史状态 | 本件 |
|---|---|---|
| ① | `Hyp229.deltaTwo_firstHalf` 要 `hcd : ∀ k' ≥ 2, H^{k'}(S,A) = 0` | **`Hyp536` 已把 `n = 0` 分支上的 `hcd` 证成空假设** ⟹ 只需 `H²(S,A) = 0`（**单次**） |
| ② | `Hyp233`／`Hyp234` 的 `innerConjTrivialIn A S 1`（具名假设） | **`Hyp246.innerConjTrivialIn_one` 无条件** |
| ③ | `Hyp239.deltaZeroBar`（要 ②） | 直接搬 ② 的无条件版 |

⟹ **`deltaTwo_minimal`：`∂₂` 的唯一前提是 `H²(S,A) = 0`。**
对战役载体 `S = I_K`，那正是（★）给的 `cd_ℓ(I_K) ≤ 1` 的单次读数
（`Hyp516.cdLE_inertia`／`Hyp517.inertiaLoc_cdLE`，S43 已无条件机检）。

## 与 `Hyp246.deltaTwoFree` 的关系（**不重复**）

`Hyp246.deltaTwoFree` 的前提是 `hcd : ∀ k' ≥ 2, …`（**全次数**）；
本件的 `deltaTwo_minimal` 的前提是单条 `IsZero (H²(S,A))`。
`hcd ⟹ h2` 是 `hcd 2 le_rfl`；反向不成立。故本件严格更强（少一个全称量词）。
两者**靶类型相同**（都带 `innerConjTrivialIn_one A S`），故可互换消费。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`deltaTwo_minimal`** | ★★★★★ **`∂₂` 只要求 `H²(S,A) = 0`** |
| **`deltaTwo_minimal_eq`** | 展开式（记录三段复合） |
| **`deltaTwo_minimal_type_lock`** | 源/靶锁定：改动任一处的 `H²`／`H¹` 即编译失败 |
| **`isZero_h2_of_hcd`** | `hcd ⟹ h2`（与 `Hyp246` 的接口；证明全次数到单次的那一步） |

## 诚实边界

* 本件是**抽象侧**（`TauCeti.groupCohomology`）。战役载体 `GaloBase.H2 = continuousCohomology 2`
  与它的桥**只在 `Hyp537`／`Hyp538` 的「`IsZero`」方向**已通；
  **映射本身**（`∂₂` 的连续侧实例）仍需一处运输 —— 那是下一轮（S44 R2）。
* 本件**不**给 (a)（GS 6.8.7 的值公式），也**不**给 (d)（`∂₂ ∘ Inf = 0`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- `hcd`（GS 的 `cd(S) ≤ 1`，抽象形式）**蕴含** `H²(S,A) = 0`（单次）。

这是 `Hyp246.deltaTwoFree` 的假设 ⟹ 本件 `deltaTwo_minimal` 的假设的接口：
反向不成立，故本件的假设严格更弱。 -/
theorem isZero_h2_of_hcd
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    IsZero (groupCohomology (Rep.res S.subtype A) 2) :=
  hcd 2 le_rfl

/-- ★★★★★ **GS 6.8.5 的 `∂₂`，假设面清零**：

`∂₂ : H²(G,A) ⟶ H¹(G⧸S, H¹(S,A))`，唯一前提是 `H²(S,A) = 0`（**不是**全次数 `cd(S) ≤ 1`）。

三段复合（照 GS 原文的顺序）：

```
H²(G,A) --(GS 6.15, Hyp536)--> H¹(G⧸S, C^S) --map deltaZeroBar--> H¹(G⧸S, H¹(S,A))
```

其中 `C = Rep.dimensionShiftUp A`（`0 → A → Coind → C → 0` 的商），
`deltaZeroBar`（`Hyp239`）是 `C^S → H¹(S,A)`（GS `lemma-conjugation-long-exact`），
其等变性由 `Hyp246.innerConjTrivialIn_one`（无条件）供给。 -/
noncomputable def deltaTwo_minimal
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    groupCohomology A 2
      ⟶ groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1 :=
  (deltaTwo_firstHalf'_of_h2 A h2).hom ≫
    groupCohomology.map (MonoidHom.id (G ⧸ S))
      (deltaZeroBar A S (innerConjTrivialIn_one A S)) 1

/-- `deltaTwo_minimal` 的三段复合展开式（记录定义，供下游 `rw`）。 -/
theorem deltaTwo_minimal_eq
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    deltaTwo_minimal A S h2 =
      (deltaTwo_firstHalf'_of_h2 A h2).hom ≫
        groupCohomology.map (MonoidHom.id (G ⧸ S))
          (deltaZeroBar A S (innerConjTrivialIn_one A S)) 1 :=
  (rfl)

/-- **源/靶类型锁定**：`deltaTwo_minimal` 是一个函数 `H²(G,A) → H¹(G⧸S, H¹(S,A))`。

改动源或靶中任何一处（次数、`h1RepQuot` 的等变性证明）都会使本引理编译失败
（KB 规则：陈述保真的机检形式之一）。 -/
noncomputable def deltaTwo_minimal_type_lock
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    (↥(groupCohomology A 2)
      → ↥(groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1)) :=
  deltaTwo_minimal A S h2

/-- **靶的载体识别**：`deltaTwo_minimal` 的靶底层确实是 `H¹(S,A)`（与 `Hyp239.h1RepQuot_one_V` 同一 `rfl`）。 -/
theorem deltaTwo_minimal_target_V :
    (h1RepQuot A S 1 (innerConjTrivialIn_one A S)).V
      = ↥(groupCohomology (Rep.res S.subtype A) 1) :=
  (rfl)

/-- ★★★ **与旧件的接口**：`Hyp246.deltaTwoFree` 的假设 `hcd` **实为本件假设的特例**。

即：凡消费 `deltaTwoFree A S hcd` 者，可用 `deltaTwo_minimal A S (isZero_h2_of_hcd A S hcd)`
得到**同源同靶**的映射 —— 本件不引入新的靶类型，故旧下游零改动。 -/
theorem deltaTwo_minimal_consumes_hcd
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    (↥(groupCohomology A 2)
        → ↥(groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1))
      = (↥(groupCohomology A 2)
        → ↥(groupCohomology (h1RepQuot A S 1 (innerConjTrivialIn_one A S)) 1)) := by
  have h2 := isZero_h2_of_hcd A S hcd
  rfl

end L20261018

#print axioms L20261018.isZero_h2_of_hcd
#print axioms L20261018.deltaTwo_minimal
#print axioms L20261018.deltaTwo_minimal_eq
#print axioms L20261018.deltaTwo_minimal_type_lock
#print axioms L20261018.deltaTwo_minimal_target_V
#print axioms L20261018.deltaTwo_minimal_consumes_hcd
