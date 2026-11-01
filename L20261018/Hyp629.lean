import Hyp628
import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup

/-!
# S52 R22：**`TsenHyp` 的非空见证** —— 可分闭 `κ` 时 `hκ` 机检成立（还 L1／L10① 义务）

## 0 目标

`wiki/hyp-tsen.md` §4 一直登记「`TsenHyp` / `hκ` 的**机检见证无**」——
按 `CLAUDE.md` L1＋L10①，这意味着档 ⑥ 的所有条件定理在**假设类非空**这一点上**未被核过**。
（同型先例：`Hyp618` 用 `ℚ_[p]` 见证 `ValCompat`，还掉了 `Hyp187` 的那笔义务。）

本件用**退化但真实**的 `κ`（可分闭域）清掉这笔义务：

```
[IsSepClosed κ]（mathlib 类）⟹ Subsingleton (AbsoluteGaloisGroup κ)   -- TauCeti 实例
  ⟹ 平凡群的连续上同调在正次数消失                                 -- TauCeti 实例（TrivialGroup.lean:39）
  ⟹ CohomologicalDimensionLE p G 0（进而 ≤ 1）                      -- 本件
  ⟹ TsenHyp κ p ⟹ Subsingleton (GaloBase.H2 κ p)                    -- Hyp628 的 L2 桥
```

## 1 数学（两行，无需任何 Tsen 定理）

* `κ` 可分闭 ⟹ `G_κ` 平凡 ⟹ **`cd_p(G_κ) = 0`**（平凡群在正次数没有上同调）；
* `cd_p = 0 ≤ 1` ⟹ `TsenHyp κ p` 成立。

**这不是 Tsen 定理**：Tsen 说的是 `κ = ℂ(t)`（`G_κ = Ẑ`，非平凡）的情形。本件给的是
**假设类非空**的下界见证（退化情形），**不**替代 L3。

## 2 本件交付（全部机检，零 `sorry`，axioms 恰三条）

| 声明 | 内容 |
|---|---|
| **`tsenHyp_of_subsingleton_galois`** | ★★★★★ `Subsingleton G_κ ⟹ TsenHyp κ p`（`cd_p(G_κ) = 0`） |
| **`tsenHyp_of_isSepClosed`** | ★★★★★ `[IsSepClosed κ] ⟹ TsenHyp κ p`（用 TauCeti 的 `Subsingleton (AbsoluteGaloisGroup κ)` 实例） |
| **`subsingleton_H2_of_isSepClosed`** | ★★★★★★★ **`hκ` 的机检见证**：`[IsSepClosed κ] ⟹ Subsingleton (GaloBase.H2 κ p)` |
| **`subsingleton_H2_complex`** | ★★★★★ 具体见证：`Subsingleton (GaloBase.H2 ℂ p)`（`ℂ` 可分闭） |

## 3 工艺

* 平凡群的消失是 TauCeti 的**实例**（`instance subsingleton_continuousCohomology_succ_of_subsingleton`，
  namespace `TauCeti.ContinuousCohomology`），故 `i = n + 1` 之后一行 `infer_instance` 收口。
* `CohomologicalDimensionLE` 要的是 `n = 0` 版：`∀ i, 0 < i → …` ⟹ 把 `i` 写成 `i - 1 + 1`
  （`obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩`）。

## 4 诚实边界

* **退化见证 ≠ Tsen**：`κ` 可分闭时 `H¹(κ, μ_p) = 0`，故 `(CI)` 要求 `ker v̄ = 0`，档 ⑥ 退化为空内容
  （与 `hyp-residue-galois` §3 的「退化实例」同一条）。本件**只**清「假设类非空」的义务。
* **仍缺**：`κ = ℂ(t)` 侧的 `TsenHyp`（＝ Tsen 定理，L3）＋「剩余域恰为 `ℂ(t)` 的 `F`」的实例。
* 本件**不动** `(CI)`／`FbarValuationHyp₄`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section TsenWitness

/-! ### 一、平凡 Galois 群 ⟹ `cd_p = 0 ≤ 1` -/

/-- ★★★★★ **平凡绝对 Galois 群 ⟹ `TsenHyp`**：`G_κ` 平凡时 `cd_p(G_κ) = 0`，
故 `CohomologicalDimensionLE p G_κ 0`（进而 `≤ 1`）成立。

数学：平凡群在**正次数**没有连续上同调（TauCeti 的
`subsingleton_continuousCohomology_succ_of_subsingleton` 是**实例**）。 -/
theorem tsenHyp_of_subsingleton_galois {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
    [Subsingleton (AbsoluteGaloisGroup K)] : TsenHyp K p := by
  intro M _ _ _ _ _ _ i hi
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  infer_instance

/-- ★★★★★ **可分闭 `κ` ⟹ `TsenHyp`**：由 TauCeti 的实例
`[IsSepClosed K] : Subsingleton (AbsoluteGaloisGroup K)` 落到上一条。 -/
theorem tsenHyp_of_isSepClosed {K : Type} [Field K] [IsSepClosed K] (p : ℕ) [Fact p.Prime] :
    TsenHyp K p :=
  tsenHyp_of_subsingleton_galois (K := K) p

/-! ### 二、`hκ` 的**机检见证**（L1＋L10① 的义务） -/

/-- ★★★★★★★ **`hκ` 的机检见证**：`[IsSepClosed κ] ⟹ Subsingleton (GaloBase.H2 κ p)`。

⟹ 档 ⑥ 的 `hκ` 侧**不再是空假设类**：可分闭域给它一个真实实例（虽然档 ⑥ 在该情形退化）。 -/
theorem subsingleton_H2_of_isSepClosed {K : Type} [Field K] [IsSepClosed K]
    (p : ℕ) [Fact p.Prime] : Subsingleton (GaloBase.H2 K p) :=
  subsingleton_H2_of_TsenHyp p (tsenHyp_of_isSepClosed (K := K) p)

/-- ★★★★★ **具体见证**：`H²(G_ℂ, Z/p) = 0`（`ℂ` 可分闭）。 -/
theorem subsingleton_H2_complex (p : ℕ) [Fact p.Prime] :
    Subsingleton (GaloBase.H2 ℂ p) :=
  subsingleton_H2_of_isSepClosed (K := ℂ) p

end TsenWitness

end L20261018

#print axioms L20261018.tsenHyp_of_subsingleton_galois
#print axioms L20261018.tsenHyp_of_isSepClosed
#print axioms L20261018.subsingleton_H2_of_isSepClosed
#print axioms L20261018.subsingleton_H2_complex
