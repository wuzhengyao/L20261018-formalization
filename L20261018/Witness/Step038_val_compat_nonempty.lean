import L20261018.Ch2.Hensel.ResidueMap.Step063_mu_p_residue_instance
import L20261018.Ch2.Hensel.Valuation.Step021_val_compat_elementwise
import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# S51 R10：**`ValCompat` 的非空见证** —— 还 `Hyp187` 登记的那笔 L1/L10① 义务

## 0 为什么这是本轮最该做的一格

`Hyp187` 文件头明写：

> **未完成（必须补，本仓 L1/L10①）**：`ValCompat` 的**非空见证**（计划：在 `ℚ_p` 上实例化）。

这不是装饰性的：`ValCompat` 被**大量**定理当作假设（`Hyp190`–`Hyp198`、`Hyp342`、`Hyp449`、
`Hyp610`–`Hyp617` 的档 ⑥ 链…）。按 `CLAUDE.md` 的**在住性**纪律（L1＋L10①：条件定理须核
假设类非空），**在给出见证之前，这一大片条件定理都是空洞的**。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`valCompat_normalizedValuation`** | ★★★★★★ **任意非阿局部域**：`ValCompat (F := K) (normalizedValuation K)` |
| **`valCompat_witness_padic`** | ★★★★★★★ **具体见证**：`ValCompat (F := ℚ_[p]) (normalizedValuation ℚ_[p])` |
| `nonempty_valCompat` | 上一条的 `Nonempty` 形态（L1 的判据式陈述） |

## 2 证明（两格，全部走库内）

`ValCompat` 两个字段（`Hyp187:10`）：

* `mem_integer : 0 ≤ (v a).toAdd → (a : F) ∈ 𝒪[F]` —— 就是
  `TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg`
  （`NormalizedValuation.lean:309`）的 `mpr`；
* `mem_maximalIdeal : (a : F) ∈ 𝒪[F] → ((⟨a,_⟩ : ↥𝒪[F]) ∈ 𝔪 ↔ 0 < (v a).toAdd)` —— 由
  **`Valuation.mem_maximalIdeal_iff`**（`ValuationSubring.lean:878`：`a ∈ 𝔪 ↔ v a < 1`）
  加两条序等价：
  `valuation K a ≤ 1 ↔ 0 ≤ toAdd`（上一条 ＋ `Valuation.mem_integer_iff`）与
  `valuation K a = 1 ↔ toAdd = 0`（`normalizedValuation_eq_one_iff` ＋ `toAdd` 单射），
  最后 `omega` 在 `ℤ` 上收口。

⟹ **零自建数学**：三件全是库内引理，本件只做接口。

## 3 诚实边界

* 见证只在**非阿局部域**（`[IsNonarchimedeanLocalField K]`，含 `ℚ_[p]`）上给出。
  论文设定是**一般 Hensel**：那里的 `ValCompat` 仍需一条「赋值与 `𝒪[F]` 相容」的接口
  （`normalizedValuation` 只在局部域上有）。**本件因此消掉的是"假设类空"的疑虑，
  不是"一般 Hensel 情形"的缺口。**
* 档 ⑥ 的另两条假设（`φ`／`(CI)`／Tsen）**不受影响**。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Normalized

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- ★★★★★★ **`ValCompat` 在任意非阿局部域上成立**（取 `v := normalizedValuation`）。 -/
theorem valCompat_normalizedValuation :
    ValCompat (F := K) (TauCeti.normalizedValuation K) where
  mem_integer := fun a h =>
    (TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg a).mpr h
  mem_maximalIdeal := by
    intro a ha
    have h1 : (valuation K (a : K)) ≤ 1 ↔ 0 ≤ (TauCeti.normalizedValuation K a).toAdd := by
      rw [← Valuation.mem_integer_iff (v := valuation K)]
      exact TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg a
    have h2 : (valuation K (a : K)) = 1 ↔ (TauCeti.normalizedValuation K a).toAdd = 0 := by
      rw [← TauCeti.normalizedValuation_eq_one_iff a]
      exact ⟨fun h => by rw [h]; rfl,
        fun h => by simpa using congrArg Multiplicative.ofAdd h⟩
    change (⟨(a : K), ha⟩ : ↥((valuation K).valuationSubring)) ∈
        IsLocalRing.maximalIdeal ((valuation K).valuationSubring) ↔
      0 < (TauCeti.normalizedValuation K a).toAdd
    rw [Valuation.mem_maximalIdeal_iff (v := valuation K)]
    constructor
    · intro hlt
      have hle : 0 ≤ (TauCeti.normalizedValuation K a).toAdd := h1.mp (le_of_lt hlt)
      have hne : (TauCeti.normalizedValuation K a).toAdd ≠ 0 :=
        fun h0 => (ne_of_lt hlt) (h2.mpr h0)
      omega
    · intro hpos
      refine lt_of_le_of_ne (h1.mpr (le_of_lt hpos)) ?_
      intro heq
      have h0 : (TauCeti.normalizedValuation K a).toAdd = 0 := h2.mp heq
      omega

end Normalized

/-! ## 具体见证：`ℚ_[p]` -/

section Padic

variable (p : ℕ) [Fact p.Prime] [NeZero p]

/-- ★★★★★★★ **L1/L10① 的非空见证**：`ValCompat` 在 `ℚ_[p]` 上成立。 -/
theorem valCompat_witness_padic :
    ValCompat (F := ℚ_[p]) (TauCeti.normalizedValuation ℚ_[p]) :=
  valCompat_normalizedValuation ℚ_[p]

/-- 上一条的判据式陈述（`Hyp187` 登记的「非空见证」义务）。 -/
theorem nonempty_valCompat :
    Nonempty (ValCompat (F := ℚ_[p]) (TauCeti.normalizedValuation ℚ_[p])) :=
  ⟨valCompat_witness_padic p⟩

end Padic

end L20261018

#print axioms L20261018.valCompat_normalizedValuation
#print axioms L20261018.valCompat_witness_padic
#print axioms L20261018.nonempty_valCompat
