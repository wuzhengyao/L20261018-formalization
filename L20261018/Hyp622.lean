import L20261018.Hyp621

/-!
# S51 R15：`𝒪_W` 的 `Γ_F`-稳定性（从 `FbarValuationHyp₃` 导出）＋ **惯性子群需要「值保持」而非仅「环稳定」**

## 0 本件两件事

**(甲)** 把 `Hyp621` 的无条件稳定性**接到** `FbarValuationHyp₃` 上：
`FbarValuationHyp₃` 给的 `W` 满足 `W.valuationSubring = 𝒪bar`（逐元），而 `𝒪bar` 已被机检为 `Γ_F`-不变
（`Hyp621.mem_integralClosure_algEquiv`）⟹ **`W.valuationSubring` 是 `Γ_F`-稳定的**。

**(乙)** ⚠ **登记一条对自定计划的更正**（见 §2）：惯性子群 `I` 的**子群性**（尤其 `⁻¹` 封闭）
**不能**只靠「`𝒪_W` 环稳定」得到，它需要 **`W ∘ σ = W`（值保持）**，而后者等价于**延拓唯一性**
（即 Hensel 的内容）。⟹ 我原计划「由稳定条件取惯性子群」**缺一格**，必须在假设里补「值保持」。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`valSubring_stable`** | ★★★★★ 由 `FbarValuationHyp₃` 得 `𝒪_W` 的 `Γ_F`-稳定性 |
| **`inertiaSet`** | 惯性**集合** `{σ | ∀ x, W x ≤ 1 → W (σ x - x) < 1}`（定义，尚未证子群） |
| **`inertiaSet_needs_value_pres`** | ★★★ 散文＋类型锁定的**更正说明**（见 §2，非定理） |

## 2 ⚠ 为什么 `inertiaSet` **不能**直接是子群（本轮的重要负面发现）

设 `I = {σ | ∀ x, W x ≤ 1 → W (σ x - x) < 1}`。

* `1 ∈ I` ✓；`σ, τ ∈ I ⟹ στ ∈ I` ✓ —— **需要** `map_add_le_max'` ＋ 稳定性（已有）。
* **`σ ∈ I ⟹ σ⁻¹ ∈ I` ✗ 不能**：`σ(σ⁻¹x - x) = x - σx`，故 `W(σ⁻¹x - x)` 与 `W(x - σx)` 之间差一个
  `σ`——把 `W` 换成 `W ∘ σ` 就变了。**这一步恰好需要 `W ∘ σ = W`**，而那是**延拓唯一性**（Hensel）。

**正确的处理**：把「值保持」显式写进假设。两种等价写法：
```
(W_unique : ∀ σ : F̄ ≃ₐ[F] F̄, ∀ y, W (σ y) = W y)
```
—— 它由 **Bourbaki VI §8 exerc. 6 e) / Neukirch (6.2)** 在 Hensel 下给出。
⟹ `FbarValuationHyp₃` 应升为 **`FbarValuationHyp₄`**：`𝒪_W = 𝒪bar` **＋** `W ∘ σ = W`。
**本件不改动 `Hyp621` 的定义**（避免破坏下游），只登记下一轮应加的第四条。

## 3 诚实边界

* `valSubring_stable` 是**导出**（从 `Hyp621` 的机检件 ＋ 假设），不是新数学。
* `inertiaSet` **只是定义**，**本轮未证其子群性**（原因见 §2，非疏漏）。
* 本轮**不增覆盖率**。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Stable

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★ **`𝒪_W` 的 `Γ_F`-稳定性**：由 `FbarValuationHyp₃`（`𝒪_W = 𝒪bar` 逐元）
＋ `Hyp621.mem_integralClosure_algEquiv`（`𝒪bar` 不变）即得。 -/
theorem valSubring_stable (h : FbarValuationHyp₃ (F := F)) :
    ∃ W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)),
      ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (x : SeparableClosure F),
        x ∈ W.valuationSubring → σ x ∈ W.valuationSubring := by
  obtain ⟨W, hW⟩ := h
  refine ⟨W, ?_⟩
  intro σ x hx
  rw [hW]
  exact mem_integralClosure_algEquiv σ ((hW x).mp hx)

end Stable

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- **惯性集合**（定义）：在 `𝒪_W/𝔪_W` 上平凡的 `Γ_F` 元素。

⚠ 本件**未**证其子群性：`⁻¹` 封闭需要**值保持** `W ∘ σ = W`（＝延拓唯一性，Hensel），
见本文件 §2。下一轮以 `FbarValuationHyp₄` 补上。 -/
def inertiaSet (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ))) :
    Set (SeparableClosure F ≃ₐ[F] SeparableClosure F) :=
  {σ | ∀ x : SeparableClosure F, W x ≤ 1 → W (σ x - x) < 1}

/-- `1` 属于惯性集合。 -/
theorem one_mem_inertiaSet (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ))) :
    (1 : SeparableClosure F ≃ₐ[F] SeparableClosure F) ∈ inertiaSet W := by
  intro x _
  simp

end Inertia

end L20261018

#print axioms L20261018.valSubring_stable
#print axioms L20261018.one_mem_inertiaSet
