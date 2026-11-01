import L20261018.Ch2.Hensel.Valuation.Step040_integral_closure_value_preserving

/-!
# S51 R16：`FbarValuationHyp₄`（加「值保持」）＋ **惯性子群 `I ≤ Γ_F` 机检成立**

## 0 补的是上一轮登记的缺口

S51 R15 发现：`𝒪_W` 的**环稳定**不足以让惯性集合成子群；`⁻¹` 封闭需要**值保持** `W ∘ σ = W`
（而值保持 ⟺ 延拓**唯一性** ⟺ Hensel，见 `BOURBAKI-ACVI-8-VALUATIONS.md` §6）。

本件：
* 把「值保持」立为 **`FbarValuationHyp₄`** 的第二条（第一条是 `𝒪_W = 𝒪bar`）；
* **注意**：`hval` **蕴含** `hstab`（`W (σ x) = W x` ⟹ 两者同时 `≤ 1`），故 R15 的 `valSubring_stable`
  在 `Hyp₄` 下**自动**成立——**环稳定性不再是独立要求**；
* 于是 **`inertia` 真成了 `Subgroup (Γ_F)`**（`Γ_F = F̄ ≃ₐ[F] F̄`）。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`FbarValuationHyp₄`** | ★★★★★★ `∃ W, (𝒪_W = 𝒪bar) ∧ (∀ σ y, W (σ y) = W y)` |
| **`inertia`** | ★★★★★★★ **惯性子群** `I ≤ Γ_F`：`{σ | ∀ x, W x ≤ 1 → W (σ x - x) < 1}` |
| `mem_inertia` | 成员判据（`rfl` 级） |
| **`hstab_of_hval`** | ★★★★ 「值保持 ⟹ 环稳定」（补上 R15 缺的那一格） |

## 2 三项封闭性的证明骨架（照 Neukirch (4.8) 的唯一性论证）

* `1`：`W (x - x) = W 0 = 0 < 1`。
* `*`：`(σ*τ)x - x = (σ(τx) - τx) + (τx - x)`；`W(τx) = W x ≤ 1`（用**值保持**），故两项都 `< 1`；
      `map_add_le_max'` ＋ `max_lt` 收口。
* `⁻¹`：`σ(σ⁻¹x - x) = x - σx = -(σx - x)`；由**值保持** `W(σ⁻¹x - x) = W(x - σx) = W(σx - x) < 1`。
      —— 这一步正是 R15 卡住处，现由 `hval` 打通。

## 3 诚实边界

* `FbarValuationHyp₄` 仍是**假设**（Neukirch (6.2) 在 Hensel 下给出）。
* 本轮**不增覆盖率**；但 `(CI)` 的**表述**从此可以写出来了（惯性子群有了）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Hyp4

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]

/-- ★★★★★★ **延拓假设（四条中最强的一版）**：`W` 的赋值环是 `𝒪[F]` 在 `F̄` 中的整闭包，
**且** `Γ_F` **保 `W` 的值**（值保持 ＝ 延拓唯一性，Neukirch (6.2) / Bourbaki VI §8 exerc. 6 e)）。 -/
def FbarValuationHyp₄ : Prop :=
  ∃ W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)),
    (∀ x : SeparableClosure F,
      x ∈ W.valuationSubring ↔ x ∈ integralClosure ↥𝒪[F] (SeparableClosure F)) ∧
    (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
      W (σ y) = W y)

/-- ★★★★ **值保持 ⟹ 环稳定**（补上 S51 R15 缺的那一格）。 -/
theorem hstab_of_hval (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
    (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
      W (σ y) = W y)
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) {x : SeparableClosure F}
    (hx : x ∈ W.valuationSubring) : σ x ∈ W.valuationSubring := by
  change W x ≤ 1 at hx
  change W (σ x) ≤ 1
  rwa [hval σ x]

end Hyp4

/-! ## 2 惯性子群 -/

section Inertia

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

/-- ★★★★★★★ **惯性子群** `I ≤ Γ_F`：在剩余域 `𝒪_W/𝔪_W` 上平凡的 `Γ_F` 元素
（等价刻画：`W (σ x - x) < 1`，即 `σ x ≡ x mod 𝔪_W`）。 -/
def inertia : Subgroup (SeparableClosure F ≃ₐ[F] SeparableClosure F) where
  carrier := {σ | ∀ x : SeparableClosure F, W x ≤ 1 → W (σ x - x) < 1}
  one_mem' := by
    intro x _
    show W ((1 : SeparableClosure F ≃ₐ[F] SeparableClosure F) x - x) < 1
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : W (τ x) ≤ 1 := by rw [hval τ x]; exact hx
    have h1 : W (σ (τ x) - τ x) < 1 := hσ (τ x) hτx
    have h2 : W (τ x - x) < 1 := hτ x hx
    rw [show ((σ * τ) x) = σ (τ x) from rfl]
    calc W (σ (τ x) - x)
        = W ((σ (τ x) - τ x) + (τ x - x)) := by
            congr 1
            ring
      _ ≤ max (W (σ (τ x) - τ x)) (W (τ x - x)) := Valuation.map_add_le_max' _ _ _
      _ < 1 := max_lt h1 h2
  inv_mem' := by
    intro σ hσ x hx
    -- `W (σ⁻¹ x - x) = W (x - σ x) = W (σ x - x) < 1`
    have key : W (σ (σ⁻¹ x - x)) = W (σ⁻¹ x - x) := hval σ _
    have harg : σ (σ⁻¹ x - x) = x - σ x := by
      simp [map_sub]
    have hneg : W (x - σ x) = W (σ x - x) := by
      rw [← neg_sub, Valuation.map_neg]
    rw [← key, harg, hneg]
    exact hσ x hx

/-- 惯性子群的成员判据。 -/
@[simp]
theorem mem_inertia (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
    σ ∈ inertia W hval ↔ ∀ x : SeparableClosure F, W x ≤ 1 → W (σ x - x) < 1 :=
  Iff.rfl

end Inertia

end L20261018

#print axioms L20261018.hstab_of_hval
#print axioms L20261018.mem_inertia
