import L20261018.Hyp623

/-!
# S51 R17：**惯性子群 `I` 的正规性** —— `Γ_κ = Γ_F/I` 成群的必要条件

## 0 先纠正一条**过时缺口登记**（L47/规则 24④）

上一轮（R16）交接件写「下一步：把 `Hyp614` 的 `hCI` 改写成以 `inertia` 为对象的具体命题」。
**按内容式 `grep` 重新生成缺口清单后，该登记是错的**：

* `Hyp342.lean:44` `VKG F p v hpF = ↥(LinearMap.ker (valLinOf …))` —— **就是 `ker v̄`**；
* `Hyp614` 的 `hCI : ∀ y : VKG F' p v hpF, ∃ a, inflH1 p φ' a = (y : GaloBase.V F' p)`
  —— **这就是 `(CI)` 的字面形式**（`ker v̄ ⊆ range infl₁`），**没有散文成分**。

⟹ `hCI` **不需要改写**；真正缺的是：`(CI)` 的**证明**，而它要先有 `Γ_κ = Γ_F/I` 这个群，
即 **`I` 必须正规**。本件补这一格。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`inertia_normal`** | ★★★★★★ **`(inertia W hval).Normal`** —— `I ◁ Γ_F` |
| `mem_inertia_normal_iff` | 正规性展开（可选辅助） |

## 2 证明（一行数学）

`τ (σ (τ⁻¹ x) − τ⁻¹ x) = (τστ⁻¹) x − x`，且由**值保持** `W (τ⁻¹ x) = W x ≤ 1`，
故 `σ ∈ I` 在 `τ⁻¹ x` 处给出 `W (σ(τ⁻¹x) − τ⁻¹x) < 1`，再用**值保持**搬回：

```
W ((τστ⁻¹) x − x) = W (τ(σ(τ⁻¹x) − τ⁻¹x)) = W (σ(τ⁻¹x) − τ⁻¹x) < 1.
```

## 3 诚实边界

* 仍**不证** `(CI)`；本件只使 `I ◁ Γ_F` 成立，从而 `Γ_F/I` 是群——这是 `infl₁` 的**定义前提**。
* `FbarValuationHyp₄` 仍是假设。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Normal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval in
/-- ★★★★★★ **惯性子群正规**：`I ◁ Γ_F`（`Γ_κ = Γ_F/I` 是群，`infl₁` 才有定义前提）。 -/
theorem inertia_normal : (inertia W hval).Normal where
  conj_mem := by
    intro σ hσ τ x hx
    have h1 : W (τ⁻¹ x) ≤ 1 := by rw [hval τ⁻¹ x]; exact hx
    have h2 : W (σ (τ⁻¹ x) - τ⁻¹ x) < 1 := hσ _ h1
    have heq : ((τ * σ * τ⁻¹) x - x) = τ (σ (τ⁻¹ x) - τ⁻¹ x) := by
      simp [map_sub]
    rw [heq, hval τ _]
    exact h2

end Normal

end L20261018

#print axioms L20261018.inertia_normal
