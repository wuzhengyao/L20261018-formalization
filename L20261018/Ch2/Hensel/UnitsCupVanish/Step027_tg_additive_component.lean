import L20261018.Ch2.Hensel.UnitsCupVanish.Step026_partial_y_descent

/-!
# S39 第 17 轮（B 第 13 步）：**`tg` 的加性组件**（`Hyp443`）

## 目标（第 5c 项）

把 `tg` 装成 `AddMonoidHom`，关键在**加性**：
`tg[x₁ + x₂] = tg[x₁] + tg[x₂]`。

由于 `tg[x] = [∂y_x]` 而 `y_x` 由 `Classical.choose` 取，加性不能靠「`y` 线性」直接得到；
但它分解为两步：

1. **`ConjInvariant` 对加法封闭**（本轮）：`ConjInvariant x₁ → ConjInvariant x₂ → ConjInvariant (x₁+x₂)`，
   取 `a_γ = a₁γ + a₂γ`（`τ•(a₁+a₂) − (a₁+a₂)` 线性分解）。
2. **下降余链加性**（本轮）：`∂(y₁ + y₂) = ∂y₁ + ∂y₂` ⟹ `tgCocycle` 加性。
3. **两支 `y` 之差的上边缘性**（已有）：`Hyp441` 的三条下降引理 ＋ `Hyp442` 的
   `d1_tgLift_quot_compat` ⟹ 不同选择给出的 `∂y` 只差一上边缘 ⟹ 加性在**上同调层**成立。

**本轮做 1、2 两步。**

| 件 | 内容 |
|---|---|
| **`conjInvariant_add`** | ★★★★ `ConjInvariant` 对加法封闭 |
| **`tgLift_hii_add`** / **`tgLift_hiii_add`** | 两条余链条件对加法封闭 |
| **`tgCocycle_add`** | ★★★★★ 下降余链的加性：`∂(y₁+y₂) = ∂y₁ + ∂y₂` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgAdd

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)

/-- ★★★★ **`ConjInvariant` 对加法封闭**（取 `a_γ = a₁γ + a₂γ`）。 -/
theorem conjInvariant_add {x₁ x₂ : G → A}
    (h₁ : ConjInvariant H S x₁) (h₂ : ConjInvariant H S x₂) :
    ConjInvariant H S (x₁ + x₂) := by
  intro γ
  obtain ⟨a₁, ha₁⟩ := h₁ γ
  obtain ⟨a₂, ha₂⟩ := h₂ γ
  refine ⟨a₁ + a₂, fun τ => ?_⟩
  have h1 := ha₁ τ
  have h2 := ha₂ τ
  simp only [Pi.add_apply]
  rw [smul_add]
  -- 目标：`τ•a₁ + τ•a₂ − (a₁ + a₂) = sγ•(x₁ c + x₂ c) − (x₁ ↑τ + x₂ ↑τ)`
  rw [smul_add]
  have : (τ : G) • a₁ + (τ : G) • a₂ - (a₁ + a₂)
      = ((τ : G) • a₁ - a₁) + ((τ : G) • a₂ - a₂) := by abel
  rw [this, h1, h2]
  abel

/-- 余链条件 (ii) 对加法封闭。 -/
theorem tgLift_hii_add {y₁ y₂ : G → A}
    (h₁ : ∀ (σ : G) (τ : H), y₁ (σ * (τ : G)) = y₁ σ + σ • y₁ (τ : G))
    (h₂ : ∀ (σ : G) (τ : H), y₂ (σ * (τ : G)) = y₂ σ + σ • y₂ (τ : G)) :
    ∀ (σ : G) (τ : H), (y₁ + y₂) (σ * (τ : G)) = (y₁ + y₂) σ + σ • (y₁ + y₂) (τ : G) := by
  intro σ τ
  simp only [Pi.add_apply, h₁, h₂, smul_add]
  abel

/-- 余链条件 (iii) 对加法封闭。 -/
theorem tgLift_hiii_add {y₁ y₂ : G → A}
    (h₁ : ∀ (σ : G) (τ : H), y₁ ((τ : G) * σ) = y₁ (τ : G) + (τ : G) • y₁ σ)
    (h₂ : ∀ (σ : G) (τ : H), y₂ ((τ : G) * σ) = y₂ (τ : G) + (τ : G) • y₂ σ) :
    ∀ (σ : G) (τ : H), (y₁ + y₂) ((τ : G) * σ) = (y₁ + y₂) (τ : G) + (τ : G) • (y₁ + y₂) σ := by
  intro σ τ
  simp only [Pi.add_apply, h₁, h₂, smul_add]
  abel

/-- ★★★★★ **下降余链的加性**：`∂(y₁ + y₂) = ∂y₁ + ∂y₂`（逐点）。 -/
theorem tgCocycle_add (y₁ y₂ : G → A)
    (hii₁ : ∀ (σ : G) (τ : H), y₁ (σ * (τ : G)) = y₁ σ + σ • y₁ (τ : G))
    (hiii₁ : ∀ (σ : G) (τ : H), y₁ ((τ : G) * σ) = y₁ (τ : G) + (τ : G) • y₁ σ)
    (hii₂ : ∀ (σ : G) (τ : H), y₂ (σ * (τ : G)) = y₂ σ + σ • y₂ (τ : G))
    (hiii₂ : ∀ (σ : G) (τ : H), y₂ ((τ : G) * σ) = y₂ (τ : G) + (τ : G) • y₂ σ)
    (q₁ q₂ : G ⧸ H) :
    tgCocycle H S (y₁ + y₂) (tgLift_hii_add H hii₁ hii₂)
        (tgLift_hiii_add H hiii₁ hiii₂) q₁ q₂
      = tgCocycle H S y₁ hii₁ hiii₁ q₁ q₂ + tgCocycle H S y₂ hii₂ hiii₂ q₁ q₂ := by
  apply Subtype.ext
  show d1 G A (y₁ + y₂) (S.s q₁, S.s q₂)
      = d1 G A y₁ (S.s q₁, S.s q₂) + d1 G A y₂ (S.s q₁, S.s q₂)
  rw [d1_apply, d1_apply, d1_apply]
  simp only [Pi.add_apply, smul_add]
  abel

end TgAdd

end L20261018

#print axioms L20261018.conjInvariant_add
#print axioms L20261018.tgLift_hii_add
#print axioms L20261018.tgLift_hiii_add
#print axioms L20261018.tgCocycle_add
