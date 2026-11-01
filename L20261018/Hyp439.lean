import Hyp438

/-!
# S39 第 13 轮（B 第 9 步）：**`∂y` 的陪集依赖 ＋ `A^H`-值性**（`Hyp439`）

## 原文（NSW `prop-1.6.6` 证明后半，`raw/NSW2020.tex:2236–2264`，逐字）

> The function `∂y(σ₁,σ₂) = σ₁y(σ₂) − y(σ₁σ₂) + y(σ₁)` **depends only on the cosets**
> `σ₁H, σ₂H`, i.e. `∂y(σ₁, σ₂τ)` and `∂y(σ₁τ, σ₂)` are independent of `τ ∈ H`.
>
> From `∂∂y = 0` and `∂y(τ,σ) = ∂y(1,σ) = 0`, we now obtain
> `τ∂y(σ₁,σ₂) = ∂y(τσ₁,σ₂) − ∂y(τ,σ₁σ₂) + ∂y(τ,σ₁) = ∂y(σ₁,σ₂)`,
> i.e. `∂y(σ₁,σ₂) ∈ A^H`.

## 本件（照原文三步）

| 件 | 内容 | NSW |
|---|---|---|
| **`d1_tgLift_snd`** | ★★★★ **(A)** `∂y(σ₁, σ₂τ) = ∂y(σ₁,σ₂)` | `:2239–2242` |
| **`d1_tgLift_fst`** | ★★★★ **(B)** `∂y(σ₁τ, σ₂) = ∂y(σ₁,σ₂)` | `:2243–2248` |
| **`d1_tgLift_h_mem`** | `τ ∈ H ⟹ ∂y(τ, σ) = 0` | `:2251` |

⟹ **第 4 项（`∂y` 的陪集依赖）机检完成**；第 3 项（`A^H`-值性）下一轮。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open TauCeti ContCohomology

namespace L20261018

section TgPartials

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (y : G → A)

/-- **(A)** `∂y(σ₁, σ₂·τ) = ∂y(σ₁, σ₂)`（`τ ∈ H`）—— NSW `:2239–2242`。

只用 (ii)：`y(σ₂τ) = y σ₂ + σ₂·y τ`、`y(σ₁σ₂τ) = y(σ₁σ₂) + σ₁σ₂·y τ`。 -/
theorem d1_tgLift_snd
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (σ₁ σ₂ : G) (τ : H) :
    d1 G A y (σ₁, σ₂ * (τ : G)) = d1 G A y (σ₁, σ₂) := by
  rw [d1_apply, d1_apply, hii σ₂ τ, ← mul_assoc, hii (σ₁ * σ₂) τ, smul_add, mul_smul]
  abel

/-- `τ ∈ H` 时 `∂y(τ, σ) = 0` —— NSW `:2251`「`∂y(τ,σ) = ∂y(1,σ) = 0`」的前半。

只用 (iii)：`y(τσ) = y τ + τ·y σ`。 -/
theorem d1_tgLift_h_mem
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (τ : H) (σ : G) :
    d1 G A y ((τ : G), σ) = 0 := by
  rw [d1_apply, hiii σ τ]
  abel

/-- **(B)** `∂y(σ₁·τ, σ₂) = ∂y(σ₁, σ₂)`（`τ ∈ H`）—— NSW `:2243–2248`。

用 (iii) 换掉 `τ·y σ₂`、用 (ii) 换掉 `y(σ₁τ)`，尾项化为 `∂y(σ₁, τσ₂)`，
再用（A）把 `τσ₂ = σ₂·(σ₂⁻¹τσ₂)` 归到 `σ₂`。 -/
theorem d1_tgLift_fst
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (σ₁ σ₂ : G) (τ : H) :
    d1 G A y (σ₁ * (τ : G), σ₂) = d1 G A y (σ₁, σ₂) := by
  -- 第一步：`∂y(σ₁τ, σ₂) = ∂y(σ₁, τσ₂)`（NSW `:2244–2247`）
  have hkey : d1 G A y (σ₁ * (τ : G), σ₂) = d1 G A y (σ₁, (τ : G) * σ₂) := by
    rw [d1_apply, d1_apply, hii σ₁ τ, hiii σ₂ τ, mul_smul, smul_add]
    have hτ : (τ : G) • y σ₂ = y ((τ : G) * σ₂) - y (τ : G) := by
      rw [hiii σ₂ τ]; abel
    rw [hτ, smul_sub, mul_assoc]
    abel
  rw [hkey]
  -- 第二步：`τσ₂ = σ₂ · (σ₂⁻¹τσ₂)`，再用 (A)
  have hmem : σ₂⁻¹ * (τ : G) * σ₂ ∈ H := by
    simpa [inv_inv] using Subgroup.Normal.conj_mem ‹H.Normal› (τ : G) τ.2 σ₂⁻¹
  have hsplit : (τ : G) * σ₂
      = σ₂ * ((⟨σ₂⁻¹ * (τ : G) * σ₂, hmem⟩ : H) : G) := by
    show (τ : G) * σ₂ = σ₂ * (σ₂⁻¹ * (τ : G) * σ₂)
    group
  rw [hsplit]
  exact d1_tgLift_snd H y hii σ₁ σ₂ _

end TgPartials

end L20261018

#print axioms L20261018.d1_tgLift_snd
#print axioms L20261018.d1_tgLift_h_mem
#print axioms L20261018.d1_tgLift_fst
