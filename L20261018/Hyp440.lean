import L20261018.Hyp439

/-!
# S39 第 14 轮（B 第 10 步）：**`∂y` 的 `A^H`-值性**（`Hyp440`）

## 原文（NSW `prop-1.6.6` 证明，`raw/NSW2020.tex:2249–2253`，逐字）

> From `∂∂y = 0` and `∂y(τ,σ) = ∂y(1,σ) = 0`, we now obtain
> `τ∂y(σ₁,σ₂) = ∂y(τσ₁,σ₂) − ∂y(τ,σ₁σ₂) + ∂y(τ,σ₁) = ∂y(σ₁,σ₂)`,
> i.e. `∂y(σ₁,σ₂) ∈ A^H`.

## 三个输入

| 输入 | 件 | 来源 |
|---|---|---|
| `∂∂y = 0` | `d2_comp_d1_apply`（`d²(d¹y) = 0`，库内） | `LowDegree` |
| `∂y(τσ₁,σ₂) = ∂y(σ₁,σ₂)` | **(B)** ＋ 共轭 `τσ₁ = σ₁·(σ₁⁻¹τσ₁)` | `Hyp439.d1_tgLift_fst` |
| `∂y(τ,·) = 0` | `Hyp439.d1_tgLift_h_mem` | `Hyp439` |

**注意方向**：`d2` 的余链恒等式给的是**左乘** `τσ₁`（`(g*h, j)`），
而 (B) 是**右乘** `σ₁τ` —— 二者靠 `H` 正规性（`σ₁⁻¹τσ₁ ∈ H`）桥接，这正是 NSW 原文的用法。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgFixed

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (y : G → A)

/-- ★★★★★ **(C) `∂y` 落在 `A^H` 上** —— NSW `:2249–2253`。

`τ • ∂y(σ₁,σ₂) = ∂y(σ₁,σ₂)`，即 `∂y(σ₁,σ₂) ∈ A^H = FixedPoints.addSubgroup H A`。 -/
theorem d1_tgLift_mem_fixed
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (σ₁ σ₂ : G) (τ : H) :
    (τ : G) • d1 G A y (σ₁, σ₂) = d1 G A y (σ₁, σ₂) := by
  -- `∂∂y = 0` 在 `(τ, σ₁, σ₂)` 处
  have hcomp : d2 G A (d1 G A y) ((τ : G), σ₁, σ₂) = 0 := by
    rw [d2_comp_d1_apply]
    simp
  rw [d2_apply] at hcomp
  -- `∂y(τσ₁, σ₂) = ∂y(σ₁, σ₂)`：以共轭元 `σ₁⁻¹τσ₁ ∈ H` 用 (B)
  have hB : d1 G A y ((τ : G) * σ₁, σ₂) = d1 G A y (σ₁, σ₂) := by
    have hmem : σ₁⁻¹ * (τ : G) * σ₁ ∈ H := by
      simpa [inv_inv] using Subgroup.Normal.conj_mem ‹H.Normal› (τ : G) τ.2 σ₁⁻¹
    have hsplit : (τ : G) * σ₁
        = σ₁ * ((⟨σ₁⁻¹ * (τ : G) * σ₁, hmem⟩ : H) : G) := by
      show (τ : G) * σ₁ = σ₁ * (σ₁⁻¹ * (τ : G) * σ₁)
      group
    rw [hsplit]
    exact d1_tgLift_fst H y hii hiii σ₁ σ₂ _
  have h0a : d1 G A y ((τ : G), σ₁ * σ₂) = 0 := d1_tgLift_h_mem H y hiii τ (σ₁ * σ₂)
  have h0b : d1 G A y ((τ : G), σ₁) = 0 := d1_tgLift_h_mem H y hiii τ σ₁
  rw [hB, h0a, h0b] at hcomp
  have hzero : (τ : G) • d1 G A y (σ₁, σ₂) - d1 G A y (σ₁, σ₂) = 0 := by
    simpa using hcomp
  exact sub_eq_zero.mp hzero

end TgFixed

/-! ## 封顶：`∂y` 的全部性质打包（NSW `prop-1.6.6` 前半） -/

section TgPackage

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)

/-- ★★★★★★ **NSW `prop-1.6.6` 的 `∂y` 部分封顶**：

由 `x`（`H` 上 1-上闭链）＋「`[x]` 共轭不变」，得 `y : G → A` 使
* `y 1 = 0`、`y|_H = x`（归一化 ＋ (i)）；
* `∂y = d¹y` **只依赖陪集**（`σ₁` 侧与 `σ₂` 侧的 `H`-右乘都不变）；
* `∂y` **落在 `A^H`**（`τ • ∂y(σ₁,σ₂) = ∂y(σ₁,σ₂)`）。

⟹ `∂y` 沿 `G → G/H` 下降为 `Z²(G/H, A^H)` 的一个上闭链 —— 即 **`tg[x] := [∂y]` 已可定义**。 -/
theorem exists_tg_partial (x : G → A)
    (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G))
    (hinv : ConjInvariant H S x) :
    ∃ y : G → A, y 1 = 0 ∧
      (∀ τ : H, y (τ : G) = x (τ : G)) ∧
      (∀ (σ₁ σ₂ : G) (τ : H), d1 G A y (σ₁ * (τ : G), σ₂) = d1 G A y (σ₁, σ₂)) ∧
      (∀ (σ₁ σ₂ : G) (τ : H), d1 G A y (σ₁, σ₂ * (τ : G)) = d1 G A y (σ₁, σ₂)) ∧
      (∀ (σ₁ σ₂ : G) (τ : H), (τ : G) • d1 G A y (σ₁, σ₂) = d1 G A y (σ₁, σ₂)) := by
  obtain ⟨y, hy1, hyi, hyii, hyiii⟩ := exists_tgLift H S x hx hinv
  exact ⟨y, hy1, hyi,
    fun σ₁ σ₂ τ => d1_tgLift_fst H y hyii hyiii σ₁ σ₂ τ,
    fun σ₁ σ₂ τ => d1_tgLift_snd H y hyii σ₁ σ₂ τ,
    fun σ₁ σ₂ τ => d1_tgLift_mem_fixed H y hyii hyiii σ₁ σ₂ τ⟩

end TgPackage

end L20261018

#print axioms L20261018.d1_tgLift_mem_fixed
#print axioms L20261018.exists_tg_partial
