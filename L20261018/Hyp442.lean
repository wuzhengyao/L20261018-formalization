import L20261018.Hyp441

/-!
# S39 第 16 轮（B 第 12 步）：**`∂y` 沿陪集的下降**（`Hyp442`）

## 目标

NSW `prop-1.6.6`：`tg[x] = [∂y]`，其中 `∂y` 经「只依赖陪集」下降为
`Z²(G/H, A^H)` 的上闭链。本件把**下降的相容性**（＝良定义性）与**下降后的余链**做实。

## 机检件

| 件 | 内容 |
|---|---|
| **`d1_tgLift_quot_compat`** | ★★★★★ 若 `σ₁ ~ σ₁'`、`σ₂ ~ σ₂'`（同一陪集），则 `∂y(σ₁,σ₂) = ∂y(σ₁',σ₂')` |
| **`tgCocycle`** | 下降后的 2-余链 `G/H → G/H → A^H`（用截面取值，`A^H`-值性由 `d1_tgLift_mem_fixed`） |

`quot_compat` 的证明：`σ₁' = σ₁·τ₁`、`σ₂' = σ₂·τ₂`（`τᵢ ∈ H`，由 `QuotientGroup.eq` 取）
⟹ 先用 (B) 归 `σ₁`、再用 (A) 归 `σ₂`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgQuot

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (y : G → A)

/-- ★★★★★ **`∂y` 沿 `G → G/H` 的下降相容性**（NSW「只依赖陪集」的定量形式）。

同一对陪集的两个代表给出同一个 `∂y` 值。 -/
theorem d1_tgLift_quot_compat
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    {σ₁ σ₂ σ₁' σ₂' : G}
    (h₁ : (QuotientGroup.mk σ₁ : G ⧸ H) = QuotientGroup.mk σ₁')
    (h₂ : (QuotientGroup.mk σ₂ : G ⧸ H) = QuotientGroup.mk σ₂') :
    d1 G A y (σ₁, σ₂) = d1 G A y (σ₁', σ₂') := by
  -- 取 `τ₁, τ₂ ∈ H` 使 `σ₁' = σ₁ · τ₁`、`σ₂' = σ₂ · τ₂`
  have hm₁ : σ₁⁻¹ * σ₁' ∈ H := (QuotientGroup.eq).mp h₁
  have hm₂ : σ₂⁻¹ * σ₂' ∈ H := (QuotientGroup.eq).mp h₂
  have hdec₁ : σ₁' = σ₁ * ((⟨σ₁⁻¹ * σ₁', hm₁⟩ : H) : G) := by
    show σ₁' = σ₁ * (σ₁⁻¹ * σ₁')
    group
  have hdec₂ : σ₂' = σ₂ * ((⟨σ₂⁻¹ * σ₂', hm₂⟩ : H) : G) := by
    show σ₂' = σ₂ * (σ₂⁻¹ * σ₂')
    group
  rw [hdec₁, hdec₂]
  rw [d1_tgLift_fst H y hii hiii σ₁ _ ⟨σ₁⁻¹ * σ₁', hm₁⟩]
  rw [d1_tgLift_snd H y hii σ₁ σ₂ ⟨σ₂⁻¹ * σ₂', hm₂⟩]

end TgQuot

section TgCocycleDef

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)

/-- ★★★★★ **下降后的 2-余链** `G/H → G/H → A^H`（NSW 的 `∂y` 经陪集下降）。

取 `∂y` 在截面代表处的值；`A^H`-值性由 `d1_tgLift_mem_fixed` 供给。
由 `d1_tgLift_quot_compat`，该定义**与截面选择无关**。 -/
noncomputable def tgCocycle (y : G → A)
    (hii : ∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G))
    (hiii : ∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ)
    (q₁ q₂ : G ⧸ H) : ↥(FixedPoints.addSubgroup (↥H) A) :=
  ⟨d1 G A y (S.s q₁, S.s q₂),
    fun τ => d1_tgLift_mem_fixed H y hii hiii (S.s q₁) (S.s q₂) τ⟩

end TgCocycleDef

end L20261018

#print axioms L20261018.d1_tgLift_quot_compat
#print axioms L20261018.tgCocycle
