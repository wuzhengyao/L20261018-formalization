import L20261018.Ch2.Hensel.UnitsCupVanish.Step024_partial_y_ah_valued

/-!
# S39 第 15 轮（B 第 11 步）：**良定义性的下降引理**（`Hyp441`）

## 原文（NSW `prop-1.6.6` 末段，`raw/NSW2020.tex:2256–2272`）

> let `y'` be any cochain with `y'|_H = x` and `∂y'` in `A^H`、只依赖陪集。则 `z = y − y'` 满足
> `z(τ) = 0`（`τ ∈ H`）与 `∂z(τ,σ) = ∂z(1,τσ) = 0`（即 `τz(σ) − z(σ) = 0`），
> 且 `∂z(1,τσ) = ∂z(1,σ)`（即 `z(τσ) = z(σ)`）⟹ `∂y − ∂y' = ∂z` 是 `Z²(G/H,A^H)` 里的上边缘。

## 本件的推导（逐步机检；比原文更直白）

设 `z : G → A`，`z|_H = 0`（`hzH`），`∂z = d¹z` 对两槽的 `H`-右乘都不变（`hleft`／`hright`）。

* **`d1_z_h_zero`**：`τ ∈ H ⟹ ∂z(τ,σ) = 0`。
  `= ∂z(1,σ)`（`hleft`）`= 1•z σ − z(1·σ) + z 1 = 0`。
* **(a) `tgLift_z_right_invariant`**：`z(σ·τ) = z σ`。
  `∂z(σ,τ) = ∂z(σ,1)`（`hright`），左边 `= −z(στ) + z σ`，右边 `= 0`。
* **(b) `tgLift_z_mem_fixed`**：`τ•z σ = z σ`。
  `d1_z_h_zero` 给 `τ•z σ = z(τσ)`；`τσ = σ·(σ⁻¹τσ)`，`σ⁻¹τσ ∈ H`，用 (a)。

⟹ `z` **下降**为 `C¹(G/H, A^H)` 的元素，`∂y − ∂y' = ∂z` 是它的上边缘 ⟹ `tg` 良定义。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open TauCeti ContCohomology

namespace L20261018

section TgDescent

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]

/-- ★★★ **`∂z` 在 `H` 的第一槽上为零**：`τ ∈ H ⟹ ∂z(τ,σ) = 0`（NSW `:2259`）。 -/
theorem d1_z_h_zero (z : G → A)
    (hzH : ∀ τ : H, z (τ : G) = 0)
    (hleft : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z ((τ : G) * σ₁, σ₂) = d1 G A z (σ₁, σ₂))
    (τ : H) (σ : G) :
    d1 G A z ((τ : G), σ) = 0 := by
  have h := hleft 1 σ τ
  rw [mul_one] at h
  have hz1 : z (1 : G) = 0 := by simpa using hzH 1
  rw [h, d1_apply, hz1]
  simp

/-- ★★★★ **(a) 右 `H`-不变**：`z(σ·τ) = z σ`。 -/
theorem tgLift_z_right_invariant (z : G → A)
    (hzH : ∀ τ : H, z (τ : G) = 0)
    (hright : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z (σ₁, σ₂ * (τ : G)) = d1 G A z (σ₁, σ₂))
    (σ : G) (τ : H) :
    z (σ * (τ : G)) = z σ := by
  have h := hright σ 1 τ
  rw [one_mul] at h
  rw [d1_apply, d1_apply] at h
  have hz1 : z (1 : G) = 0 := by simpa using hzH 1
  rw [hzH τ, hz1, mul_one] at h
  simp only [smul_zero, zero_sub, zero_add] at h
  have h2 : -z σ + z σ = (0 : A) := neg_add_cancel _
  rw [h2] at h
  exact eq_of_neg_add_eq_zero h

/-- ★★★★ **(b) 落在 `A^H`**：`τ ∈ H ⟹ τ•z σ = z σ`。 -/
theorem tgLift_z_mem_fixed (z : G → A)
    (hzH : ∀ τ : H, z (τ : G) = 0)
    (hleft : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z ((τ : G) * σ₁, σ₂) = d1 G A z (σ₁, σ₂))
    (hright : ∀ (σ₁ σ₂ : G) (τ : H), d1 G A z (σ₁, σ₂ * (τ : G)) = d1 G A z (σ₁, σ₂))
    (σ : G) (τ : H) :
    (τ : G) • z σ = z σ := by
  have hinv := tgLift_z_right_invariant H z hzH hright
  have h0 : d1 G A z ((τ : G), σ) = 0 := d1_z_h_zero H z hzH hleft τ σ
  rw [d1_apply, hzH τ, add_zero] at h0
  -- `h0 : ↑τ • z σ - z (↑τ * σ) = 0`
  have h3 : (τ : G) • z σ = z ((τ : G) * σ) := sub_eq_zero.mp h0
  rw [h3]
  have hmem : σ⁻¹ * (τ : G) * σ ∈ H := by
    simpa [inv_inv] using Subgroup.Normal.conj_mem ‹H.Normal› (τ : G) τ.2 σ⁻¹
  have hsplit : (τ : G) * σ = σ * ((⟨σ⁻¹ * (τ : G) * σ, hmem⟩ : H) : G) := by
    show (τ : G) * σ = σ * (σ⁻¹ * (τ : G) * σ)
    group
  rw [hsplit]
  exact hinv σ _

end TgDescent

end L20261018

#print axioms L20261018.d1_z_h_zero
#print axioms L20261018.tgLift_z_right_invariant
#print axioms L20261018.tgLift_z_mem_fixed
