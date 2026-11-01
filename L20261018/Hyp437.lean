import Hyp436

/-!
# S39 第 11 轮（B 第 7 步）：**`tg` 的相容条件 (1) ＋ NSW 的 (iii)**（`Hyp437`）

## 原文（NSW `prop-1.6.6`，`raw/NSW2020.tex:2226–2240`，逐字）

NSW 的 (iii) 证明用 **(1)**（即 `y(sγ)` 的相容条件，`:2210–2215`）：

> **(1)**  `sγ · x((sγ)⁻¹ τ sγ) = x(τ) + τ·y(sγ) − y(sγ)`  （`τ ∈ H`）

NSW 的推导（`:2226–2240`）：

```
y(τg) = y(g) + g x((g)⁻¹τg) = y(g) + x(τ) + τ y(g) − y(g) = x(τ) + τ y(g)      -- 用 (1)
y(τσ) = y(τgτ') = y(τg) + τg x(τ') = x(τ) + τ y(g) + τg x(τ') = y(τ) + τ y(σ)
```

## 本件（本轮）

| 件 | 内容 |
|---|---|
| **`conjH`** | `τ` 关于 `sγ` 的共轭 `(sγ)⁻¹ τ sγ ∈ H`（用 `Subgroup.Normal.conj_mem'`） |
| **`hpart_section`** | `hpart (sγ) = 1` |
| **`hpart_conj`** | `hpart (τ·sγ) = conjH γ τ` |
| **`tgLift_apply_section`** | `y(sγ) = yx γ`（需 `x 1 = 0`） |
| **`x_one_eq_zero`** | `x 1 = 0`（由 `x` 的 1-上闭链条件） |
| **`TgCompat`** | ★★★★★ **相容条件 (1)**（作为具名 `Prop`） |
| **`tgLift_apply_h_mul_section`** | ★★★★ `y(τ·sγ) = x(τ) + τ·y(sγ)`（NSW 第一行） |
| **`tgLift_mul_left`** | ★★★★★ **NSW (iii)** `y(τσ) = y(τ) + τ·y(σ)` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace L20261018

open scoped Classical

section TgCompat

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)

/-- ★★★ **`τ` 关于 `sγ` 的共轭** `(sγ)⁻¹ τ sγ ∈ H`（`H` 正规）。 -/
noncomputable def conjH (γ : G ⧸ H) (τ : H) : H :=
  ⟨(S.s γ)⁻¹ * (τ : G) * S.s γ, Subgroup.Normal.conj_mem' ‹H.Normal› (τ : G) τ.2 (S.s γ)⟩

/-- `H` 上 1-上闭链在 `1` 处为零。 -/
theorem x_one_eq_zero {x : G → A}
    (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G)) :
    x 1 = 0 := by
  have h := hx 1 1
  rw [Subgroup.coe_one, one_mul, one_smul] at h
  have h2 : x 1 + x 1 = x 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- `hpart (sγ) = 1`。 -/
theorem hpart_section (σ : G) : hpart H S (sσ H S σ) = 1 := by
  apply Subtype.ext
  show (sσ H S (sσ H S σ))⁻¹ * sσ H S σ = 1
  have h1 : QuotientGroup.mk (sσ H S σ) = QuotientGroup.mk σ := S.sec (QuotientGroup.mk σ)
  have h2 : sσ H S (sσ H S σ) = sσ H S σ := by
    show S.s (QuotientGroup.mk (sσ H S σ)) = S.s (QuotientGroup.mk σ)
    rw [h1]
  rw [h2, inv_mul_cancel]

/-- ★★★ `hpart (τ·sγ) = conjH γ τ`。 -/
theorem hpart_conj (σ : G) (τ : H) :
    hpart H S ((τ : G) * sσ H S σ) = conjH H S (QuotientGroup.mk σ) τ := by
  apply Subtype.ext
  show (sσ H S ((τ : G) * sσ H S σ))⁻¹ * ((τ : G) * sσ H S σ)
      = (S.s (QuotientGroup.mk σ))⁻¹ * (τ : G) * S.s (QuotientGroup.mk σ)
  have hmk : (QuotientGroup.mk ((τ : G) * sσ H S σ) : G ⧸ H) = QuotientGroup.mk σ := by
    rw [QuotientGroup.mk_mul H,
      show (QuotientGroup.mk (τ : G) : G ⧸ H) = 1 from
        (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2, one_mul]
    exact S.sec (QuotientGroup.mk σ)
  have hsp : sσ H S ((τ : G) * sσ H S σ) = sσ H S σ := by
    show S.s (QuotientGroup.mk ((τ : G) * sσ H S σ)) = S.s (QuotientGroup.mk σ)
    rw [hmk]
  rw [hsp]
  show (sσ H S σ)⁻¹ * ((τ : G) * sσ H S σ) = (sσ H S σ)⁻¹ * (τ : G) * sσ H S σ
  rw [mul_assoc]

/-- `y(sγ) = yx γ`（需 `x 1 = 0`）。 -/
theorem tgLift_apply_section (yx : G ⧸ H → A) (x : G → A) (hx1 : x 1 = 0) (σ : G) :
    tgLift H S yx x (sσ H S σ) = yx (QuotientGroup.mk σ) := by
  have hmk : QuotientGroup.mk (sσ H S σ) = QuotientGroup.mk σ := S.sec (QuotientGroup.mk σ)
  show yx (QuotientGroup.mk (sσ H S σ)) + sσ H S (sσ H S σ) • x (hpart H S (sσ H S σ) : G)
      = yx (QuotientGroup.mk σ)
  rw [hmk, hpart_section H S σ]
  simp [hx1]

/-- ★★★★★ **NSW 的相容条件 (1)**（`:2210–2215`，逐字）：

> `sγ · x((sγ)⁻¹τsγ) = x(τ) + τ·y(sγ) − y(sγ)`   （`τ ∈ H`，`γ ∈ G/H`）

NSW 原文把它记为 **(1)**，并说明它存在是因为 `[x]` 在共轭下不变（`[x] ∈ H¹(H,A)^{G/H}`）。 -/
def TgCompat (yx : G ⧸ H → A) (x : G → A) : Prop :=
  ∀ (γ : G ⧸ H) (τ : H),
    S.s γ • x (conjH H S γ τ : G) = x (τ : G) + (τ : G) • yx γ - yx γ

variable {S}

/-- ★★★★ **NSW 的第一行**：`y(τ·sγ) = x(τ) + τ·y(sγ)`（由 (1)）。 -/
theorem tgLift_apply_h_mul_section (yx : G ⧸ H → A) (x : G → A) (hx1 : x 1 = 0)
    (hc : TgCompat H S yx x) (σ : G) (τ : H) :
    tgLift H S yx x ((τ : G) * sσ H S σ)
      = x (τ : G) + (τ : G) • yx (QuotientGroup.mk σ) := by
  have hmk : (QuotientGroup.mk ((τ : G) * sσ H S σ) : G ⧸ H) = QuotientGroup.mk σ := by
    rw [QuotientGroup.mk_mul H,
      show (QuotientGroup.mk (τ : G) : G ⧸ H) = 1 from
        (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2, one_mul]
    exact S.sec (QuotientGroup.mk σ)
  have hsp : sσ H S ((τ : G) * sσ H S σ) = sσ H S σ := by
    show S.s (QuotientGroup.mk ((τ : G) * sσ H S σ)) = S.s (QuotientGroup.mk σ)
    rw [hmk]
  show yx (QuotientGroup.mk ((τ : G) * sσ H S σ))
      + sσ H S ((τ : G) * sσ H S σ) • x (hpart H S ((τ : G) * sσ H S σ) : G)
      = x (τ : G) + (τ : G) • yx (QuotientGroup.mk σ)
  rw [hmk, hsp, hpart_conj H S σ τ]
  have h := hc (QuotientGroup.mk σ) τ
  rw [show sσ H S σ = S.s (QuotientGroup.mk σ) from rfl, h]
  abel

/-- ★★★★★ **NSW (iii)**：`y(τσ) = y(τ) + τ·y(σ)`（`τ ∈ H`）。

证明路线逐字照 NSW：`σ = sγ·τ'`（`τ' = hpart σ`），
用 (ii) 两次 ＋ 上一行的 `y(τ·sγ) = x(τ) + τ·y(sγ)`。 -/
theorem tgLift_mul_left (yx : G ⧸ H → A) (x : G → A)
    (hyx1 : yx 1 = 0)
    (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G))
    (hc : TgCompat H S yx x) (σ : G) (τ : H) :
    tgLift H S yx x ((τ : G) * σ) = tgLift H S yx x (τ : G) + (τ : G) • tgLift H S yx x σ := by
  have hx1 : x 1 = 0 := x_one_eq_zero (H := H) hx
  -- `σ = sσ · hpart σ`
  have hdecomp : (τ : G) * σ = ((τ : G) * sσ H S σ) * (hpart H S σ : G) := by
    rw [mul_assoc, s_mul_hpart H S σ]
  have hσ : σ = sσ H S σ * (hpart H S σ : G) := (s_mul_hpart H S σ).symm
  -- (ii) 两次
  have h1 := tgLift_mul_right H S yx x hyx1 hx ((τ : G) * sσ H S σ) (hpart H S σ)
  have h2 := tgLift_mul_right H S yx x hyx1 hx (sσ H S σ) (hpart H S σ)
  -- `y(τ)` 与 `y(hpart σ)`
  have hyτ : tgLift H S yx x (τ : G) = x (τ : G) :=
    tgLift_apply_hpart H S yx x hyx1 τ.2
  have hys : tgLift H S yx x (hpart H S σ : G) = x (hpart H S σ : G) :=
    tgLift_apply_hpart H S yx x hyx1 (hpart H S σ).2
  have hsec := tgLift_apply_h_mul_section H yx x hx1 hc σ τ
  rw [hdecomp, h1, hys, hsec, hyτ]
  show x (τ : G) + (τ : G) • yx (QuotientGroup.mk σ) + ((τ : G) * sσ H S σ) • x (hpart H S σ : G)
      = x (τ : G) + (τ : G) • (yx (QuotientGroup.mk σ) + sσ H S σ • x (hpart H S σ : G))
  rw [smul_add, smul_smul]
  abel

end TgCompat

end L20261018

#print axioms L20261018.conjH
#print axioms L20261018.x_one_eq_zero
#print axioms L20261018.hpart_section
#print axioms L20261018.hpart_conj
#print axioms L20261018.tgLift_apply_section
#print axioms L20261018.tgLift_apply_h_mul_section
#print axioms L20261018.tgLift_mul_left
