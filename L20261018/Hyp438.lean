import Hyp437

/-!
# S39 第 12 轮（B 第 8 步）：**NSW 的 `y` 存在**（`Hyp438`）

## 原文

NSW `prop-1.6.6`（`raw/NSW2020.tex:2210–2215`）：因 `[x] ∈ H¹(H,A)^{G/H}` 共轭不变，
对每个 `γ ∈ G/H` 存在 `y(sγ) ∈ A` 使

> **(1)** `sγ · x((sγ)⁻¹τsγ) = x(τ) + τ·y(sγ) − y(sγ)`　（`τ ∈ H`）

再令 `y(σ) = y(sγ) + sγ·x(τ)`（`σ = sγτ`），则 (i)(ii)(iii) 成立（`:2226–2240`）。

## 本件：把「共轭不变」写成可判定的 `Prop`，并合成存在定理

`ConjInvariant x`：

```
∀ γ, ∃ a : A, ∀ τ : H,  τ • a − a  =  sγ • x((sγ)⁻¹τsγ) − x(τ)
```

左边正是 `d0 ↥H A a (τ)`（`Hyp` 的 `d0_apply`：`τ • a − a`）⟹ 该 `Prop` 就是
「`τ ↦ sγ•x((sγ)⁻¹τsγ)` 与 `x` 在 `H¹(H,A)` 中同类」，即 `[x]` 在 `γ`-共轭下不变。

**机检件**

| 件 | 内容 |
|---|---|
| **`ConjInvariant`** | 「`[x]` 共轭不变」的可判定形式（每个 `γ` 一个 `a`） |
| **`conjH_one`** | `conjH 1 τ = τ` |
| **`exists_tgCompat_normalized`** | ★★★★★ **`TgCompat` 的实例化**（并把 `yx 1 = 0` 归一化） |
| **`exists_tgLift`** | ★★★★★★ **NSW 的 `y` 存在**：`y 1 = 0` ＋ **(i)** ＋ **(ii)** ＋ **(iii)** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace L20261018

open scoped Classical

section TgExistence

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]
variable (S : TgSection H)

/-- ★★★★★ **「`[x]` 在共轭下不变」的可判定形式**。

对每个 `γ ∈ G/H` 存在 `a ∈ A`，使 `τ ↦ sγ•x((sγ)⁻¹τsγ) − x(τ)` 恰为 `a` 在 `H` 上的
**1-上边缘**（`d⁰ a (τ) = τ•a − a`）。这正是 `[x] ∈ H¹(H,A)^{G/H}` 的展开。 -/
def ConjInvariant (x : G → A) : Prop :=
  ∀ γ : G ⧸ H, ∃ a : A, ∀ τ : H,
    (τ : G) • a - a = S.s γ • x (conjH H S γ τ : G) - x (τ : G)

/-- `conjH 1 τ = τ`。 -/
theorem conjH_one (τ : H) : conjH H S (1 : G ⧸ H) τ = τ := by
  apply Subtype.ext
  show (S.s (1 : G ⧸ H))⁻¹ * (τ : G) * S.s (1 : G ⧸ H) = (τ : G)
  simp [S.one]

/-- ★★★★★ **`TgCompat` 的实例化**（含 `yx 1 = 0` 归一化）。

由 `ConjInvariant` 用 `Classical.choose` 取 `yx`；
`TgCompat` 在 `γ = 1` 处给出 `τ • yx 1 − yx 1 = 0`，故 `γ ↦ yx γ − yx 1` 仍满足 `TgCompat`
且归一化到 `0`。 -/
theorem exists_tgCompat_normalized (x : G → A) (hinv : ConjInvariant H S x) :
    ∃ yx : G ⧸ H → A, yx 1 = 0 ∧ TgCompat H S yx x := by
  classical
  choose yx hyx using hinv
  -- `γ = 1`：`τ • yx 1 − yx 1 = 0`
  have hone : ∀ τ : H, (τ : G) • yx 1 - yx 1 = 0 := by
    intro τ
    have h := hyx (1 : G ⧸ H) τ
    rw [conjH_one H S τ] at h
    simp only [S.one, inv_one, one_mul, one_smul] at h
    rw [sub_self] at h
    exact h
  refine ⟨fun γ => yx γ - yx 1, ?_, ?_⟩
  · show yx 1 - yx 1 = 0
    abel
  · intro γ τ
    have h := hyx γ τ
    have h1 := hone τ
    have hb : (τ : G) • yx γ = (S.s γ • x (conjH H S γ τ : G) - x (τ : G)) + yx γ :=
      (sub_eq_iff_eq_add).mp h
    have h1' : (τ : G) • yx 1 = yx 1 := sub_eq_zero.mp h1
    show S.s γ • x (conjH H S γ τ : G)
        = x (τ : G) + (τ : G) • (yx γ - yx 1) - (yx γ - yx 1)
    rw [smul_sub, h1', hb]
    abel

/-- ★★★★★★ **NSW 的 `y` 存在**（`prop-1.6.6` 的构造部分，`raw/NSW2020.tex:2206–2240`）。

设 `x : G → A` 是 `H` 上的 1-上闭链（`hx`），且 `[x]` 共轭不变（`hinv`）。
则存在 `y : G → A` 满足

* `y 1 = 0`（NSW 的归一化）
* **(i)** `y|_H = x`
* **(ii)** `y(στ) = y(σ) + σ·y(τ)`
* **(iii)** `y(τσ) = y(τ) + τ·y(σ)`

⟹ 下一步即可定义 `tg[x] := [∂y]`（`∂y` 即 `d1 y`），并证其落在 `A^H`、只依赖陪集。 -/
theorem exists_tgLift (x : G → A)
    (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G))
    (hinv : ConjInvariant H S x) :
    ∃ y : G → A, y 1 = 0 ∧
      (∀ τ : H, y (τ : G) = x (τ : G)) ∧
      (∀ (σ : G) (τ : H), y (σ * (τ : G)) = y σ + σ • y (τ : G)) ∧
      (∀ (σ : G) (τ : H), y ((τ : G) * σ) = y (τ : G) + (τ : G) • y σ) := by
  obtain ⟨yx, hyx1, hc⟩ := exists_tgCompat_normalized H S x hinv
  refine ⟨tgLift H S yx x, ?_, ?_, ?_, ?_⟩
  · -- `y 1 = 0`
    have hx1 : x 1 = 0 := by
      have h := hx 1 1
      simp only [Subgroup.coe_one, one_mul, one_smul] at h
      have h2 : x 1 + x 1 = x 1 + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    show yx (QuotientGroup.mk 1) + sσ H S 1 • x (hpart H S 1 : G) = 0
    have hmk1 : (QuotientGroup.mk (1 : G) : G ⧸ H) = 1 := by simp
    have hsp1 : sσ H S 1 = 1 := by
      show S.s (QuotientGroup.mk (1 : G)) = 1
      rw [hmk1]; exact S.one
    rw [hmk1, hyx1, hsp1, one_smul]
    -- 目标是 `0 + x (hpart 1) = 0`；`hpart 1 = 1`
    have hhp1 : (hpart H S (1 : G) : G) = 1 := by
      show (sσ H S 1)⁻¹ * 1 = 1
      rw [hsp1, inv_one, one_mul]
    rw [hhp1, hx1, add_zero]
  · intro τ
    exact tgLift_apply_hpart (H := H) (S := S) (yx := yx) (x := x) hyx1 τ.2
  · intro σ τ
    exact tgLift_mul_right (H := H) (S := S) (yx := yx) (x := x) hyx1 hx σ τ
  · intro σ τ
    exact tgLift_mul_left (H := H) (S := S) (yx := yx) (x := x) hyx1 hx hc σ τ

end TgExistence

end L20261018

#print axioms L20261018.conjH_one
#print axioms L20261018.exists_tgCompat_normalized
#print axioms L20261018.exists_tgLift
