import L20261018.Ch2.Hensel.UnitsCupVanish.Step019_b_tension_resolved

/-!
# S39 第 10 轮（B 第 6 步）：**`tg` 的定义层 ＋ NSW 的 (i)(ii)**（`Hyp436`）

## 原文（NSW 2020 `prop-1.6.6`，`raw/NSW2020.tex:2193–2240`，逐字）

设 `H ◁ G` 闭正规、`A` 为 `G`-模。取连续截面 `s : G/H → G`，`s1 = 1`。
对 1-上闭链 `x : H → A`（其类 `[x] ∈ H¹(H,A)^{G/H}` 共轭不变），NSW 构造 `y : G → A` 满足

* **(i)** `y|_H = x`；
* **(ii)** `y(στ) = y(σ) + σy(τ)`（`σ ∈ G`, `τ ∈ H`）；
* **(iii)** `y(τσ) = y(τ) + τy(σ)`（`σ ∈ G`, `τ ∈ H`），

然后 **`tg[x] = [∂y]`**，且 `∂y` 落在 `A^H` 上、只依赖陪集。

显式公式（NSW 原文）：对 `σ = sγ·τ` 置 `y(σ) = y(sγ) + sγ·x(τ)`。

## 本件（本轮只做**不需要 `y(sγ)` 任何条件**的部分）

本件把 `y(sγ)` 提为**自由数据** `yx : G ⧸ H → A`，定义

```
tgLift yx x σ  =  yx (σH)  +  s(σH) • x (hpart σ)        -- `hpart σ = (s(σH))⁻¹ · σ ∈ H`
```

并机检 NSW 的 **(i)** 与 **(ii)** —— 二者只用「`x` 是 `H` 上的 1-上闭链」＋`yx 1 = 0`，
**不涉及** `y(sγ)` 的相容条件（那条件只为 (iii) 与 `A^H`-值性所需，留下轮）。

## 机检件

| 件 | 内容 |
|---|---|
| **`TgSection`** | 截面 `s`（`s1 = 1` ＋ `mk (s q) = q`） |
| **`hpart`** | `σ` 的 `H`-分量；**`s_mul_hpart : s(σH) · hpart σ = σ`**（NSW 的 `σ = sγ·τ` 分解） |
| **`tgLift`** | 显式公式 `y(σ) = yx(σH) + s(σH) • x(hpart σ)` |
| **`tgLift_apply_hpart`** | ★★★ **(i)** `τ ∈ H ⟹ tgLift yx x τ = x τ` |
| **`tgLift_mul_right`** | ★★★★ **(ii)** `tgLift yx x (σ*τ) = tgLift yx x σ + σ • tgLift yx x τ` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace L20261018

open scoped Classical

section TgCore

variable {G : Type*} [Group G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A]
variable (H : Subgroup G) [H.Normal]

/-- **NSW `prop-1.6.6` 的截面数据**：`s : G⧸H → G` 是投影的集合论截面，且 `s 1 = 1`。 -/
structure TgSection where
  /-- 截面本身。 -/
  s : G ⧸ H → G
  /-- 截面条件：`s` 的像落在它自己的陪集里。 -/
  sec : ∀ q : G ⧸ H, QuotientGroup.mk (s q) = q
  /-- NSW 的归一化 `s1 = 1`。 -/
  one : s 1 = 1

variable (S : TgSection H)

/-- `s(σH)`。 -/
def sσ (σ : G) : G := S.s (QuotientGroup.mk σ)

/-- ★★★ **`σ` 的 `H`-分量** `τ := (s(σH))⁻¹ · σ ∈ H`（NSW 的 `σ = sγ·τ`）。 -/
def hpart (σ : G) : H :=
  ⟨(sσ H S σ)⁻¹ * σ, by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk ((sσ H S σ)⁻¹ * σ) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, show QuotientGroup.mk (sσ H S σ)
      = QuotientGroup.mk σ from S.sec (QuotientGroup.mk σ), inv_mul_cancel]⟩

/-- ★★★ **NSW 的分解**：`s(σH) · hpart σ = σ`。 -/
theorem s_mul_hpart (σ : G) : sσ H S σ * (hpart H S σ : G) = σ := by
  show sσ H S σ * ((sσ H S σ)⁻¹ * σ) = σ
  rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- ★★★ **`tg` 的显式公式**（NSW：`y(σ) = y(sγ) + sγ·x(τ)`）。

`yx : G ⧸ H → A` 承担 `y(sγ)` 的自由选择；`x : G → A` 承担 `x(τ)`（只用到它在 `H` 上的值）。 -/
def tgLift (yx : G ⧸ H → A) (x : G → A) (σ : G) : A :=
  yx (QuotientGroup.mk σ) + sσ H S σ • x (hpart H S σ : G)

/-- `hpart` 在 `H` 的陪集内不变：`hpart (σ * τ) = hpart σ * τ`（`τ ∈ H`）。 -/
theorem hpart_mul (σ : G) (τ : H) :
    hpart H S (σ * (τ : G)) = hpart H S σ * τ := by
  apply Subtype.ext
  show (sσ H S (σ * (τ : G)))⁻¹ * (σ * (τ : G)) = ((sσ H S σ)⁻¹ * σ) * (τ : G)
  have hmk : (QuotientGroup.mk (σ * (τ : G)) : G ⧸ H) = QuotientGroup.mk σ := by
    rw [QuotientGroup.mk_mul H, show (QuotientGroup.mk (τ : G) : G ⧸ H) = 1 from
      (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2, mul_one]
  show (S.s (QuotientGroup.mk (σ * (τ : G))))⁻¹ * (σ * (τ : G)) = ((sσ H S σ)⁻¹ * σ) * (τ : G)
  rw [hmk]
  show ((sσ H S σ)⁻¹ * (σ * (τ : G))) = ((sσ H S σ)⁻¹ * σ) * (τ : G)
  rw [mul_assoc]

/-- ★★★ **NSW (i)**：`y|_H = x`（需 `yx 1 = 0`）。 -/
theorem tgLift_apply_hpart (yx : G ⧸ H → A) (x : G → A) (hx1 : yx 1 = 0)
    {τ : G} (hτ : τ ∈ H) : tgLift H S yx x τ = x τ := by
  have hmk : (QuotientGroup.mk τ : G ⧸ H) = (1 : G ⧸ H) := (QuotientGroup.eq_one_iff τ).mpr hτ
  have hsp : sσ H S τ = 1 := by
    show S.s (QuotientGroup.mk τ) = 1
    rw [hmk]; exact S.one
  have hhp : (hpart H S τ : G) = τ := by
    show (sσ H S τ)⁻¹ * τ = τ
    rw [hsp, inv_one, one_mul]
  show yx (QuotientGroup.mk τ) + sσ H S τ • x (hpart H S τ : G) = x τ
  rw [hmk, hx1, hhp, hsp, one_smul, zero_add]

/-- ★★★★ **NSW (ii)**：`y(στ) = y(σ) + σ·y(τ)`（`τ ∈ H`）。

只用「`x` 在 `H` 上是 1-上闭链」＋ `yx 1 = 0`，**不需** `y(sγ)` 的相容条件。 -/
theorem tgLift_mul_right (yx : G ⧸ H → A) (x : G → A) (hx1 : yx 1 = 0)
    (hx : ∀ τ₁ τ₂ : H, x ((τ₁ : G) * τ₂) = x (τ₁ : G) + (τ₁ : G) • x (τ₂ : G))
    (σ : G) (τ : H) :
    tgLift H S yx x (σ * (τ : G)) = tgLift H S yx x σ + σ • tgLift H S yx x τ := by
  have hmk : (QuotientGroup.mk (σ * (τ : G)) : G ⧸ H) = QuotientGroup.mk σ := by
    rw [QuotientGroup.mk_mul H, show (QuotientGroup.mk (τ : G) : G ⧸ H) = 1 from
      (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2, mul_one]
  have hcoc : x ((hpart H S σ : G) * (τ : G))
      = x (hpart H S σ : G) + (hpart H S σ : G) • x (τ : G) := hx (hpart H S σ) τ
  have hsp : sσ H S (σ * (τ : G)) = sσ H S σ := by
    show S.s (QuotientGroup.mk (σ * (τ : G))) = S.s (QuotientGroup.mk σ)
    rw [hmk]
  have hhp : (hpart H S (σ * (τ : G)) : G) = (hpart H S σ : G) * (τ : G) :=
    congrArg Subtype.val (hpart_mul H S σ τ)
  -- 目标展开
  show yx (QuotientGroup.mk (σ * (τ : G))) + sσ H S (σ * (τ : G)) • x (hpart H S (σ * (τ : G)) : G)
      = (yx (QuotientGroup.mk σ) + sσ H S σ • x (hpart H S σ : G))
        + σ • (yx (QuotientGroup.mk τ) + sσ H S τ • x (hpart H S τ : G))
  rw [hmk, hsp, hhp, hcoc]
  -- `tgLift τ` 的两项：`yx 1 = 0`、`s 1 = 1`、`hpart τ = τ`
  have hmkτ : (QuotientGroup.mk (τ : G) : G ⧸ H) = (1 : G ⧸ H) :=
    (QuotientGroup.eq_one_iff (τ : G)).mpr τ.2
  have hspτ : sσ H S (τ : G) = 1 := by
    show S.s (QuotientGroup.mk (τ : G)) = 1
    rw [hmkτ]; exact S.one
  have hhpτ : (hpart H S (τ : G) : G) = (τ : G) := by
    show (sσ H S (τ : G))⁻¹ * (τ : G) = (τ : G)
    rw [hspτ, inv_one, one_mul]
  rw [hmkτ, hx1, hspτ, hhpτ, one_smul, smul_add, zero_add]
  -- 两边同形：`yx + (a + b) = yx + a + σ•x τ`，其中 `b = sσ • (hpart σ • x τ)`
  rw [← mul_smul, s_mul_hpart, add_assoc]

end TgCore

end L20261018

#print axioms L20261018.s_mul_hpart
#print axioms L20261018.hpart_mul
#print axioms L20261018.tgLift_apply_hpart
#print axioms L20261018.tgLift_mul_right
