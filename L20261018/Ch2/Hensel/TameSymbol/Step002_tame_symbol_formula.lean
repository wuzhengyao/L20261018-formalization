import L20261018.Ch2.Hensel.Inertia.Step004_knr_galois_zhat

/-!
# R1295（S37 第 3 轮 · `prop:prelim-residue` (2)）：**一般驯符号公式** `eq:prelim-tame`

论文 `raw/L20261018.tex:1025–1031`（label `eq:prelim-tame`）的**完整公式**：

> 对 $a,b\in F^\times$，二次剩余由驯符号给出
> $$\partial_2\bigl((a)\cup(b)\bigr)=\left((-1)^{v(a)v(b)}\,\overline{a^{v(b)}b^{-v(a)}}\right)
>   \quad\text{于 }K^\times/K^{\times p}.$$

## 此前的覆盖状态（诚实口径）

`Hyp109`／`Hyp110` 的 `ResidueCupData` 只把该公式的**三处特化**当公理
（`tame_uu`／`tame_u_pi`／`tame_pi_u`），并注明「`eq:prelim-tame` 在证明里只以三处特化出现」。
**完整的公式本身从未机检** —— 本轮补上，并证明它与三处特化**等价**。

## 本轮结果

在 `ResidueCupData k V H2 VK`（`Hyp109`）的公理下（`k` 特征 `≠ 2`）：

| 声明 | 内容 |
|---|---|
| `val_eq_of_split` | 分解 `x = infl x₀ + m•π` 中 `m = val x`（赋值层唯一） |
| `unitPart_unique` | 分解的 `x₀` 唯一（用 `inj_infl`） |
| `res_cup_infl_pi`／`res_cup_pi_infl`／`res_cup_pi_pi` | 三处特化 ＋ `cup π π = 0` |
| **`infl_res_cup`** | ★★★★★ **`infl (res (cup a b)) = val b • a - val a • b`**（一般驯符号） |
| **`res_cup_eq_unitParts`** | ★★★★★ `res (cup a b) = val b • a₀ - val a • b₀`（用分解写出的经典形状） |
| `tame_uu_of_general`／`tame_u_pi_of_general`／`tame_pi_u_of_general` | **一般公式 ⟹ 三处特化**（回归对照：新公理不比旧的三条更强） |

## 公式与其翻译

论文右侧 `\overline{a^{v(b)}b^{-v(a)}}` 的 `K^\times/K^{\times p}` 类，在 Kummer 商里就是
`val b • (a) - val a • (b)`（`(a^{m}) = m • (a)`）；而 `\overline{\,}`（把单位降到剩余域）恰是
`res` 的取值。故论文公式 = `res (cup a b) = val b • a₀ - val a • b₀`，
其中 `a₀ = infl⁻¹(a - val a • π)` 即 `\overline{a\cdot\pi^{-v(a)}}` 的类。

`(-1)^{v(a)v(b)}` 这一因子在 Kummer 商里**是零类**：`-1 = (-1)^{p}`（`p` 奇数）是 `p` 次幂，
正如论文 `:1051` 所说「因为 $p$ 为奇数，$-1=(-1)^p$ 在右侧的 Kummer 商中为零类」。
故本文件的一般公式**不含**该因子，与论文一致。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

variable {k : Type*} [Field k] [NeZero (2 : k)]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {VK : Type*} [AddCommGroup VK] [Module k VK]

namespace ResidueCupData

variable (D : ResidueCupData k V H2 VK)

/-! ### 赋值层与单位部分的唯一性 -/

/-- 分解 `x = infl x₀ + m • π` 中的 `m` 恰是 `val x`。 -/
theorem val_eq_of_split {x : V} {x₀ : VK} {m : k} (h : x = D.infl x₀ + m • D.pi) :
    D.val x = m := by
  rw [h, map_add, map_smul, D.val_infl, D.val_pi, zero_add, smul_eq_mul, mul_one]

/-- 两个分解的赋值层相等。 -/
theorem val_eq_of_split' {x : V} {x₀ y₀ : VK} {m n : k}
    (h : x = D.infl x₀ + m • D.pi) (h' : x = D.infl y₀ + n • D.pi) : m = n := by
  rw [← val_eq_of_split D h, ← val_eq_of_split D h']

/-- 分解的单位部分在 `infl` 后唯一。 -/
theorem infl_eq_of_split' {x : V} {x₀ y₀ : VK} {m n : k}
    (h : x = D.infl x₀ + m • D.pi) (h' : x = D.infl y₀ + n • D.pi) :
    D.infl x₀ = D.infl y₀ := by
  have hmn : m = n := val_eq_of_split' D h h'
  have hxy : D.infl x₀ + m • D.pi = D.infl y₀ + n • D.pi := h.symm.trans h'
  rw [hmn] at hxy
  exact add_right_cancel hxy

/-! ### 三处特化的推论形状 -/

/-- `res (cup (infl y) π) = y`（由 `tame_u_pi`）。 -/
theorem res_cup_infl_pi (y : VK) : D.res (D.cup (D.infl y) D.pi) = y :=
  D.tame_u_pi y

/-- `res (cup π (infl z)) = -z`（由 `tame_pi_u` 与 `val π = 1`）。 -/
theorem res_cup_pi_infl (z : VK) : D.res (D.cup D.pi (D.infl z)) = -z :=
  D.tame_pi_u D.pi D.val_pi z

/-- `res (cup π π) = 0`（由交错性）。 -/
theorem res_cup_pi_pi : D.res (D.cup D.pi D.pi) = 0 := by
  rw [D.alt D.pi, map_zero]

/-! ### 一般驯符号公式 -/

/-- ★★★★★ **一般驯符号公式**（`eq:prelim-tame` 的 `infl` 形状）：

`infl (res (cup a b)) = val b • a - val a • b`。

证明：把 `a`、`b` 各按 `x = infl x₀ + val x • π` 分解，双线性展开 `cup`，
四项的 `res` 分别是 `0`、`val b • a₀`、`val a • (−b₀)`、`0`；再 `infl`。 -/
-- @source file=raw/L20261018.tex locator=label:eq:prelim-tame quote="\partial_2\bigl((a)\cup(b)\bigr) =\left((-1)^{v(a)v(b)} \overline{a^{v(b)}b^{-v(a)}}\right)"
theorem infl_res_cup (a b : V) :
    D.infl (D.res (D.cup a b)) = D.val b • a - D.val a • b := by
  obtain ⟨a₀, ma, ha⟩ := D.split a
  obtain ⟨b₀, mb, hb⟩ := D.split b
  have hma : D.val a = ma := val_eq_of_split D ha
  have hmb : D.val b = mb := val_eq_of_split D hb
  subst ha
  subst hb
  rw [hma, hmb]
  simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, map_sub, map_neg, smul_add, smul_sub, smul_neg, smul_smul,
    D.tame_uu a₀ b₀, res_cup_infl_pi D a₀, res_cup_pi_infl D b₀, res_cup_pi_pi D,
    smul_zero, add_zero, zero_add, sub_eq_add_neg, neg_zero]
  module

/-- ★★★★★ **一般驯符号公式（经典形状）**：取分解 `a = infl a₀ + val a • π`、
`b = infl b₀ + val b • π`，则 `res (cup a b) = val b • a₀ - val a • b₀`。 -/
theorem res_cup_eq_unitParts {a b : V} {a₀ b₀ : VK} {ma mb : k}
    (ha : a = D.infl a₀ + ma • D.pi) (hb : b = D.infl b₀ + mb • D.pi) :
    D.res (D.cup a b) = D.val b • a₀ - D.val a • b₀ := by
  have hma : D.val a = ma := val_eq_of_split D ha
  have hmb : D.val b = mb := val_eq_of_split D hb
  refine D.inj_infl ?_
  rw [infl_res_cup D a b, hma, hmb, ha, hb]
  simp only [map_add, map_sub, map_smul, map_neg, smul_sub, smul_add, smul_neg, smul_smul,
    sub_eq_add_neg, neg_zero]
  module

/-! ### 回归对照：一般公式 ⟹ 三处特化（新公理不比旧三条更强） -/

/-- 一般公式 ⟹ `tame_uu`（单位之间的杯积剩余为 `0`）。 -/
theorem tame_uu_of_general (a b : V) (ha : D.val a = 0) (hb : D.val b = 0) :
    D.res (D.cup a b) = 0 := by
  have h := infl_res_cup D a b
  rw [ha, hb] at h
  simp only [zero_smul, sub_zero] at h
  refine D.inj_infl ?_
  rw [h, map_zero]

/-- 一般公式 ⟹ `tame_u_pi`（`res (cup (infl y) π) = y`）。 -/
theorem tame_u_pi_of_general (y : VK) : D.res (D.cup (D.infl y) D.pi) = y := by
  have h := infl_res_cup D (D.infl y) D.pi
  rw [D.val_infl, D.val_pi] at h
  simp only [zero_smul, one_smul, sub_zero] at h
  refine D.inj_infl ?_
  rw [h]

/-- 一般公式 ⟹ `tame_pi_u`（`val κ = 1` 时 `res (cup κ (infl z)) = -z`）。 -/
theorem tame_pi_u_of_general (κ : V) (hκ : D.val κ = 1) (z : VK) :
    D.res (D.cup κ (D.infl z)) = -z := by
  have h := infl_res_cup D κ (D.infl z)
  rw [D.val_infl, hκ] at h
  simp only [zero_smul, one_smul, zero_sub] at h
  refine D.inj_infl ?_
  rw [map_neg]
  exact h

end ResidueCupData

end L20261018

#print axioms L20261018.ResidueCupData.val_eq_of_split
#print axioms L20261018.ResidueCupData.res_cup_pi_pi
#print axioms L20261018.ResidueCupData.infl_res_cup
#print axioms L20261018.ResidueCupData.res_cup_eq_unitParts
#print axioms L20261018.ResidueCupData.tame_u_pi_of_general
#print axioms L20261018.ResidueCupData.tame_pi_u_of_general
#print axioms L20261018.ResidueCupData.tame_uu_of_general
