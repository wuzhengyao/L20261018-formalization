import L20261018.Hyp325

/-!
# R1232（S34 第 4 轮）：**驯符号一般式**（`eq:prelim-tame` 的锁定版本）

论文 `eq:prelim-tame` 给的是
`∂₂((a)∪(b)) = ((−1)^{v(a)v(b)}\,\overline{a^{v(b)}b^{-v(a)}})`。
本轮把 `HenselResidueData` 的**两条规范 ＋ 斜对称性**能推出的**一般式**机检出来：

```
x = inf a + (v x)·π ,  y = inf b + (v y)·π
⟹ ∂(cup x y) = (v y) • a − (v x) • b
```

（推导：双线性展开四项 `cup(inf a)(inf b) = 0`（`tame_uu`）、`(v y)•cup(inf a)π = (v y)•a`
（`tame_u_pi`）、`(v x)•cup π (inf b) = −(v x)•b`（`tame_pi_u`，由 `Hyp325` 的冗余性亦可导）、
以及 `(v x)(v y)•cup π π = 0`（**斜对称 ＋ `p` 奇** ⟹ `cup π π = 0`）。）

⚠ **与论文印刷式的符号差（`⚠-contentious`）**：上式即「`\overline{u_a^{v y}u_b^{−v x}}` 的类」，
**无** `(−1)^{v x·v y}` 因子；论文印刷式有。两者的差别只在 `v x·v y` 为奇的混合情形，
且**不影响第 4 章**（其证明只用三处特化，三处与上式逐点一致：`v y = 0` 给 `(ū_a)`、
`v x = 0` 给 `−(ū_b)`、两者皆 0 给 `0`）。符号来源是「把一致化元置于杯积右端」的规范选择，
需人工裁决 —— 见 `CH4-COVERAGE-AUDIT.md` §R1232。

## 本轮

| 声明 | 内容 |
|---|---|
| `cup_pi_pi_eq_zero` | ★ `cup π π = 0`（斜对称 ＋ `2 ≠ 0`） |
| **`res_cup_eq`** | ★★★★★ **一般驯符号式**：`∂(cup x y) = (v y) • a − (v x) • b` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti

namespace L20261018

section TameGeneral

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {H2 : Type*} [AddCommGroup H2] [Module k H2]
  {VK : Type*} [AddCommGroup VK] [Module k VK]
  {cup : V →ₗ[k] V →ₗ[k] H2} [NeZero (2 : k)]

/-- ★ **`cup π π = 0`**：斜对称给 `cup π π = −cup π π`，`2 ≠ 0` 消去。 -/
theorem cup_pi_pi_eq_zero (D : HenselResidueData k V H2 VK cup)
    (hskew : ∀ x y : V, cup x y = - cup y x) :
    cup D.pi D.pi = 0 := by
  have h : cup D.pi D.pi = - cup D.pi D.pi := hskew D.pi D.pi
  have hz : cup D.pi D.pi + cup D.pi D.pi = 0 := by
    nth_rewrite 1 [h]
    abel
  have h2 : (2 : k) • (cup D.pi D.pi) = 0 := by
    rw [two_smul]
    exact hz
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (NeZero.ne (2 : k))
  · exact h0

/-- ★★★★★ **一般驯符号式**（本战役编码下的 `eq:prelim-tame`）：

若 `x = inf a + (v x)·π`、`y = inf b + (v y)·π`，则
`∂(cup x y) = (v y) • a − (v x) • b`。

对 Kummer 类 `x = (A)`、`y = (B)`（`A = u_a π^n`、`B = u_b π^m`）即
`∂((A)∪(B)) = m•(ū_a) − n•(ū_b)`，也就是类 `\overline{u_a^m u_b^{−n}}`。 -/
-- @source file=raw/L20261018.tex locator=label:eq:prelim-tame quote="\partial_2\bigl((a)\cup(b)\bigr)"
theorem res_cup_eq (D : HenselResidueData k V H2 VK cup)
    (hskew : ∀ x y : V, cup x y = - cup y x)
    {x y : V} {a b : VK}
    (ha : D.infl a = x - D.val x • D.pi) (hb : D.infl b = y - D.val y • D.pi) :
    D.res (cup x y) = D.val y • a - D.val x • b := by
  set n : k := D.val x with hn
  set m : k := D.val y with hm
  have ha' : D.infl a = x - n • D.pi := ha
  have hb' : D.infl b = y - m • D.pi := hb
  have hx : x = D.infl a + n • D.pi := by rw [ha']; abel
  have hy : y = D.infl b + m • D.pi := by rw [hb']; abel
  have hpipi : cup D.pi D.pi = 0 := cup_pi_pi_eq_zero D hskew
  rw [hx, hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add,
    smul_smul]
  rw [D.tame_uu a b, D.tame_u_pi a, D.tame_pi_u_of_skew hskew D.val_pi b, hpipi]
  simp only [map_zero, smul_zero, add_zero, smul_neg]
  module

end TameGeneral

end L20261018

#print axioms L20261018.cup_pi_pi_eq_zero
#print axioms L20261018.res_cup_eq
