import L20261018.Ch2.Hensel.TameSymbol.Step006_tame_symbol_explicit

/-!
# S59 R3：**驯符号的点式双线性 ＋ 零点判据 ＋ 必要条件** —— `(R2)` 的 Steinberg 路线的代数层

## 动机

`Hyp680` 把 `(R2)` 压成 `TameSymbolFactors cup val`（`∃ res, res ∘ ∪ = tame`），
其内容 ＝ `ker ∪ ⊆ ker tame`；`Hyp681` 给了 Steinberg 情形需要的两条算术输入
`(K1) κ(1+m)=0`／`(K2) κ(−1)=0`。本件补**代数层**：把「证 `tame a b = 0`」化归成
**一条在 `V` 里的等式** `v̄(b)·a = v̄(a)·b`，并给出
`TameSymbolFactors` 的**必要条件**（可用于反证，也可作为攻它的中间目标）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`tameExpr_eq_zero_iff`** | ★★ `tame a b = 0 ⟺ v̄(b)·a = v̄(a)·b`（**零点判据**） |
| `tameExpr_add_left`／`_add_right`／`_smul_left`／`_smul_right` | 点式双线性（`tame` 是双线性型，无需 `LinearMap` 打包） |
| **`tameExpr_collinear`** | 共线对 `tame a (c·a) = 0` |
| **`tameExpr_eq_zero_of_tameSymbolFactors`** | ★ `TameSymbolFactors ⟹ (∪ a b = 0 ⟹ tame a b = 0)`（**必要条件／反证入口**） |

## 用法（下一轮）

Steinberg `tame(a, 1−a) = 0` 由 `tameExpr_eq_zero_iff` 变成
`v̄(1−a)·κ(a) = v̄(a)·κ(1−a)` —— 四情形（`PROMPT-S60` §①-2）里每一条都是这个等式；
`(K1)`／`(K2)`（`Hyp681`）正是消去 `κ(1−a)` 的两把钥匙。

## 诚实边界

* **不**证 `TameSymbolFactors`（`(R2)` 仍 `∅-open`）。
* `tameExpr_eq_zero_of_tameSymbolFactors` 是**单向**（必要条件）；其逆需 `ker ∪` 的**生成性**
  （Steinberg／Matsumoto 层），是全战役唯一剩下的硬核。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section TameCalc
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

-- @source file=raw/L20261018.tex locator=label:eq:prelim-tame quote="\partial_2\bigl((a)\cup(b)\bigr)"
theorem tameExpr_eq_zero_iff (val : V →ₗ[k] k) (a b : V) :
    tameExpr val a b = 0 ↔ val b • a = val a • b := by
  constructor
  · intro h
    have h' : val b • a - val a • b = 0 := by rw [← tameExpr_coe, h, Submodule.coe_zero]
    exact sub_eq_zero.mp h'
  · intro h
    apply Subtype.ext
    rw [tameExpr_coe, h, sub_self, Submodule.coe_zero]

theorem tameExpr_add_right (val : V →ₗ[k] k) (a b b' : V) :
    tameExpr val a (b + b') = tameExpr val a b + tameExpr val a b' := by
  apply Subtype.ext
  simp only [tameExpr_coe, Submodule.coe_add, map_add, add_smul, smul_add]
  module

theorem tameExpr_add_left (val : V →ₗ[k] k) (a a' b : V) :
    tameExpr val (a + a') b = tameExpr val a b + tameExpr val a' b := by
  apply Subtype.ext
  simp only [tameExpr_coe, Submodule.coe_add, map_add, add_smul, smul_add]
  module

theorem tameExpr_smul_right (val : V →ₗ[k] k) (a b : V) (c : k) :
    tameExpr val a (c • b) = c • tameExpr val a b := by
  apply Subtype.ext
  simp only [tameExpr_coe, Submodule.coe_smul, map_smul, smul_sub, smul_smul]
  module

theorem tameExpr_smul_left (val : V →ₗ[k] k) (a b : V) (c : k) :
    tameExpr val (c • a) b = c • tameExpr val a b := by
  apply Subtype.ext
  simp only [tameExpr_coe, Submodule.coe_smul, map_smul, smul_sub, smul_smul]
  module

theorem tameExpr_collinear (val : V →ₗ[k] k) (a : V) (c : k) :
    tameExpr val a (c • a) = 0 := by
  rw [tameExpr_eq_zero_iff, map_smul]
  module

theorem tameExpr_eq_zero_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : TameSymbolFactors cup val) {a b : V} (hab : cup a b = 0) :
    tameExpr val a b = 0 := by
  obtain ⟨res, hres⟩ := h
  have h1 := hres a b
  rw [hab, map_zero] at h1
  exact h1.symm

end TameCalc
end L20261018

#print axioms L20261018.tameExpr_eq_zero_iff
#print axioms L20261018.tameExpr_add_right
#print axioms L20261018.tameExpr_add_left
#print axioms L20261018.tameExpr_smul_right
#print axioms L20261018.tameExpr_smul_left
#print axioms L20261018.tameExpr_collinear
#print axioms L20261018.tameExpr_eq_zero_of_tameSymbolFactors
