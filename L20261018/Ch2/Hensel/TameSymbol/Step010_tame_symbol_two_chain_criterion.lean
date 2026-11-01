import L20261018.Ch2.Hensel.TameSymbol.Step009_tame_symbol_factors_descent

/-!
# S59 R5：**A1 的判据更正** —— 正确形态是「二项链式判据」，不是「点式判据」

## 更正（本轮最重要的产出）

`G2-PLAN.md` §2 原把 A1 写成
`TameSymbolFactors ⟺ ∀ a b a' b', ∪ab = ∪a'b' → tame ab = tame a'b'`（**点式**）。
本轮判读：**点式判据严格弱于 `TameSymbolFactors`**，故不能作为等价刻画。
理由（一句话）：构造 `res` 需要 `span{∪ a b}` 上的良定义，而 `∪ab + ∪a'b'` **一般不是**单个 `∪`-值
（抽象层无此保证），故「单元组一致」推不出「二元组一致」。

**正确判据**（本件 `ChainCond`）：二项链式
`∀ a b a' b', ∪ab + ∪a'b' = 0 → tame ab + tame a'b' = 0`。
它 **⟸** `TameSymbolFactors`（本件机检），并且 **⟹** 点式判据（本件机检，用 `∪` 与 `tame` 的斜对称）。
⟹ `TameSymbolFactors` 的等价刻画必须走**有限和**（`Hyp683` 的求和形态）／二项链式，**不是**点式。

## 机检件

| 声明 | 内容 |
|---|---|
| **`tameChainCond`** | 谓词：二项链式判据 |
| **`tameChainCond_of_tameSymbolFactors`** | ★ `TameSymbolFactors ⟹ 链式判据` |
| **`tamePointwise_of_tameChainCond`** | ★★ **链式 ⟹ 点式**（**不需要 `hskew`**：只用 `map_neg` ＋ `tame` 第二变元线性） |

## 诚实边界

* **不**证 `TameSymbolFactors`；本件只**更正判据**并机检两条蕴含。
* 链式 ⟹ `TameSymbolFactors`（构造 `res`）**仍未做**：需 `span` 上的良定义（`Hyp683` 求和形态给出）
  ＋ `Submodule.exists_isCompl` 扩到 `H2`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ChainCond

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- **二项链式判据**（A1 的正确形态）。 -/
def tameChainCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) : Prop :=
  ∀ a b a' b' : V, cup a b + cup a' b' = 0 →
    tameExpr val a b + tameExpr val a' b' = 0

theorem tameChainCond_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : TameSymbolFactors cup val) : tameChainCond cup val := by
  obtain ⟨res, hres⟩ := h
  intro a b a' b' hsum
  have h1 : res (cup a b + cup a' b') = tameExpr val a b + tameExpr val a' b' := by
    rw [map_add, hres, hres]
  rw [hsum, map_zero] at h1
  exact h1.symm

/-- ★★ **链式 ⟹ 点式**：把 `∪ab = ∪a'b'` 抬成 `∪ab + ∪a'(-b') = 0`（只用 `∪` 在第二变元的线性，
**不需要斜对称**）。 -/
theorem tamePointwise_of_tameChainCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : tameChainCond cup val)
    {a b a' b' : V} (hab : cup a b = cup a' b') :
    tameExpr val a b = tameExpr val a' b' := by
  have hzero : cup a b + cup a' (-b') = 0 := by
    rw [map_neg, ← hab, add_neg_cancel]
  have h2 : tameExpr val a b + tameExpr val a' (-b') = 0 := h a b a' (-b') hzero
  have hneg : tameExpr val a' (-b') = -tameExpr val a' b' := by
    rw [← neg_one_smul k b', tameExpr_smul_right, neg_one_smul]
  rw [hneg, add_neg_eq_zero] at h2
  exact h2

end ChainCond

end L20261018

/-! ## 机检读数 -/

#print axioms L20261018.tameChainCond_of_tameSymbolFactors
#print axioms L20261018.tamePointwise_of_tameChainCond
