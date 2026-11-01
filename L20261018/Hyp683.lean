import Hyp682

/-!
# S59 R4：**A1 的易向 ＋ 求和必要条件** —— `TameSymbolFactors` 的「下降」已压成一条求和判据

## 定位（`G2-PLAN.md` §2 的 A1 格）

A1 要证 `TameSymbolFactors cup val ⟺ ∀ a b a' b', ∪ a b = ∪ a' b' → tame a b = tame a' b'`。
本件交**易向**与**求和版必要条件**；难向（由求和判据**构造** `res`）留下的**恰好**是两步构造：
① `span{∪ a b}` 上的良定义（由本件的求和判据给出）＋ ② 由 `Submodule.exists_isCompl` 把
`span` 上的线性映射扩到 `H2`。已 `#check` 确认 `Submodule.exists_isCompl`／`Submodule.liftQ`／
`Submodule.span_induction` 在库（`Submodule.exists_projection`／`*_ker_le_ker_iff` **不在**）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`tameExpr_congr_of_tameSymbolFactors`** | ★ A1 易向：`TameSymbolFactors ⟹ ∪ 相等则 tame 相等` |
| **`tameExpr_sum_eq_zero_of_tameSymbolFactors`** | ★★ **求和必要条件**（`Fin n` 版）：`∑ ∪ = 0 ⟹ ∑ tame = 0` |
| `tameExpr_zero_left`／`tameExpr_zero_right` | `@[simp]`：零元的驯符号为零（求和归纳用） |

## 为什么求和版是**正确**的目标形态

求和判据里**标量可以吸进 `a`**：`c • ∪ a b = ∪ (c • a) b`（`∪` 双线性）。
⟹ `∑ᵢ cᵢ • ∪ (aᵢ) (bᵢ) = ∑ᵢ ∪ (cᵢ • aᵢ) (bᵢ)`，故「`span{∪ a b}` 上良定义」**就是**求和判据，
不需要另立条件。这正是难向要证的**唯一**内容。

## 诚实边界

**不**证 `TameSymbolFactors`（`(R2)` 仍 `∅-open`）；本件是 A1 的**一半**（易向 ＋ 目标形态锁定）。
难向（`res` 的构造）未做。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section TameDescent

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- ★ **A1 易向**：`TameSymbolFactors ⟹ tame` 只依赖 `∪ a b`。 -/
theorem tameExpr_congr_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : TameSymbolFactors cup val) {a b a' b' : V} (hab : cup a b = cup a' b') :
    tameExpr val a b = tameExpr val a' b' := by
  obtain ⟨res, hres⟩ := h
  rw [← hres a b, ← hres a' b', hab]

/-- ★★ **求和必要条件**：这是 A1 难向要证的**目标形态**（`span{∪ a b}` 上的良定义）。 -/
theorem tameExpr_sum_eq_zero_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : TameSymbolFactors cup val) (n : ℕ) (as bs : Fin n → V)
    (hsum : ∑ i, cup (as i) (bs i) = 0) :
    ∑ i, tameExpr val (as i) (bs i) = 0 := by
  obtain ⟨res, hres⟩ := h
  have h1 : res (∑ i, cup (as i) (bs i)) = ∑ i, tameExpr val (as i) (bs i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hres (as i) (bs i)
  rw [hsum, map_zero] at h1
  exact h1.symm

@[simp] theorem tameExpr_zero_right (val : V →ₗ[k] k) (a : V) : tameExpr val a 0 = 0 := by
  rw [tameExpr_eq_zero_iff]
  simp

@[simp] theorem tameExpr_zero_left (val : V →ₗ[k] k) (b : V) : tameExpr val 0 b = 0 := by
  rw [tameExpr_eq_zero_iff]
  simp

end TameDescent

end L20261018

/-! ## 机检读数 -/

#print axioms L20261018.tameExpr_congr_of_tameSymbolFactors
#print axioms L20261018.tameExpr_sum_eq_zero_of_tameSymbolFactors
#print axioms L20261018.tameExpr_zero_right
#print axioms L20261018.tameExpr_zero_left
