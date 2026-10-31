import Hyp187
import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# R1041（**补 `ValCompat` 的非空见证** · 第一步）：`ℚ_[p]` 上的 ℤ-值赋值 `v`

`ValCompat`（`Hyp187`）要的非空见证，取 `F := ℚ_[p]`（`p` 素、`p` 为一致化元）。
本轮先造出 **`v : ℚ_[p]ˣ →* Multiplicative ℤ`**（即 `Padic.valuation` 的限制）并机检：

| 声明 | 内容 |
|---|---|
| **`padicUnitV`** | `ℚ_[p]ˣ →* Multiplicative ℤ`，`a ↦ ofAdd (Padic.valuation a)` |
| **`padicUnitV_uniformizer`** | **`padicUnitV p = ofAdd 1`**（`Padic.valuation_p`） |

> **剩余两字段（下一轮）**：`0 ≤ toAdd (v a) → (a : ℚ_[p]) ∈ 𝒪[ℚ_[p]]` 与
> `(a ∈ 𝒪) → (元素 ∈ 𝔪 ↔ 0 < toAdd (v a))`，用
> `𝒪[R] = (ValuativeRel.valuation R).integer`（mathlib `Valued/ValuativeRel.lean:88` 的 scoped notation）
> ＋ `Valuation.mem_integer_iff (v) (r) : r ∈ v.integer ↔ v r ≤ 1` ＋ `Padic/ValuativeRel.lean:34` 的
> `instance : ValuativeRel ℚ_[p] := .ofValuation mulValuation` 的相容性引理。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel

namespace L20261018

section PadicValuation

/-- **`ℚ_[p]` 的单位上的 ℤ-值赋值**（一致化元 `p`）。 -/
noncomputable def padicUnitV (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (Padic.valuation (a : ℚ_[p]))
  map_one' := by
    rw [Units.val_one, Padic.valuation_one]
    rfl
  map_mul' a b := by
    rw [Units.val_mul, Padic.valuation_mul (Units.ne_zero a) (Units.ne_zero b)]
    rfl

/-- **一致化元的赋值是 `1`**：`padicUnitV p = ofAdd 1`。 -/
theorem padicUnitV_uniformizer (p : ℕ) [Fact p.Prime] :
    padicUnitV p (Units.mk0 ((p : ℕ) : ℚ_[p]) (by
      rw [Nat.cast_ne_zero]
      exact (Fact.out : p.Prime).ne_zero)) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [padicUnitV]
  show Multiplicative.ofAdd (Padic.valuation (((↑p : ℕ) : ℚ_[p]))) = Multiplicative.ofAdd (1 : ℤ)
  rw [Padic.valuation_p]

end PadicValuation

end L20261018

#print axioms L20261018.padicUnitV_uniformizer
