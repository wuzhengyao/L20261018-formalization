import L20261018.Hyp332

/-!
# R1239（S34 第 11 轮）：**两套赋值桥** —— `ValCompat (normalizedValuation)` at `ℚ_[7]`

本战役的 `vCompatHom`（由 `IsDiscreteValuationRing.addVal` 构造，`Hyp304`–`Hyp307`）与
TauCeti 的 `normalizedValuation`（局部域库的整套工具 `unitFiltration`／`localSymbol` 都用它）
是**两套赋值**。本轮把 TauCeti 那套接到本战役的 `ValCompat` 接口上，用的全是库内桥：

* `TauCeti.toAdd_normalizedValuation_le_iff_valuation_le`
  （`toAdd (v x) ≤ toAdd (v y) ↔ valuation y ≤ valuation x`）；
* `Valuation.mem_integer_iff`（`a ∈ v.integer ↔ v a ≤ 1`）；
* `Valuation.Integer.not_isUnit_iff_valuation_lt_one`（`¬ IsUnit x ↔ v x < 1`）。

## 本轮

| 声明 | 内容 |
|---|---|
| **`valCompat_normalizedValuation_Q7`** | ★★★★ `ValCompat (F := ℚ_[7]) (normalizedValuation ℚ_[7])` |
| **`normalizedValuation_seven_Q7`** | ★★ `normalizedValuation ℚ_[7] 7 = ofAdd 1`（`7` 是一致化元） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Q7Valuation

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- ★★★★ **TauCeti 的 `normalizedValuation` 满足本战役的 `ValCompat`**（`F = ℚ_[7]`）。 -/
theorem valCompat_normalizedValuation_Q7 :
    ValCompat (F := ℚ_[7]) (TauCeti.normalizedValuation ℚ_[7]) where
  mem_integer a ha := by
    have h1 : Multiplicative.toAdd ((TauCeti.normalizedValuation ℚ_[7]) 1)
        ≤ Multiplicative.toAdd ((TauCeti.normalizedValuation ℚ_[7]) a) := by
      simpa using ha
    have h2 := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le (K := ℚ_[7]) 1 a).mp h1
    rw [Valuation.mem_integer_iff]
    simpa using h2
  mem_maximalIdeal a ha := by
    have hle := (TauCeti.toAdd_normalizedValuation_le_iff_valuation_le (K := ℚ_[7]) a 1)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    have hzero : Multiplicative.toAdd ((TauCeti.normalizedValuation ℚ_[7]) 1) = 0 := by simp
    rw [hzero] at hle
    constructor
    · intro hlt
      by_contra hcon
      have hle' : Multiplicative.toAdd ((TauCeti.normalizedValuation ℚ_[7]) a) ≤ 0 :=
        not_lt.mp hcon
      have h2 := hle.mp hle'
      have h2' : (1 : ValueGroupWithZero ℚ_[7]) ≤ (ValuativeRel.valuation ℚ_[7]) ↑a := by
        simpa using h2
      exact absurd h2' (not_le.mpr hlt)
    · intro hpos
      by_contra hcon
      have h2 : (1 : ValueGroupWithZero ℚ_[7]) ≤ (ValuativeRel.valuation ℚ_[7]) ↑a :=
        not_lt.mp hcon
      have h2' : (ValuativeRel.valuation ℚ_[7]) (1 : ℚ_[7]) ≤
          (ValuativeRel.valuation ℚ_[7]) ↑a := by
        simpa using h2
      exact absurd (hle.mpr h2') (not_le.mpr hpos)

/-- ★★ **`7` 是 `ℚ_[7]` 的一致化元**：`normalizedValuation ℚ_[7] 7 = ofAdd 1`。 -/
theorem normalizedValuation_seven_Q7 :
    TauCeti.normalizedValuation ℚ_[7] (Units.mk0 (7 : ℚ_[7]) (by norm_num))
      = Multiplicative.ofAdd (1 : ℤ) :=
  (TauCeti.isUniformizer_def (K := ℚ_[7])
    (Units.mk0 (7 : ℚ_[7]) (by norm_num))).mp
    (TauCeti.Padic.isUniformizer_natCast_self 7)

end Q7Valuation

end L20261018

#print axioms L20261018.valCompat_normalizedValuation_Q7
#print axioms L20261018.normalizedValuation_seven_Q7
