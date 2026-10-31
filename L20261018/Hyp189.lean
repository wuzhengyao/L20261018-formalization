import Hyp188
import Mathlib.NumberTheory.Padics.LocalField

/-!
# R1042（**非空见证第二步**）：`ValCompat` 在完备局部域上成立

R1041 造出了 `ℚ_[p]ˣ →* Multiplicative ℤ`。本轮更进一步：**对任意 `IsNonarchimedeanLocalField F`**，
取 `v := TauCeti.normalizedValuation F`，则 `ValCompat v` 的两字段都由 TauCeti 现成引理给出：

| 字段 | 依据 |
|---|---|
| `mem_integer` | **`mem_integer_iff_toAdd_normalizedValuation_nonneg (a) : ↑a ∈ 𝒪[F] ↔ 0 ≤ toAdd (v a)`**（TauCeti） |
| `mem_maximalIdeal` | `Valuation.mem_maximalIdeal_iff`（∈ `𝔪` ⟺ `v a < 1`）＋ 反序桥
`toAdd_normalizedValuation_le_iff_valuation_le`（`toAdd (v x) ≤ toAdd (v y) ↔ valuation y ≤ valuation x`） |

| 声明 | 内容 |
|---|---|
| **`valCompat_mem_integer_of_localField`** | 第一字段（完备局部域版） |
| **`valCompat_of_localField`** | **`ValCompat (normalizedValuation F)`** —— 若两字段都过，则 `ValCompat` 非空 ✓ |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel

namespace L20261018

section LocalFieldWitness

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F]

/-- **`ValCompat` 的第一字段**（完备局部域）：`0 ≤ toAdd (v a) ⟹ a ∈ 𝒪_F`。 -/
theorem valCompat_mem_integer_of_localField (a : Fˣ) :
    0 ≤ Multiplicative.toAdd (TauCeti.normalizedValuation F a) → (a : F) ∈ 𝒪[F] :=
  fun ha => (mem_integer_iff_toAdd_normalizedValuation_nonneg a).mpr ha

/-- **`ValCompat` 的第二字段**（完备局部域）：`元素 ∈ 𝔪 ↔ 0 < toAdd (v a)`。 -/
theorem valCompat_mem_maximalIdeal_of_localField (a : Fˣ) (h : (a : F) ∈ 𝒪[F]) :
    (⟨(a : F), h⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] ↔
      0 < Multiplicative.toAdd (TauCeti.normalizedValuation F a) := by
  -- 1. `∈ 𝔪 ⟺ valuation a < 1`（TauCeti 的用法：`mem_maximalIdeal` ＋ `mem_nonunits_iff` ＋ `not_isUnit_iff_valuation_lt_one`）
  have h𝔪 : ((⟨(a : F), h⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F])
      ↔ (ValuativeRel.valuation F (a : F)) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  -- 2. `0 < toAdd (v a) ⟺ valuation a < 1`（反序桥，`x = a`, `y = 1`）
  have hbridge := toAdd_normalizedValuation_le_iff_valuation_le (K := F) a (1 : Fˣ)
  have h1 : TauCeti.normalizedValuation F (1 : Fˣ) = 1 := map_one _
  have h2 : (ValuativeRel.valuation F ((1 : Fˣ) : F)) = 1 := by simp
  have h3 : Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 := toAdd_one
  rw [h1, h3, h2] at hbridge
  rw [h𝔪]
  constructor
  · intro hlt
    by_contra hv
    push_neg at hv
    exact absurd (hbridge.mp hv) (not_le.mpr hlt)
  · intro hv
    by_contra hlt
    push_neg at hlt
    have := hbridge.mpr hlt
    omega

/-- **`ValCompat` 在完备局部域上成立**（取 `v = normalizedValuation`）。 -/
theorem valCompat_of_localField :
    ValCompat (F := F) (TauCeti.normalizedValuation F) where
  mem_integer := valCompat_mem_integer_of_localField
  mem_maximalIdeal := valCompat_mem_maximalIdeal_of_localField

end LocalFieldWitness

/-- **具体的非空见证**：`ℚ_[p]` 上 `ValCompat` 成立（`IsNonarchimedeanLocalField ℚ_[p]` 是现成实例）。 -/
example (p : ℕ) [Fact p.Prime] :
    ValCompat (F := ℚ_[p]) (TauCeti.normalizedValuation ℚ_[p]) :=
  valCompat_of_localField

end L20261018

#print axioms L20261018.valCompat_mem_integer_of_localField
#print axioms L20261018.valCompat_mem_maximalIdeal_of_localField
#print axioms L20261018.valCompat_of_localField
