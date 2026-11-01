import L20261018.Witness.Step025_f7t_hne_hval

/-!
# R1267（S36 C 项 末步之一）：主单位（`1 + 𝔪`）在 `𝔽₇((t))` 中是立方

`HANDOFF` §S36 收尾计划的第 2(a) 件：`Finite (Fˣ/(Fˣ)³)` 的**核心数学**。
对 `y ∈ 𝔪[F]` 解 `(1+z)³ = 1+y` —— 标准「Hensel 于 `1`」。本战役**不必**用 TauCeti 的
`unitFiltration`（那条走 `[IsNonarchimedeanLocalField]` ＋ 紧性迭代），因为
`HenselianRing ↥𝒪[F]` 已由 `Hyp352` 机检，一次 Hensel 即得。

| 声明 | 内容 |
|---|---|
| `mF` | 局部记号：`𝔪[𝔽₇((t))]` |
| `henselPoly`／`monic_henselPoly` | `Y³ + 3Y² + 3Y − y`（首一） |
| `derivative_henselPoly` | 其在 `0` 处的导数为 `3` |
| **`one_add_mem_cubes`** | ★★★★★ `y ∈ 𝔪 ⟹ ∃ u : Fˣ, u³ = 1+y` |

**为什么 `3` 可逆就够**：`f(Y) = Y³ + 3Y² + 3Y − y` 的导数在 `0` 处取值 `3`，
而 `3` 是 `↥𝒪[F]` 的单位（`Hyp353.three_isUnit_O`）⟹ 其在剩余域中的像是单位 ⟹ Hensel 适用。
`char F = 7 ≠ 3` 正体现在这里（这也是论文假设 `char K ≠ p` 的用处）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LaurentSeries ValuativeRel IsLocalRing Polynomial
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 局部记号：`↥𝒪[𝔽₇((t))]` 的极大理想。 -/
noncomputable abbrev mF : Ideal ↥𝒪[LaurentSeries (ZMod 7)] := IsLocalRing.maximalIdeal _

/-- 本文件的 Hensel 多项式 `Y³ + 3Y² + 3Y − y`（`= (Y+1)³ − (1+y)`）。 -/
noncomputable def henselPoly (y : ↥𝒪[LaurentSeries (ZMod 7)]) :
    Polynomial ↥𝒪[LaurentSeries (ZMod 7)] :=
  X ^ 3 + (C (3 : ↥𝒪[LaurentSeries (ZMod 7)]) * X ^ 2 + C 3 * X - C y)

/-- `henselPoly y` 首一。 -/
theorem monic_henselPoly (y : ↥𝒪[LaurentSeries (ZMod 7)]) : (henselPoly y).Monic :=
  monic_X_pow_add (n := 3) (by
    show ((C (3 : ↥𝒪[LaurentSeries (ZMod 7)]) * X ^ 2 + C 3 * X - C y)).degree < (3 : WithBot ℕ)
    compute_degree!)

/-- `henselPoly y` 在 `0` 处的取值为 `-y`。 -/
theorem eval_zero_henselPoly (y : ↥𝒪[LaurentSeries (ZMod 7)]) :
    (henselPoly y).eval 0 = -y := by
  simp [henselPoly]

/-- `henselPoly y` 在 `0` 处的导数为 `3`。 -/
theorem derivative_henselPoly (y : ↥𝒪[LaurentSeries (ZMod 7)]) :
    (henselPoly y).derivative.eval 0 = 3 := by
  simp [henselPoly]

/-- ★★★★★ **`1 + y` 在 `Fˣ` 中是立方**（`y ∈ 𝔪[F]`）。

Hensel 于 `henselPoly y`：`f(0) = -y ∈ 𝔪`、`f'(0) = 3` 可逆 ⟹ 存在 `z ∈ 𝔪` 使 `f(z) = 0`，
即 `z³ + 3z² + 3z = y`，亦即 `(1+z)³ = 1+y`；`z ∈ 𝔪` ⟹ `1+z` 是 `↥𝒪[F]` 的单位。 -/
theorem one_add_mem_cubes {y : ↥𝒪[LaurentSeries (ZMod 7)]} (hy : y ∈ mF) :
    ∃ u : (LaurentSeries (ZMod 7))ˣ,
      (u : LaurentSeries (ZMod 7)) ^ 3 = 1 + (y : LaurentSeries (ZMod 7)) := by
  haveI hhens : HenselianRing ↥𝒪[LaurentSeries (ZMod 7)] mF := henselianRing_O
  have hunit3 : IsUnit (Ideal.Quotient.mk mF ((henselPoly y).derivative.eval 0)) := by
    rw [derivative_henselPoly]
    exact IsUnit.map (Ideal.Quotient.mk mF) three_isUnit_O
  obtain ⟨z, hzroot, hzmem⟩ :=
    HenselianRing.is_henselian (I := mF) (henselPoly y) (monic_henselPoly y) 0
      (by rw [eval_zero_henselPoly]; exact neg_mem hy) hunit3
  rw [sub_zero] at hzmem
  -- `(1+z)³ = 1+y`
  have hz3 : (1 + z) ^ 3 = 1 + y := by
    have h := hzroot
    rw [IsRoot] at h
    have h' : z ^ 3 + ((3 : ↥𝒪[LaurentSeries (ZMod 7)]) * z ^ 2 + 3 * z - y) = 0 := by
      simpa [henselPoly] using h
    rw [show (1 + z) ^ 3
      = 1 + y + (z ^ 3 + ((3 : ↥𝒪[LaurentSeries (ZMod 7)]) * z ^ 2 + 3 * z - y)) by ring, h',
      add_zero]
  -- `1+z` 是 `↥𝒪[F]` 的单位
  have h1z_unit : IsUnit (1 + z) :=
    IsLocalRing.notMem_maximalIdeal.mp (by
      intro hmem
      have h1 : (1 : ↥𝒪[LaurentSeries (ZMod 7)]) ∈ mF := by
        simpa using Submodule.sub_mem mF hmem hzmem
      exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[LaurentSeries (ZMod 7)]).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one))
  obtain ⟨w, hw⟩ := h1z_unit
  refine ⟨Units.map (Subring.subtype 𝒪[LaurentSeries (ZMod 7)]) w, ?_⟩
  have hcoe : ((Units.map (Subring.subtype 𝒪[LaurentSeries (ZMod 7)]) w :
      (LaurentSeries (ZMod 7))ˣ) : LaurentSeries (ZMod 7))
      = ((1 + z : ↥𝒪[LaurentSeries (ZMod 7)]) : LaurentSeries (ZMod 7)) := by
    rw [Units.coe_map, hw]
    rfl
  rw [hcoe, ← Subring.coe_pow, hz3]
  push_cast
  rfl

end FqXt
end L20261018

#print axioms L20261018.FqXt.one_add_mem_cubes
