import L20261018.Witness.Step026_f7t_principal_units_cube

/-!
# R1268（S36 C 项 末步之二）：`𝒪[𝔽₇((t))]` 的单位「剩余类为立方 ⟹ 自身为立方」

`HANDOFF` §S36 收尾计划的第 2(b) 件。有了 `Hyp356`（`1+𝔪 ⊆ 立方`），
「单位是立方」在**剩余层完全确定**：

```
u · w⁻³ 的剩余类 = 1  ⟹  u·w⁻³ = 1 + y（y ∈ 𝔪）⟹  由 Hyp356 是立方 ⟹ u = 立方 · w³
```

| 声明 | 内容 |
|---|---|
| **`isCube_of_residue_cube`** | ★★★★★ `residue u = (residue w)³ ⟹ ↑u 在 Fˣ 中是立方` |
| **`isCube_of_residue_one`** | ★★★★ `residue u = 1 ⟹ ↑u 是立方`（上条的 `w = 1`） |

这是 `Finite (𝒪ˣ/(𝒪ˣ)³)` 的全部数学（`𝓀ˣ` 有限 ⟹ 只有 3 个立方类），
也是 `Finite (Fˣ/(Fˣ)³)` 的两块之一；另一块是 `π` 的 `ℤ/3` 生成元角色（下一件）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LaurentSeries ValuativeRel IsLocalRing Polynomial
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `↥𝒪[𝔽₇((t))]` 的极大理想（局部记号）。 -/
noncomputable abbrev mF' : Ideal ↥𝒪[LaurentSeries (ZMod 7)] := IsLocalRing.maximalIdeal _

/-- `↥𝒪[𝔽₇((t))]` 的单位群到 `Fˣ` 的映射（`abbrev`：下游要能便宜地展开）。 -/
noncomputable abbrev unitsToF :
    (↥𝒪[LaurentSeries (ZMod 7)])ˣ →* (LaurentSeries (ZMod 7))ˣ :=
  Units.map (Subring.subtype 𝒪[LaurentSeries (ZMod 7)])

/-- 剩余映射（`𝒪` 的单位群 → 剩余域的单位群）。 -/
noncomputable abbrev unitsResidue :
    (↥𝒪[LaurentSeries (ZMod 7)])ˣ →* (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ :=
  Units.map (IsLocalRing.residue ↥𝒪[LaurentSeries (ZMod 7)])

/-- ★★★★★ **剩余类为立方 ⟹ 自身为立方**（`𝒪[𝔽₇((t))]` 的单位，映到 `Fˣ`）。

设 `residue u = (residue w)³`。则 `u · w⁻³` 的剩余类为 `1`，即 `u·w⁻³ = 1 + y`（`y ∈ 𝔪`），
由 `Hyp356.one_add_mem_cubes` 有 `c³ = 1 + y = u·w⁻³`，
故 `(c · w)³ = u`（在 `Fˣ` 中）。 -/
theorem isCube_of_residue_cube (u w : (↥𝒪[LaurentSeries (ZMod 7)])ˣ)
    (h : unitsResidue u = (unitsResidue w) ^ 3) :
    ∃ c : (LaurentSeries (ZMod 7))ˣ,
      c ^ 3 = unitsToF u := by
  -- `u * w⁻³` 的剩余类为 1
  have hres1 : unitsResidue (u * (w ^ 3)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, h]
    simp
  -- 落到 `↥𝒪` 的剩余类上
  have hres1' : IsLocalRing.residue ↥𝒪[LaurentSeries (ZMod 7)]
      ((u * (w ^ 3)⁻¹ : (↥𝒪[LaurentSeries (ZMod 7)])ˣ) : ↥𝒪[LaurentSeries (ZMod 7)]) = 1 := by
    have := congrArg (fun x : (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ =>
      (x : IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])) hres1
    simpa [unitsResidue] using this
  -- `y := u·w⁻³ - 1 ∈ 𝔪`
  set A : ↥𝒪[LaurentSeries (ZMod 7)] :=
    ((u * (w ^ 3)⁻¹ : (↥𝒪[LaurentSeries (ZMod 7)])ˣ) : ↥𝒪[LaurentSeries (ZMod 7)]) with hA
  have hy : A - 1 ∈ mF' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, hres1', map_one, sub_self]
  obtain ⟨c, hc⟩ := one_add_mem_cubes (y := A - 1) hy
  -- `1 + ↑(A - 1) = ↑A`
  have hA' : (1 : LaurentSeries (ZMod 7)) + ((A - 1 : ↥𝒪[LaurentSeries (ZMod 7)]) : LaurentSeries (ZMod 7))
      = (A : LaurentSeries (ZMod 7)) := by
    push_cast
    ring
  rw [hA'] at hc
  -- `unitsToF` 与 `↥𝒪` 的强制转换相容（定义层）
  have hcoe_units : ∀ x : (↥𝒪[LaurentSeries (ZMod 7)])ˣ,
      ((unitsToF x : (LaurentSeries (ZMod 7))ˣ) : LaurentSeries (ZMod 7))
        = ((x : ↥𝒪[LaurentSeries (ZMod 7)]) : LaurentSeries (ZMod 7)) := fun x => rfl
  -- 抬到 `Fˣ`
  have hc'' : c ^ 3 = unitsToF (u * (w ^ 3)⁻¹) := by
    ext
    rw [Units.val_pow_eq_pow_val, hc, hcoe_units, hA]
  refine ⟨c * unitsToF w, ?_⟩
  rw [mul_pow, hc'', ← map_pow, ← map_mul]
  congr 1
  group

/-- ★★★★ **剩余类为 `1` ⟹ 自身为立方**（`isCube_of_residue_cube` 取 `w = 1`）。 -/
theorem isCube_of_residue_one (u : (↥𝒪[LaurentSeries (ZMod 7)])ˣ)
    (h : unitsResidue u = 1) :
    ∃ c : (LaurentSeries (ZMod 7))ˣ, c ^ 3 = unitsToF u := by
  refine isCube_of_residue_cube u 1 ?_
  rw [h, map_one, one_pow]

end FqXt
end L20261018

#print axioms L20261018.FqXt.isCube_of_residue_cube
#print axioms L20261018.FqXt.isCube_of_residue_one
