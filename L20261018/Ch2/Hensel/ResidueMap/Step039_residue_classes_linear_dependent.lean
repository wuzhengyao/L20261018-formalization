import L20261018.Ch2.Hensel.ResidueMap.Step038_ker_v_finrank_pos

/-!
# R1285（S36 C 项 · `hK1` 上界 #1）：剩余层「任意两个立方类线性相关」

`hK1`（`finrank (ker v̄) = 1`）的上界需要：**任意两个阶 0 单位，其差是某个立方**。
本文件把该命题降到 `𝔽₇ˣ`（在那里可 `decide`），再沿 `Hyp352.residueEquiv : 𝓀 ≃+* 𝔽₇` 抬回。

| 声明 | 内容 |
|---|---|
| `residueUnitsEquiv` | `𝓀ˣ ≃* 𝔽₇ˣ`（`residueEquiv` 在单位层） |
| **`residue_dependent`** | ★★★★★ `∀ U W : ↥𝒪ˣ, ∃ j : ZMod 3, ∃ V, residue U = (residue V)³ · (residue W)^j` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- `𝓀[𝔽₇((t))]ˣ ≃* 𝔽₇ˣ`（`Hyp352.residueEquiv` 在单位层）。 -/
noncomputable def residueUnitsEquiv :
    (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ ≃* (ZMod 7)ˣ :=
  Units.mapEquiv (residueEquiv).toMulEquiv

/-- `↥𝒪ˣ →* 𝔽₇ˣ`（剩余再取单位等价）。 -/
noncomputable def chi : (↥𝒪[LaurentSeries (ZMod 7)])ˣ →* (ZMod 7)ˣ :=
  residueUnitsEquiv.toMonoidHom.comp unitsResidue

theorem chi_surjective : Function.Surjective (chi) :=
  residueUnitsEquiv.surjective.comp unitsResidue_surjective

/-- ★★★★ **`𝔽₇ˣ` 的立方类群 ≅ `ℤ/3`**：任意两元，其一必是另一个的幂乘立方（**对称形式**，
因为「彼此都是立方」时两边都平凡）。`decide`。 -/
theorem zmod7_cube_dependent_closed :
    ∀ x y : (ZMod 7)ˣ,
      (∃ j : ZMod 3, ∃ c : (ZMod 7)ˣ, c ^ 3 * y ^ (j.val : ℕ) = x) ∨
        (∃ j : ZMod 3, ∃ c : (ZMod 7)ˣ, c ^ 3 * x ^ (j.val : ℕ) = y) := by
  decide

/-- ★★★★★ **剩余层线性相关**：任意两个 `𝒪` 的单位，`U` 与 `W^j` 只差一个「剩余为立方」的因子。 -/
theorem residue_dependent (U W : (↥𝒪[LaurentSeries (ZMod 7)])ˣ) :
    (∃ j : ZMod 3, ∃ V : (↥𝒪[LaurentSeries (ZMod 7)])ˣ,
      unitsResidue U = (unitsResidue V) ^ 3 * (unitsResidue W) ^ (j.val : ℕ)) ∨
    (∃ j : ZMod 3, ∃ V : (↥𝒪[LaurentSeries (ZMod 7)])ˣ,
      unitsResidue W = (unitsResidue V) ^ 3 * (unitsResidue U) ^ (j.val : ℕ)) := by
  rcases zmod7_cube_dependent_closed (chi U) (chi W) with ⟨j, c, hc⟩ | ⟨j, c, hc⟩
  · obtain ⟨V, hV⟩ := chi_surjective c
    left
    refine ⟨j, V, ?_⟩
    apply residueUnitsEquiv.injective
    show chi U = chi (V ^ 3 * W ^ (j.val : ℕ))
    rw [map_mul, map_pow, map_pow, hV, hc]
  · obtain ⟨V, hV⟩ := chi_surjective c
    right
    refine ⟨j, V, ?_⟩
    apply residueUnitsEquiv.injective
    show chi W = chi (V ^ 3 * U ^ (j.val : ℕ))
    rw [map_mul, map_pow, map_pow, hV, hc]

end FqXt
end L20261018

#print axioms L20261018.FqXt.zmod7_cube_dependent_closed
#print axioms L20261018.FqXt.residue_dependent
