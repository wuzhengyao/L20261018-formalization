import Hyp308

/-!
# R1200（无条件版的核心输入：构造性的一致化元 `π`）

`Hyp303` 四条带 `{π : Fˣ}`、`hπ : v π = ofAdd 1`、`[Fact (Irreducible (X^p − C π))]`。
本轮把这三样**一并构造出来**（取 `v := vCompatHom`）：

* `π` := `𝒪[F]` 的一个不可约元（`IsDiscreteValuationRing.exists_irreducible`）作为 `Fˣ` 的元素；
* `zval π = 1`（`Hyp308.zval_uniformizer`）；
* `π ∉ (Fˣ)^p`（`Hyp308.not_pow_of_zval_eq_one`）⟹ **`∀ b : F, b^p ≠ π`**（含 `b = 0`）。

## 本轮
| 声明 | 内容 |
|---|---|
| **`exists_uniformizer_not_pow`** | ★★★★★ `∃ π : Fˣ, zval π = 1 ∧ ∀ b : F, b^p ≠ (π:F)` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section UniformizerExists

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]
variable {p : ℕ} [Fact p.Prime]

/-- ★★★★★ **存在阶为 `1` 且非 `p` 次幂的元**（一步给出 `hπ` 与 Capelli 的输入）。

取 `𝒪[F]` 的不可约元 `π₀`，作为 `Fˣ` 的元素 `π`：
`zval π = znat π₀ = 1`，且 `π ∉ (Fˣ)^p`，故 `∀ b : F, b^p ≠ π`（`b = 0` 由 `π ≠ 0` 排除）。 -/
theorem exists_uniformizer_not_pow (hp2' : p ≠ 1) :
    ∃ π : Fˣ, zval (F := F) π = 1 ∧ ∀ b : F, b ^ p ≠ (π : F) := by
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[F]
  have hπ₀0 : (π₀ : F) ≠ 0 := by
    intro h
    exact hπ₀.ne_zero (Subtype.ext h)
  refine ⟨Units.mk0 (π₀ : F) hπ₀0, zval_uniformizer hπ₀, ?_⟩
  intro b hb
  have hp1 : 1 < p := by
    have := (Fact.out : p.Prime).two_le
    omega
  rcases eq_or_ne b 0 with hb0 | hb0
  · rw [hb0, zero_pow (by omega : p ≠ 0)] at hb
    exact hπ₀0 hb.symm
  · refine not_pow_of_zval_eq_one (zval_uniformizer hπ₀) hp1 (Units.mk0 b hb0) ?_
    exact Units.ext (by simpa using hb)

end UniformizerExists

end L20261018

#print axioms L20261018.exists_uniformizer_not_pow
