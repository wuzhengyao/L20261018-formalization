import L20261018.Hyp307

/-!
# R1199（消 `hπ` 与 `[Fact (Irreducible (X^p − C π))]`）

`Hyp303` 四条除 `hv : ValCompat v` 外还带 `hπ : v π = ofAdd 1` 与
`[Fact (Irreducible (X ^ p - C (π : F)))]`。用 `v := vCompatHom` 后两者都可**证**：

* `hπ`：取 `π` 为 `𝒪[F]` 的**一致化元**（`IsDiscreteValuationRing.exists_irreducible`），
  `zval π = znat π = 1`；
* `Irreducible (X^p − C π)`：由 Capelli（`Hyp294`）等价于 `π ∉ (Fˣ)^p`，
  而 `zval π = 1` 时若 `π = z^p` 则 `1 = p · zval z`，矛盾。

## 本轮
| 声明 | 内容 |
|---|---|
| `zval_pow` | `zval (a^n) = n * zval a` |
| **`zval_uniformizer`** | ★★★★★ 一致化元的阶是 `1` |
| **`not_pow_of_zval_eq_one`** | ★★★★★ `zval a = 1` ⟹ `a` 不是 `p`（`p > 1`）次幂 |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Uniformizer

variable {F : Type} [Field F] [ValuativeRel F] [IsDiscreteValuationRing ↥𝒪[F]]

/-- `zval` 的幂公式。 -/
theorem zval_pow (a : Fˣ) :
    ∀ n : ℕ, zval (F := F) (a ^ n) = n * zval (F := F) a
  | 0 => by simp [zval_one]
  | n + 1 => by
      rw [pow_succ, zval_mul, zval_pow a n]
      push_cast
      ring

/-- ★★★★★ **一致化元（作为 `Fˣ` 的元素）的阶是 `1`**。

`π : ↥𝒪[F]` 不可约 ⟹ `(π : F) ≠ 0` ⟹ `π : Fˣ`；其阶 `zval = znat π = 1`。 -/
theorem zval_uniformizer {π : ↥𝒪[F]} (hπ : Irreducible π) :
    zval (F := F) (Units.mk0 (π : F) (by
      intro h
      exact hπ.ne_zero (Subtype.ext h))) = 1 := by
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hint : (Units.mk0 (π : F) hπ0 : F) ∈ 𝒪[F] := π.2
  rw [zval_eq_znat (F := F) hint]
  have hsub : (⟨(Units.mk0 (π : F) hπ0 : F), hint⟩ : ↥𝒪[F]) = π := Subtype.ext rfl
  rw [hsub]
  simp only [znat]
  rw [IsDiscreteValuationRing.addVal_uniformizer hπ]
  rfl

/-- ★★★★★ **阶为 `1` 的元素不是 `p` 次幂**（`p > 1`）。

若 `a = z^p`，则 `zval a = p · zval z = 1`，与 `p > 1` 矛盾。 -/
theorem not_pow_of_zval_eq_one {a : Fˣ} (ha : zval (F := F) a = 1) {p : ℕ} (hp : 1 < p) :
    ∀ z : Fˣ, z ^ p ≠ a := by
  intro z hz
  have h1 : zval (F := F) (z ^ p) = 1 := by rw [hz, ha]
  rw [zval_pow] at h1
  have hp' : (2 : ℤ) ≤ (p : ℤ) := by
    have : 2 ≤ p := hp
    exact_mod_cast this
  by_cases hle : zval (F := F) z ≤ 0
  · nlinarith
  · push_neg at hle
    nlinarith

end Uniformizer

end L20261018

#print axioms L20261018.zval_pow
#print axioms L20261018.zval_uniformizer
#print axioms L20261018.not_pow_of_zval_eq_one
