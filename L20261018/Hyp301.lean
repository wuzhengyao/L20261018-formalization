import Hyp300

/-!
# R1186（**(P) 收口的运输步 1–2：`Fˣ → 𝒪[F]ˣ → 𝓀ˣ`**）

## 本轮做什么

`Hyp300.exists_pow_mul_pow_of_isCyclic` 在**循环有限群**上给出 (P) 的群论形态。
要把它搬到 `Fˣ`，须走 `Fˣ ⊇ {v = 1} ≅ 𝒪[F]ˣ --residue--> 𝓀ˣ`。本轮落成运输的**两个端**：

| # | 陈述 | 依据 |
|---|---|---|
| **运输 1** | `v a = 1 ⟹ a ∈ 𝒪[F]` 且是 `𝒪[F]ˣ` 的元素 | `ValCompat.mem_integer` ＋ `ValCompat.mem_maximalIdeal` |
| **运输 2** | `residue a = 1 ⟹ a 是 𝒪[F]ˣ 中的 p 次幂` | `Hyp297.one_add_subset_pow`（(U1)）＋ `residue_eq_zero_iff` |

运输 1 的意义：`PowClassGen`（`Hyp292`）活在 `Fˣ` 上，而 `residue` 活在 `𝒪[F]ˣ` 上；
`ValCompat` 的 `mem_integer`（`0 ≤ v a ⟹ a ∈ 𝒪[F]`）＋ `mem_maximalIdeal`
（`a ∈ 𝔪 ↔ 0 < v a`）恰好把 `v a = 0` 的元素识别为 `𝒪[F]ˣ`。

运输 2 的意义：`residue a = 1 ⟺ a ∈ 1+𝔪`，而 (U1) 说 `1+𝔪 ⊆ (𝒪[F]ˣ)^p`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_unitOf_of_val_eq_one`** | ★★★★★ **运输 1**：`v a = 1 ⟹ ∃ u : 𝒪[F]ˣ, (u : F) = (a : F)` |
| **`exists_pow_of_residue_eq_one`** | ★★★★★ **运输 2**：`residue a = 1 ⟹ ∃ c : 𝒪[F]ˣ, c^p = a` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Transport

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
variable {v : Fˣ →* Multiplicative ℤ}

/-- ★★★★★ **运输 1**：`v a = 1`（即 `a` 是整价单位）⟹ `a` 来自 `𝒪[F]ˣ`。

`ValCompat.mem_integer` 给 `a ∈ 𝒪[F]`（因 `toAdd (v a) = 0 ≥ 0`），
`ValCompat.mem_maximalIdeal` 给 `a ∉ 𝔪`（因 `¬ 0 < toAdd (v a)`），
局部环中 `∉ 𝔪 ⟺ IsUnit`。 -/
theorem exists_unitOf_of_val_eq_one (hv : ValCompat (F := F) v) {a : Fˣ} (ha : v a = 1) :
    ∃ u : (↥𝒪[F])ˣ, (((u : ↥𝒪[F]) : F)) = (a : F) := by
  have hzero : Multiplicative.toAdd (v a) = 0 := by rw [ha]; rfl
  have hint : (a : F) ∈ 𝒪[F] := hv.mem_integer a (by rw [hzero])
  have hnotmem : (⟨(a : F), hint⟩ : ↥𝒪[F]) ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    intro hmem
    have h := (hv.mem_maximalIdeal a hint).mp hmem
    rw [hzero] at h
    exact lt_irrefl 0 h
  have hunit : IsUnit (⟨(a : F), hint⟩ : ↥𝒪[F]) := by
    by_contra h
    exact hnotmem ((IsLocalRing.mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hunit
  exact ⟨u, by rw [hu]⟩

/-- ★★★★★ **运输 2**：`residue a = 1` ⟹ `a` 是 `𝒪[F]ˣ` 中的 `p` 次幂。

`residue a = 1` ⟹ `a - 1 ∈ 𝔪`（`residue_eq_zero_iff`），再用 (U1)
`Hyp297.one_add_subset_pow`。 -/
theorem exists_pow_of_residue_eq_one (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsUnit (p : ↥𝒪[F])) {a : (↥𝒪[F])ˣ}
    (ha : IsLocalRing.residue ↥𝒪[F] ((a : ↥𝒪[F])) = 1) :
    ∃ c : (↥𝒪[F])ˣ, c ^ p = a := by
  have hmem : (a : ↥𝒪[F]) - 1 ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    have h1 : IsLocalRing.residue ↥𝒪[F] ((a : ↥𝒪[F]) - 1) = 0 := by
      rw [map_sub, map_one, ha, sub_self]
    exact (IsLocalRing.residue_eq_zero_iff ((a : ↥𝒪[F]) - 1)).mp h1
  obtain ⟨z, hz, _⟩ := one_add_subset_pow ↥𝒪[F] p hp0 hp hmem
  exact ⟨z, Units.ext hz⟩

end Transport

end L20261018

#print axioms L20261018.exists_unitOf_of_val_eq_one
#print axioms L20261018.exists_pow_of_residue_eq_one
