import L20261018.Hyp186

/-!
# R1040（**修复 R1039 的空假设**）：元素级 `ValCompat` ＋ 重述受影响的定理

R1039 机检了 `ValFiltrationCompat` 的假设类为空（`Hyp186.valFiltrationCompat_false`）。
本文件给出**一致**的替代结构（`𝒪_F`/`𝔪` 判据都用**元素**，不用 `𝒪_Fˣ`＝单位）：

```lean
structure ValCompat (v : Fˣ →* Multiplicative ℤ) : Prop where
  mem_integer : ∀ a : Fˣ, 0 ≤ toAdd (v a) → (a : F) ∈ 𝒪[F]
  mem_maximalIdeal : ∀ (a : Fˣ) (h : (a : F) ∈ 𝒪[F]),
    (⟨(a : F), h⟩ : ↥𝒪[F]) ∈ 𝔪 ↔ 0 < toAdd (v a)
```

对 DVF ＋ 一致化元：`v π = 1`、`π ∈ 𝒪_F`、`π ∈ 𝔪 ⟺ 0 < 1` ✓ —— **一致**（旧结构要求 `π` 是单位，故为空）。

| 声明 | 内容 |
|---|---|
| **`ValCompat`** | 元素级判据（见上） |
| **`valCompat_uniformizer_mem_integer`** | `π ∈ 𝒪_F` |
| **`valCompat_uniformizer_mem_maximalIdeal`** | `π ∈ 𝔪` |
| **`valCompat_exists_pow_mul_mem_integer`** | `∀ a : F, ∃ n, πⁿ·a ∈ 𝒪_F`（清分母） |
| **`valCompat_pow_mul_mem_integer_mono`** | 清分母的单调性 |

> **未完成（必须补，本仓 L1/L10①）**：`ValCompat` 的**非空见证**（计划：在 `ℚ_p` 上实例化）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section ValCompatFixed

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **元素级赋值相容性**（替换病态的单位级结构）。 -/
structure ValCompat (v : Fˣ →* Multiplicative ℤ) : Prop where
  /-- 非负赋值的元素在 `𝒪_F` 中（**元素**，非单位）。 -/
  mem_integer : ∀ a : Fˣ, 0 ≤ Multiplicative.toAdd (v a) → (a : F) ∈ 𝒪[F]
  /-- `v > 0 ⟺ 元素在 `𝔪` 中`（元素级）。 -/
  mem_maximalIdeal : ∀ (a : Fˣ) (h : (a : F) ∈ 𝒪[F]),
    (⟨(a : F), h⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] ↔
      0 < Multiplicative.toAdd (v a)

/-- **一致化元在 `𝒪_F` 中**。 -/
theorem valCompat_uniformizer_mem_integer (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) : (π : F) ∈ 𝒪[F] :=
  hv.mem_integer π (by rw [hπ]; norm_num)

/-- **一致化元在 `𝔪` 中**。 -/
theorem valCompat_uniformizer_mem_maximalIdeal (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    (⟨(π : F), hv.mem_integer π (by rw [hπ]; norm_num)⟩ : ↥𝒪[F])
      ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
  have hπ𝒪 : (π : F) ∈ 𝒪[F] := hv.mem_integer π (by rw [hπ]; norm_num)
  exact (hv.mem_maximalIdeal π hπ𝒪).mpr (by rw [hπ]; norm_num)

/-- **清分母**：`∀ a : F, ∃ n, πⁿ·a ∈ 𝒪_F`。 -/
theorem valCompat_exists_pow_mul_mem_integer (hv : ValCompat (F := F) v) (π : Fˣ)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (a : F) :
    ∃ n : ℕ, (π : F) ^ n * a ∈ 𝒪[F] := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  · set u : Fˣ := Units.mk0 a ha with hu
    have huval : (u : F) = a := rfl
    by_cases hm0 : 0 ≤ Multiplicative.toAdd (v u)
    · exact ⟨0, by simpa [huval] using hv.mem_integer u hm0⟩
    · have hmneg : Multiplicative.toAdd (v u) < 0 := not_le.mp hm0
      set k : ℕ := (-(Multiplicative.toAdd (v u))).toNat with hk
      have hkval : (k : ℤ) = -(Multiplicative.toAdd (v u)) := by
        rw [hk]
        exact Int.toNat_of_nonneg (by omega)
      have hkey : Multiplicative.toAdd (v (π ^ k * u))
          = (k : ℤ) + Multiplicative.toAdd (v u) := by
        rw [map_mul, toAdd_mul', map_pow, toAdd_pow', hπ]
        simp
      have hnonneg : 0 ≤ Multiplicative.toAdd (v (π ^ k * u)) := by
        rw [hkey, hkval]
        omega
      have hmem := hv.mem_integer (π ^ k * u) hnonneg
      refine ⟨k, ?_⟩
      have hcoe : ((π ^ k * u : Fˣ) : F) = (π : F) ^ k * a := by
        simp [huval]
      rwa [hcoe] at hmem

/-- **清分母的单调性**。 -/
theorem valCompat_pow_mul_mem_integer_mono (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {a : F} {n m : ℕ} (hnm : n ≤ m)
    (ha : (π : F) ^ n * a ∈ 𝒪[F]) : (π : F) ^ m * a ∈ 𝒪[F] := by
  have hπ𝒪 : (π : F) ∈ 𝒪[F] := valCompat_uniformizer_mem_integer (F := F) hv hπ
  have hsplit : (π : F) ^ m * a = (π : F) ^ (m - n) * ((π : F) ^ n * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
  rw [hsplit]
  exact Subring.mul_mem _ (Subring.pow_mem _ hπ𝒪 _) ha

end ValCompatFixed

end L20261018

#print axioms L20261018.valCompat_uniformizer_mem_integer
#print axioms L20261018.valCompat_uniformizer_mem_maximalIdeal
#print axioms L20261018.valCompat_exists_pow_mul_mem_integer
#print axioms L20261018.valCompat_pow_mul_mem_integer_mono
