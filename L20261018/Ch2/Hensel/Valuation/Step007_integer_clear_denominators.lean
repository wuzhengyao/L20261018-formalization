import L20261018.Ch2.Hensel.Valuation.Step006_residue_map_subring

/-!
# R1023（路径 A · **A1′·2·b·ii**）：整性判据的**系数侧** —— 任意元素乘 `π` 的幂后落在 `𝒪_F` 中

A1′·2 的整性判据（`N(x)` 单位 ⟹ `x ∈ 𝒪_F[s]`）需要两步：
1. **系数侧（本文件）**：任意 `a : F` 乘上 `π` 的某个幂后是 `𝒪_F` 的元素（`F = Frac 𝒪_F` 的离散形式）；
2. **扩域侧**（下一轮）：`x = s^{-n} y`（`y ∈ 𝒪_F[s]`）＋ 模 `s` 的范数残差 ⟹ `n = 0`。

| 声明 | 内容 |
|---|---|
| **`ValIntegralityCompat`** | 非负赋值元素是 `𝒪_F` 的单位（`𝒪_F` 的「整数性」，与 `Hyp168` 的 `𝔪`／`𝔪²` 滤过互补） |
| **`exists_uniformizer_pow_mul_mem_integer`** | `∀ a : F, ∃ n : ℕ, (π : F)^n * a ∈ 𝒪_F` |

> 与 `Hyp168.ValFiltrationCompat`（`𝔪`／`𝔪²` 滤过，管「`>0` 与 `>1`」）互补：本条管「`≥0`」。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Integrality

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **`v` 与 `𝒪_F` 的成员判定**：非负赋值 ⟹ 是 `𝒪_F` 的单位。 -/
structure ValIntegralityCompat (v : Fˣ →* Multiplicative ℤ) : Prop where
  /-- 非负赋值的元素来自 `𝒪_F` 的单位。 -/
  exists_unit_of_nonneg : ∀ a : Fˣ, 0 ≤ Multiplicative.toAdd (v a) →
    ∃ b : 𝒪[F]ˣ, Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = a

/-- **系数侧整性**：每个 `a : F` 乘上 `π` 的某个幂后落在 `𝒪_F` 中。 -/
theorem exists_uniformizer_pow_mul_mem_integer (hv : ValIntegralityCompat (F := F) v) (π : Fˣ)
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (a : F) :
    ∃ n : ℕ, (π : F) ^ n * a ∈ 𝒪[F] := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp⟩
  · set u : Fˣ := Units.mk0 a ha with hu
    have huval : (u : F) = a := rfl
    by_cases hm0 : 0 ≤ Multiplicative.toAdd (v u)
    · -- 已是整数：`n = 0`
      obtain ⟨b, hb⟩ := hv.exists_unit_of_nonneg u hm0
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, ← huval, ← hb]
      exact (b : ↥𝒪[F]).2
    · -- 取 `n = (-toAdd (v u)).toNat`
      set k : ℕ := (-(Multiplicative.toAdd (v u))).toNat with hk
      have hkval : (k : ℤ) = -(Multiplicative.toAdd (v u)) := by
        rw [hk]
        exact Int.toNat_of_nonneg (by omega)
      have hkey : Multiplicative.toAdd (v (π ^ k * u))
          = (k : ℤ) + Multiplicative.toAdd (v u) := by
        rw [map_mul, toAdd_mul', map_pow, toAdd_pow', hπ]
        simp
      have hnonneg : (0 : ℤ) ≤ Multiplicative.toAdd (v (π ^ k * u)) := by
        rw [hkey, hkval]; omega
      obtain ⟨b, hb⟩ := hv.exists_unit_of_nonneg (π ^ k * u) hnonneg
      refine ⟨k, ?_⟩
      have hbF : ((b : ↥𝒪[F]) : F) = (π : F) ^ k * a := by
        have h1 : ((b : ↥𝒪[F]) : F) = ((π ^ k * u : Fˣ) : F) := by
          rw [← hb]; rfl
        rw [h1]
        push_cast
        rfl
      rw [← hbF]
      exact (b : ↥𝒪[F]).2

end Integrality

end L20261018

#print axioms L20261018.exists_uniformizer_pow_mul_mem_integer
