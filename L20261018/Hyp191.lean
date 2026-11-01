import L20261018.Hyp190

/-!
# R1044（路径 A · **S28 第 3 步的前提**）：`𝔪 = (π)` —— `𝔪` 中元素都被一致化元整除

整性判据（`N(x)` 单位 ⟹ `x ∈ 𝒪_F[s]`）的**极小性论证**需要 DVR 性质
「`a ∈ 𝔪 ⟹ a = π·a'`」。本文件从 `ValCompat` 机检它：

* `a ∈ 𝔪` ⟺ `0 < v(a)`（`ValCompat.mem_maximalIdeal`）；
* `v(a/π) = v(a) − 1 ≥ 0` ⟹ `a/π ∈ 𝒪_F`（`ValCompat.mem_integer`）；
* 故 `a = π·(a/π)` ✓

| 声明 | 内容 |
|---|---|
| **`exists_mul_uniformizer_of_mem_maximalIdeal`** | **`a ∈ 𝔪 → ∃ a' : ↥𝒪_F, a = b * a'`**（`b` 是 `π` 的像） |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section DivUniformizer

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **`𝔪 = (π)`**：`𝔪` 中的元素都能被一致化元整除。 -/
theorem exists_mul_uniformizer_of_mem_maximalIdeal (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : ↥𝒪[F]} (hb : (b : F) = (π : F))
    {a : ↥𝒪[F]} (ha : a ∈ IsLocalRing.maximalIdeal ↥𝒪[F]) :
    ∃ a' : ↥𝒪[F], a = b * a' := by
  by_cases ha0 : (a : F) = 0
  · exact ⟨0, Subtype.ext (by simp [ha0])⟩
  · set u : Fˣ := Units.mk0 (a : F) ha0 with hu
    have huv : (u : F) = (a : F) := rfl
    have ha𝒪 : (u : F) ∈ 𝒪[F] := by rw [huv]; exact a.2
    -- `a ∈ 𝔪` ⟹ `0 < v u`
    have hpos : 0 < Multiplicative.toAdd (v u) := by
      have hmem : (⟨(u : F), ha𝒪⟩ : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
        have hEq : (⟨(u : F), ha𝒪⟩ : ↥𝒪[F]) = a := Subtype.ext huv
        rwa [hEq]
      exact (hv.mem_maximalIdeal u ha𝒪).mp hmem
    -- `v (u/π) = v u − 1 ≥ 0`
    have hnonneg : 0 ≤ Multiplicative.toAdd (v (u / π)) := by
      rw [map_div, toAdd_div, hπ, toAdd_ofAdd]
      omega
    refine ⟨⟨((u / π : Fˣ) : F), hv.mem_integer (u / π) hnonneg⟩, ?_⟩
    apply Subtype.ext
    show (a : F) = (b : F) * ((u / π : Fˣ) : F)
    rw [hb, ← huv, mul_comm]
    rw [← Units.val_mul, div_mul_cancel]

end DivUniformizer

end L20261018

#print axioms L20261018.exists_mul_uniformizer_of_mem_maximalIdeal
