import L20261018.Ch2.Hensel.UnitsCupVanish.Step006_principal_units_pow_hensel

/-!
# R1180（**残余 (P) 第二块 (U2)：`𝒪^× ↠ 𝓀^×` 满（Hensel／局部环）**）

## 本轮做什么

`Hyp295` 把 `UnitsCupVanish` 归约到 (P)；`PLAN-R2` §H-41 把 (P) 的数学内容
`|𝒪_F^×/(𝒪_F^×)^p| = p` 分成三块。(U1) 已在 `Hyp296` 机检。本轮做 **(U2)**：

> 剩余映射 `𝒪^× → 𝓀^×` 是**满的**（每个非零剩余类都有单位代表）。

理由（局部环 ＋ `residue` 满）：取 `r : 𝓀^×`，`residue` 满给 `a` 使 `residue a = r`；
`r ≠ 0` ⟹ `a ∉ 𝔪` ⟹ `a` 是单位（局部环：`𝔪` 补＝单位群）。

**(U2) 的用途**：把 `𝒪^×/(𝒪^×)^p` 与 `𝓀^×/(𝓀^×)^p` 对齐 —— 因 (U1) 给出
`U^{(1)} ⊆ (𝒪^×)^p`，故核在模 `p` 次幂下消失，于是

```
𝒪^×/(𝒪^×)^p  ≅  𝓀^×/(𝓀^×)^p
```

再由 (U3)（`𝓀^×` 循环、`p ∣ q−1`）得 `≅ Z/p` ⟹ **(P)** ⟹ `UnitsCupVanish`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`exists_unit_residue_eq`** | ★★★★★ **(U2)：`∀ r : 𝓀^×, ∃ u : Rˣ, residue u = r`** |
| **`one_add_subset_pow`** | (U1) 的单位形式：`y ∈ 1+𝔪 ⟹ ∃ z, z^p = y` 且 `z ∈ 1+𝔪` |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ResidueSurj

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- ★★★★★ **(U2)：剩余映射在单位群上满** —— 每个非零剩余类都有 `Rˣ` 的代表。

`residue` 满 ＋「`a ∉ 𝔪` ⟹ `a` 是单位」（局部环）。 -/
theorem exists_unit_residue_eq (r : (IsLocalRing.ResidueField R)ˣ) :
    ∃ u : Rˣ, IsLocalRing.residue R ((u : R)) = ((r : IsLocalRing.ResidueField R)) := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (r : IsLocalRing.ResidueField R)
  have hnotmem : a ∉ IsLocalRing.maximalIdeal R := by
    intro hmem
    have h0 : IsLocalRing.residue R a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr hmem
    rw [ha] at h0
    exact Units.ne_zero r h0
  have hunit : IsUnit a := by
    by_contra h
    exact hnotmem ((IsLocalRing.mem_maximalIdeal a).mpr h)
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨u, ha⟩

end ResidueSurj

section OneAddPow

variable (R : Type*) [CommRing R] [IsLocalRing R]
  [HenselianRing R (IsLocalRing.maximalIdeal R)]

/-- ★★★★★ **(U1) 的单位形式**：`y ∈ 1+𝔪 ⟹ y 是 Rˣ 中某元素的 p 次幂`。

由 `Hyp296.pow_surj_on_one_add_maximalIdeal`（Hensel）＋「`x ∈ 1+𝔪` ⟹ `x` 是单位」。 -/
theorem one_add_subset_pow (p : ℕ) (hp0 : p ≠ 0) (hp : IsUnit (p : R)) {y : R}
    (hy : y - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ z : Rˣ, ((z : R)) ^ p = y ∧ ((z : R) - 1) ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨x, hx, hxp⟩ := pow_surj_on_one_add_maximalIdeal R p hp0 hp hy
  have hnotmem : x ∉ IsLocalRing.maximalIdeal R := by
    intro hmem
    have hsub : x - 1 ∈ IsLocalRing.maximalIdeal R := hx
    have h1m : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have h := sub_mem hmem hsub
      simpa using h
    exact ((IsLocalRing.mem_maximalIdeal (1 : R)).mp h1m) isUnit_one
  have hunit : IsUnit x := by
    by_contra h
    exact hnotmem ((IsLocalRing.mem_maximalIdeal x).mpr h)
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨u, hxp, hx⟩

end OneAddPow

end L20261018

#print axioms L20261018.exists_unit_residue_eq
#print axioms L20261018.one_add_subset_pow
