import Hyp198

/-!
# R1052（**S29 · ④.2 第二步**）：`v(N y) ≡ 0 (mod p)` ⟹ `N(y)` 是 `p` 次幂

`Hyp198`（`Hyp197` ＋ Hensel）处理 `v (N y) = 0` 的**单位情形**。本文件把假设降到 (R1) 真正需要的形态

```
valOfUnitOf v (N_{L/F} y) = 0      --  即  v (N y) ≡ 0 (mod p)
```

**归约**：`(p:ℤ) ∣ toAdd (v u)` ⟹ 取 `k` 使 `toAdd (v u) = p·k`，令 `cπ := π^k`、
`y' := y · (cπ)⁻¹`（在 `Lˣ` 里除）。则

* `N(y') = N(y) · (cπ)⁻¹ = u · (cπᵖ)⁻¹`（`TauCeti.Algebra.normUnits_unitsMap_algebraMap` ＋
  `finrank_adjoinRoot_uniformizer`），
* `toAdd (v (N y')) = p·k − p·k = 0` ⟹ `Hyp198` 适用 ⟹ `N(y') = y₁ᵖ`，
* `u = N(y')·cπᵖ = (y₁·cπ)ᵖ` ✓

## 新增小引理（`Multiplicative ℤ` 的 `zpow` API，本 pin 缺）

| 声明 | 内容 |
|---|---|
| **`toAdd_zpow'`** | `toAdd (a ^ n) = n * toAdd a`（`n : ℤ`；`Hyp115.toAdd_pow'` 的 `ℤ` 版） |
| **`toAdd_val_zpow'`** | `toAdd (v (π ^ k)) = k`（`Hyp121.toAdd_val_pi_pow` 的 `ℤ` 版、任意 `v` 版） |

> `Multiplicative` 的 API 在本 pin **只有 `toAdd_mul'`／`toAdd_pow'`（本战役自带）与 `toAdd_inv'`（`rfl`）**；
> `Multiplicative.toAdd_pow`／`toAdd_mul`／`ofAdd_mul`／`ofAdd_zpow` **都不存在**（已 `#check`）。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section ToAddZpow

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}

/-- `toAdd (a ^ n) = n · toAdd a`（`n : ℤ`）。 -/
lemma toAdd_zpow' (a : Multiplicative ℤ) (n : ℤ) :
    Multiplicative.toAdd (a ^ n) = n * Multiplicative.toAdd a := by
  rcases Int.le_total 0 n with hn | hn
  · have h1 : a ^ n = a ^ n.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hn]
    rw [h1, toAdd_pow', Int.toNat_of_nonneg hn]
  · have h1 : a ^ n = (a ^ (-n))⁻¹ := by rw [zpow_neg, inv_inv]
    have h2 : a ^ (-n) = a ^ (-n).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n)]
    rw [h1, toAdd_inv', h2, toAdd_pow', Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n)]
    ring

/-- **`toAdd (v (π^k)) = k`**（`k : ℤ`；`Hyp121.toAdd_val_pi_pow` 的 `ℤ` 版、任意 `v` 版）。 -/
lemma toAdd_val_zpow' (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (k : ℤ) :
    Multiplicative.toAdd (v (π ^ k)) = k := by
  rw [map_zpow, toAdd_zpow']
  have h1 : Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = 1 := rfl
  rw [hπ, h1, mul_one]

end ToAddZpow

section GeneralCase

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **④.2 一般情形**：`v (N y) ≡ 0 (mod p)` ⟹ `N(y)` 是 `F` 中的 `p` 次幂。 -/
theorem normUnits_mem_pow_of_valOfUnitOf_eq_zero
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (y : (AdjoinRoot (X ^ p - C (π : F)))ˣ)
    (hval : valOfUnitOf (p := p) v (TauCeti.Algebra.normUnits F y) = 0) :
    TauCeti.Algebra.normUnits F y ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  classical
  set u₀ : Fˣ := TauCeti.Algebra.normUnits F y with hu₀
  -- `(p : ℤ) ∣ toAdd (v u₀)`
  have hdv : (p : ℤ) ∣ Multiplicative.toAdd (v u₀) := by
    have h := hval
    rw [valOfUnitOf] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (Multiplicative.toAdd (v u₀)) p).mp h
  obtain ⟨k, hk⟩ := hdv
  -- 除以 `(π^k)ᵖ`
  set cπ : Fˣ := π ^ k with hcπ
  set y' : (AdjoinRoot (X ^ p - C (π : F)))ˣ :=
    y * (Units.map (algebraMap F (AdjoinRoot (X ^ p - C (π : F))) : F →* AdjoinRoot (X ^ p - C (π : F))) cπ)⁻¹ with hy'def
  have hFree : Module.Free F (AdjoinRoot (X ^ p - C (π : F))) :=
    free_adjoinRoot_uniformizer_f (F := F) p π
  have hnorm_c : TauCeti.Algebra.normUnits F
      (Units.map (algebraMap F (AdjoinRoot (X ^ p - C (π : F))) : F →* AdjoinRoot (X ^ p - C (π : F))) cπ) = cπ ^ p := by
    rw [TauCeti.Algebra.normUnits_unitsMap_algebraMap, finrank_adjoinRoot_uniformizer]
  have hnorm_y' : TauCeti.Algebra.normUnits F y' = u₀ * (cπ ^ p)⁻¹ := by
    rw [hy'def, map_mul, map_inv, hnorm_c]
  -- 赋值降为 `0`
  have hcp : Multiplicative.toAdd (v (cπ ^ p)) = (p : ℤ) * k := by
    rw [hcπ, map_pow, toAdd_pow', toAdd_val_zpow' (F := F) hπ]
  have hval' : Multiplicative.toAdd (v (TauCeti.Algebra.normUnits F y')) = 0 := by
    rw [hnorm_y', map_mul, map_inv, toAdd_mul', toAdd_inv', hcp, hk]
    ring
  -- 单位情形（`Hyp198`）
  obtain ⟨y₁, hy₁⟩ := normUnits_mem_pow_of_val_eq_zero (F := F) p hp hv hπ hp2 y' hval'
  -- 拼回
  refine ⟨y₁ * cπ, ?_⟩
  have hy₁' : y₁ ^ p = TauCeti.Algebra.normUnits F y' := hy₁
  have hsplit : u₀ = TauCeti.Algebra.normUnits F y' * cπ ^ p := by
    rw [hnorm_y', mul_assoc, inv_mul_cancel, mul_one]
  show (y₁ * cπ) ^ p = u₀
  rw [mul_pow, hy₁', hsplit]

end GeneralCase

end L20261018

#print axioms L20261018.toAdd_zpow'
#print axioms L20261018.toAdd_val_zpow'
#print axioms L20261018.normUnits_mem_pow_of_valOfUnitOf_eq_zero

