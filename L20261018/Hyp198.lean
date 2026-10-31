import Hyp197
import Hyp163
import TauCeti.RingTheory.Norm.Units

/-!
# R1051（**S29 · ④.2 第一步**）：单位范数是 `p` 次幂（Hensel）

(R1) 的**数学核心**：设 `y ∈ Lˣ`（`L = AdjoinRoot_F (Xᵖ − Cπ)`），若 `N(y)` 是 `𝒪_F` 的**单位**
（本件以 `v (N y) = 0` 陈述），则 `N(y)` 是 `F` 中的 `p` 次幂。

```
v (N_{L/F} y) = 0   ⟹   N(y) ∈ (·)ᵖ(Fˣ)
```

## 论证（④.1 ＋ Hensel，论文 `:1622`）

1. `v (N y) = 0` ⟹ `N y ∈ 𝒪_F`（`ValCompat.mem_integer`）且 `⟨N y, _⟩ ∉ 𝔪`（`mem_maximalIdeal`，`0 ≮ 0`）
   ⟹ `⟨N y, _⟩` 是 `𝒪_F` 的单位 `u`；
2. **④.1**（`Hyp197.exists_coeff_of_norm_mem_integer`）：`red u = (red (c 0))ᵖ`；
3. `red u ≠ 0`（单位）⟹ `red (c 0) ≠ 0` ⟹ 它是 `𝓀_Fˣ` 的元素，故 `red u` 是 `p` 次幂（单位层）；
4. **`Hyp163.unit_pow_of_residue_pow_of_hensel`**（`[HenselianRing 𝒪_F 𝔪]`、`p` 在 `𝒪_F` 中可逆）：
   `u = (z)ᵖ`，`z ∈ Fˣ` —— 即论文 `:1622` 的「`ar w ∈ K^{×p} ⟹ w ∈ K^{×p}`」。

## 层级说明

* **不需要**完备性：唯一输入是 `[HenselianRing 𝒪_F 𝔪]`（与 `Hyp163` 一致）。
* **不需要** `L` 是域（本件只对 `y : Lˣ` 陈述，把域性推后到 `normGroup` 那一步）。
* `hp2 : p ≠ 2` 来自 `Hyp171` 的 `N(s) = π` 的符号约定（论文：`p` 为奇素数）。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NormUnitsPow

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- **④.2 单位情形**：`N(y)` 是 `𝒪_F` 单位（即 `v (N y) = 0`）⟹ `N(y)` 是 `F` 中的 `p` 次幂。 -/
theorem normUnits_mem_pow_of_val_eq_zero
    [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
    (hp : IsUnit (p : ↥𝒪[F])) (hv : ValCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (y : (AdjoinRoot (X ^ p - C (π : F)))ˣ)
    (hval : Multiplicative.toAdd (v (TauCeti.Algebra.normUnits F y)) = 0) :
    TauCeti.Algebra.normUnits F y ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  classical
  set u₀ : Fˣ := TauCeti.Algebra.normUnits F y with hu₀
  have hcoe : (Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))) : F) = (u₀ : F) :=
    (TauCeti.Algebra.coe_normUnits (R := F) y).symm
  -- `N(y) ∈ 𝒪_F`
  have hx : (Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))) : F) ∈ 𝒪[F] := by
    rw [hcoe]
    exact hv.mem_integer u₀ (le_of_eq hval.symm)
  -- ④.1：整性判据
  obtain ⟨c, -, hres⟩ := exists_coeff_of_norm_mem_integer (F := F) p hv hπ hp2 hx
  -- `N(y)` 是 `𝒪_F` 单位
  have hx' : (u₀ : F) ∈ 𝒪[F] := by rw [← hcoe]; exact hx
  have hnotmem : (⟨(u₀ : F), hx'⟩ : ↥𝒪[F]) ∉ IsLocalRing.maximalIdeal ↥𝒪[F] := by
    intro hmem
    have hpos : 0 < Multiplicative.toAdd (v u₀) := (hv.mem_maximalIdeal u₀ hx').mp hmem
    rw [hval] at hpos
    exact lt_irrefl _ hpos
  have hunit : IsUnit (⟨Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))), hx⟩ : ↥𝒪[F]) := by
    have hEq : (⟨Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))), hx⟩ : ↥𝒪[F])
        = ⟨(u₀ : F), hx'⟩ := Subtype.ext hcoe
    rw [hEq]
    exact (IsLocalRing.notMem_maximalIdeal).mp hnotmem
  -- `red` 是 `p` 次幂
  set uu : (↥𝒪[F])ˣ := hunit.unit with huu
  have hspec : (uu : ↥𝒪[F]) = ⟨Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))), hx⟩ :=
    IsUnit.unit_spec hunit
  have hredpow : IsLocalRing.residue ↥𝒪[F] (uu : ↥𝒪[F])
      = (IsLocalRing.residue ↥𝒪[F] (c 0)) ^ p := by
    rw [hspec]; exact hres
  -- 残差非零 ⟹ `red c₀` 是单位
  have hru_ne : IsLocalRing.residue ↥𝒪[F] (uu : ↥𝒪[F]) ≠ 0 :=
    (uu.isUnit.map (IsLocalRing.residue ↥𝒪[F])).ne_zero
  have hredunit : IsUnit (IsLocalRing.residue ↥𝒪[F] (c 0)) := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hru_ne ?_
    rw [hredpow, h0, zero_pow (Fact.out : p.Prime).ne_zero]
  -- 剩余层：`red u` 是 `p` 次幂
  have hmap : Units.map (IsLocalRing.residue ↥𝒪[F] : ↥𝒪[F] →* 𝓀[F]) uu
      ∈ (powMonoidHom p : 𝓀[F]ˣ →* 𝓀[F]ˣ).range := by
    refine ⟨hredunit.unit, ?_⟩
    ext
    show (hredunit.unit : 𝓀[F]) ^ p = IsLocalRing.residue ↥𝒪[F] (uu : ↥𝒪[F])
    rw [hredpow, IsUnit.unit_spec hredunit]
  -- Hensel：`u` 本身是 `F` 中的 `p` 次幂
  have hmain := unit_pow_of_residue_pow_of_hensel (F := F) (p := p) hp uu hmap
  obtain ⟨y₁, hy₁⟩ := hmain
  refine ⟨y₁, ?_⟩
  have h1 : ((Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F)) uu : F)
      = (Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))) : F) := by
    rw [Units.coe_map]
    show ((uu : ↥𝒪[F]) : F) = _
    rw [hspec]
  ext
  show (y₁ : F) ^ p = (u₀ : F)
  rw [← hcoe]
  calc (y₁ : F) ^ p = (((powMonoidHom p) y₁ : Fˣ) : F) :=
        (Units.val_pow_eq_pow_val y₁ p).symm
    _ = ((Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F)) uu : F) := by rw [hy₁]
    _ = (Algebra.norm F (y : AdjoinRoot (X ^ p - C (π : F))) : F) := h1

end NormUnitsPow

end L20261018

#print axioms L20261018.normUnits_mem_pow_of_val_eq_zero
