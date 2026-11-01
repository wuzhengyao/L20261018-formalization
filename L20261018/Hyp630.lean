import Hyp629

/-!
# S52 R22：**N4 的算术核心** —— 惯性群固定单位在 `F̄` 中的 `p` 次根（**免 Hensel**）

## 0 本件在路线上的位置

`PROMPT-S52` §1.2 的 **N4**：`u ∈ 𝒪[F]ˣ ⟹ kummerClass u` 在 `I` 上为 0。
数学（`PROMPT-S52` §1.2 已写死）：

```
u 是单位 ⟹ α^p = u 给 W α = 1（Hyp619 引擎）
⟹ ᾱ ∈ κ̄^× 且 σ ∈ I 固定 ᾱ
⟹ σ(α)/α ∈ μ_p 的剩余是 1 ⟹ 由 μ_p ↪ κ̄^× 得 σ(α) = α ⟹ res_I = 0
```

本件把这条链**机检到 `σ α = α`** 为止（点值层）。Kummer 类层的包装（`H¹(I, μ_p)` 的 restrict／
`infl` 表述）是下一步，**本件不声称**已做。

## 1 两件交付

| 段 | 内容 |
|---|---|
| **(甲)** `val_root_eq_one` | ★★★★★★ **`α^p = u`、`W u = 1` ⟹ `W α = 1`**（`Valuation` 层的 `ν(u^{1/p}) = 0`）。这**正是 `Hyp620` 登记未做**的那一条（`val_algMap_eq_one`／端到端 `val_root_eq_one`） |
| **(乙)** `inertia_fixes_pow_root` | ★★★★★★★ **N4 核心**：`σ ∈ I`、`α^p = u`、`W u = 1` ⟹ **`σ α = α`** |

## 2 数学（四步）

1. **（甲）**`W(α)^p = W(α^p) = W u = 1` ⟹ `W α = 1`（值群 `Multiplicative ℚ` 无挠，`Hyp619.unitVal_root_eq_one`；
   经 `Hyp620.unitValOf` 与 `u ↦ u` 的单位化把 `WithZero` 层降到群层）。
   ⟹ `α` 与 `α⁻¹` 都在 `𝒪_W` 里 ⟹ `A := ⟨α⟩` 是 `𝒪_W` 的**单位**。
2. `σ ∈ I` ⟹ `σ` 在 `κ̄` 上平凡 ⟹ `residue (σ A) = residue A`（`Hyp625.mem_inertia_iff_residue_eq`）。
3. `(σ α)^p = σ(α^p) = σ(u) = u = α^p` ⟹ `U^p = A^p`（`U := subringAct σ A`，用 `Hyp627.subringAct`）。
4. `μ_p ↪ κ̄^×` 的**比值形态**：`(U A⁻¹)^p = 1` ＋ `residue (U A⁻¹) = 1` ⟹ `U A⁻¹ = 1` ⟹ `U = A` ⟹ `σ α = α`。

## 3 ★★ 本件的一个**类型层发现**：`Hyp613` 的 `[HenselianRing]` 是**多余的**

`Hyp613` 的 `isUnit_sub_one_of_pow_eq_one`／`residueUnits_injective_on_pow_eq_one` 的
`#check` 签名里带 `[HenselianRing R (maximalIdeal R)]`，而 `Hyp613` 文件头写的是
「（`[CommRing R] [IsLocalRing R]`，无需 Hensel）」。**逐行核过：证明只用**
`geom_sum_mul`（纯环论）＋ `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`（局部环，无 Hensel），
`[HenselianRing]` 从未被用到——它是 section 变量的**自动包含**（同一 `section` 里所有 `variable` 一并进签名）。

⟹ 本件把需要的部分**重写为免 Hensel 版**（`geomSum_sub_eq'`／`isUnit_of_mul_left'`／
`isUnit_sub_one_of_pow_eq_one'`／`eq_one_of_pow_eq_one_of_residue_eq_one`），
于 `R = ↥W.valuationSubring`（**未必 Hensel**）处可用。
⚠ **不**改 `Hyp613`（它会牵动 `Hyp615`／`Hyp617`／整条档 ⑥ 的签名）；登记为「类型可收窄」的余量。

## 4 诚实边界

* **未做**：Kummer 类层的 `res_I(kummerClass u) = 0`（要 `H¹`／restriction 的包装；本件只到点值 `σ α = α`）。
* **未做**：把 `u ∈ 𝒪[F]ˣ` 搬成 `W (algebraMap u) = 1`（需 `FbarValuationHyp₄` 的 `𝒪_W = 𝒪bar`；
  本件以 `hu : W u = 1` 为假设，正是那一步的**结论形态**）。
* **未做**：`IsUnit (p : ↥𝒪_W)` 由 `IsUnit (p : ↥𝒪[F])` 导出（本件作为假设 `hpun`）。
* 本件**不动** `(CI)`／`FbarValuationHyp₄`；**不增覆盖率**（`(R2)` 仍 `∅-open`）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

/-! ### 0 免 Hensel 的重写（见文件头 §3） -/

section HenselFree

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (n : ℕ) [NeZero n]

/-- 差商恒等式（纯环论；`Hyp613.geomSum_sub_eq` 的免 Hensel 版）。 -/
theorem geomSum_sub_eq' (u : R) :
    Finset.sum (Finset.range n) (fun i => u ^ i) - (n : R)
      = (u - 1) * Finset.sum (Finset.range n)
          (fun i => Finset.sum (Finset.range i) (fun j => u ^ j)) := by
  have h1 : Finset.sum (Finset.range n) (fun i => u ^ i) - (n : R)
      = Finset.sum (Finset.range n) (fun i => (u ^ i - 1)) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    simp [Finset.sum_const]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (u - 1), geom_sum_mul]

/-- `a*b` 是单位 ⟹ `a` 是单位（交换环；`Hyp613.isUnit_of_mul_left` 的免 Hensel 版）。 -/
theorem isUnit_of_mul_left' {a b : R} (h : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨w, hw⟩ := h
  have h1 : a * (b * ↑w⁻¹) = 1 := by
    calc a * (b * ↑w⁻¹) = (a * b) * ↑w⁻¹ := by ring
      _ = ↑w * ↑w⁻¹ := by rw [hw]
      _ = 1 := w.mul_inv
  exact ⟨⟨a, b * ↑w⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- `u^n = 1`、`u ≠ 1`、`n` 是单位 ⟹ `u - 1` 是单位（免 Hensel 版）。 -/
theorem isUnit_sub_one_of_pow_eq_one' (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1)
    (hne : u ≠ 1) : IsUnit (u - 1) := by
  classical
  set S := Finset.sum (Finset.range n) (fun i => u ^ i) with hS
  set D := Finset.sum (Finset.range n)
    (fun i => Finset.sum (Finset.range i) (fun j => u ^ j)) with hD
  have htel : S * (u - 1) = 0 := by
    rw [hS]
    have hgm := geom_sum_mul u n
    rw [hgm, hu, sub_self]
  have hsub : S - (n : R) = (u - 1) * D := by
    rw [hS, hD, geomSum_sub_eq']
  by_cases hD : IsUnit ((u - 1) * D)
  · exact isUnit_of_mul_left' R hD
  · exfalso
    have hSunit : IsUnit S := by
      by_contra hcon
      have hsum : IsUnit (S + (-((u - 1) * D))) := by
        have heq : S + (-((u - 1) * D)) = (n : R) := by rw [← hsub]; ring
        rw [heq]; exact hn
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
      · exact hcon h
      · exact hD (by simpa using h.neg)
    have hzero : u - 1 = 0 := by
      obtain ⟨w, hw⟩ := hSunit
      have h := htel
      rw [← hw] at h
      have heq : u - 1 = ↑w⁻¹ * (↑w * (u - 1)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      rw [heq, h, mul_zero]
    exact hne (sub_eq_zero.mp hzero)

/-- ★★★★★★ **`μ_n ↪ κ^×` 的「比值形态」（免 Hensel）**：`ζ` 是 `n` 次单位根且剩余为 `1` ⟹ `ζ = 1`。 -/
theorem eq_one_of_pow_eq_one_of_residueUnits_eq_one (hn : IsUnit (n : R)) {ζ : Rˣ}
    (hpow : ((ζ : R)) ^ n = 1) (hres : residueUnits R ζ = 1) : ζ = 1 := by
  by_contra hne
  have hnev : ((ζ : R)) ≠ 1 := fun h => hne (Units.ext h)
  have hunit : IsUnit ((ζ : R) - 1) := isUnit_sub_one_of_pow_eq_one' R n hn hpow hnev
  -- `residue (ζ : R) = 1` ⟹ `ζ - 1 ∈ 𝔪`
  have hres' : IsLocalRing.residue R ((ζ : R)) = 1 := by
    have h := congrArg (fun x : (IsLocalRing.ResidueField R)ˣ => (x : IsLocalRing.ResidueField R)) hres
    simpa [residueUnits, Units.coe_map] using h
  have hmem : ((ζ : R) - 1) ∈ IsLocalRing.maximalIdeal R := by
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub, hres', map_one, sub_self]
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.eq_top_of_isUnit_mem (I := IsLocalRing.maximalIdeal R) hmem hunit)

end HenselFree

/-! ### 甲：`Valuation` 层的 `ν(u^{1/p}) = 0`（`Hyp620` 登记的缺口） -/

section ValRoot

variable {F : Type} [Field F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))

/-- ★★★★★★ **`α^p = u`、`W u = 1` ⟹ `W α = 1`**（`Hyp620` 登记的 `val_root_eq_one`）。 -/
theorem val_root_eq_one {p : ℕ} (hp : p ≠ 0) {α : SeparableClosure F} {u : F}
    (hα : α ^ p = algebraMap F (SeparableClosure F) u)
    (hu : W (algebraMap F (SeparableClosure F) u) = 1) :
    W α = 1 := by
  have hu0 : algebraMap F (SeparableClosure F) u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_pow hp] at hα; exact hu0 hα.symm
  set ū : (SeparableClosure F)ˣ := Units.mk0 _ hu0 with hū
  set ā : (SeparableClosure F)ˣ := Units.mk0 α hα0 with hā
  have hαu : ā ^ p = ū := by
    refine Units.ext ?_
    show (ā : SeparableClosure F) ^ p = (ū : SeparableClosure F)
    rw [hā, hū]
    simpa using hα
  have hw : unitValOf W ā = 1 := by
    refine unitVal_root_eq_one hp (unitValOf W) hαu ?_
    rw [unitValOf_eq_one_iff, hū]
    simpa using hu
  have hWā : W (ā : SeparableClosure F) = 1 := (unitValOf_eq_one_iff W ā).mp hw
  simpa [hā] using hWā

end ValRoot

/-! ### 乙：**N4 核心** —— 惯性群固定 `p` 次根 -/

section InertiaRoot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  (W : Valuation (SeparableClosure F) (WithZero (Multiplicative ℚ)))
  (hval : ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (y : SeparableClosure F),
    W (σ y) = W y)

include hval in
/-- ★★★★★★★ **N4 的算术核心**：`σ ∈ I` 固定 `u` 在 `F̄` 中的 `p` 次根
（`u ∈ F`，`W u = 1` 即 `u` 是赋值单位）。

**免 Hensel**：只用 `𝒪_W` 是局部环（`IsLocalRing`）＋ 值保持。 -/
theorem inertia_fixes_pow_root {p : ℕ} (hp : p ≠ 0) (hpun : IsUnit (p : ↥W.valuationSubring))
    {α : SeparableClosure F} {u : F}
    (hα : α ^ p = algebraMap F (SeparableClosure F) u)
    (hu : W (algebraMap F (SeparableClosure F) u) = 1)
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (hσ : σ ∈ inertia W hval) :
    σ α = α := by
  haveI : NeZero p := ⟨hp⟩
  have hWα : W α = 1 := val_root_eq_one W hp hα hu
  have hu0 : algebraMap F (SeparableClosure F) u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_pow hp] at hα; exact hu0 hα.symm
  have hmemA : α ∈ W.valuationSubring := by
    change W α ≤ 1
    rw [hWα]
  have hmemAinv : α⁻¹ ∈ W.valuationSubring := by
    change W α⁻¹ ≤ 1
    rw [map_inv₀, hWα]
    simp
  set A : ↥W.valuationSubring := ⟨α, hmemA⟩ with hA
  set Ainv : ↥W.valuationSubring := ⟨α⁻¹, hmemAinv⟩ with hAinv
  have hmul : A * Ainv = 1 := by
    refine Subtype.ext ?_
    show α * α⁻¹ = (1 : SeparableClosure F)
    exact mul_inv_cancel₀ hα0
  have hmul' : Ainv * A = 1 := by
    refine Subtype.ext ?_
    show α⁻¹ * α = (1 : SeparableClosure F)
    exact inv_mul_cancel₀ hα0
  set Aunit : (↥W.valuationSubring)ˣ := Units.mk A Ainv hmul hmul' with hAunit
  set U : (↥W.valuationSubring)ˣ :=
    Units.map (subringAct W hval σ).toMonoidHom Aunit with hU
  have hUcoe : (U : ↥W.valuationSubring) = subringAct W hval σ A := rfl
  -- 幂相等：`(σ α)^p = α^p`
  have hpow : ((U : ↥W.valuationSubring)) ^ p = ((Aunit : ↥W.valuationSubring)) ^ p := by
    rw [hUcoe, hAunit, Units.val_mk, hA]
    refine Subtype.ext ?_
    show (subringAct W hval σ ⟨α, hmemA⟩ : SeparableClosure F) ^ p = α ^ p
    rw [subringAct_coe]
    show σ α ^ p = α ^ p
    rw [← map_pow, hα, AlgEquiv.commutes]
  -- 剩余相等：`σ ∈ I` 在 `κ̄` 上平凡
  have hres : residueUnits (↥W.valuationSubring) U
      = residueUnits (↥W.valuationSubring) Aunit := by
    refine Units.ext ?_
    show IsLocalRing.residue (↥W.valuationSubring) (U : ↥W.valuationSubring)
      = IsLocalRing.residue (↥W.valuationSubring) (Aunit : ↥W.valuationSubring)
    rw [hUcoe, hAunit, Units.val_mk, hA]
    exact (mem_inertia_iff_residue_eq W hval σ).mp hσ ⟨α, hmemA⟩
  -- 比值 `U * Aunit⁻¹` 是单位根且剩余为 1
  have hpowU : U ^ p = Aunit ^ p := Units.ext hpow
  have hζpow_units : (U * Aunit⁻¹) ^ p = 1 := by
    rw [mul_pow, hpowU, inv_pow]
    exact mul_inv_cancel _
  have hζpow : (((U * Aunit⁻¹ : (↥W.valuationSubring)ˣ) : ↥W.valuationSubring)) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζpow_units, Units.val_one]
  have hζres : residueUnits (↥W.valuationSubring) (U * Aunit⁻¹) = 1 := by
    rw [map_mul, map_inv, hres]
    exact mul_inv_cancel _
  have hζ : U * Aunit⁻¹ = 1 :=
    eq_one_of_pow_eq_one_of_residueUnits_eq_one (↥W.valuationSubring) p hpun hζpow hζres
  have hUA : U = Aunit := by
    have h := congrArg (fun x => x * Aunit) hζ
    simpa [mul_assoc] using h
  have hfin : (U : ↥W.valuationSubring) = (Aunit : ↥W.valuationSubring) := by rw [hUA]
  have hval : (U : ↥W.valuationSubring) = (Aunit : ↥W.valuationSubring) := hfin
  have h2 : ((U : ↥W.valuationSubring) : SeparableClosure F)
      = ((Aunit : ↥W.valuationSubring) : SeparableClosure F) := by rw [hval]
  rw [hUcoe, subringAct_coe] at h2
  simpa [hAunit, Units.val_mk, hA] using h2

end InertiaRoot

end L20261018

#print axioms L20261018.geomSum_sub_eq'
#print axioms L20261018.isUnit_sub_one_of_pow_eq_one'
#print axioms L20261018.eq_one_of_pow_eq_one_of_residueUnits_eq_one
#print axioms L20261018.val_root_eq_one
#print axioms L20261018.inertia_fixes_pow_root
