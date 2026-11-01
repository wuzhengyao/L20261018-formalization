import Hyp608

/-!
# S51 R4：`μ_p ↪ κ^×` —— 单位群里的 `p` 次单位根在剩余域中**单射**

## 0 为什么需要这一件

`wiki/hyp-ci-residue.md` §4 把 `(CI)` 的阻断拆成三项基建：

| # | 需要 | 库内现状（L46 侦察，2026-10-31） |
|---|---|---|
| 1 | `v` 延拓到 `F̄` | mathlib **只有** `Valuation.HasExtension` **谓词** ＋ `extendToLocalization`；**无代数闭包上的延拓存在性** |
| 2 | 一般 Hensel 的惯性子群 | 只有局部域版（带 `[IsNonarchimedeanLocalField]`） |
| **3** | **`μ_n ↪ κ^×` 单射（`n` 是单位）** | **本件补上（自建，纯交换代数）** |

第 3 项在每条 `(CI)` 论证里都要用：`σ ∈ I` 保持赋值且在 `κ̄` 上平凡 ⟹
`σ(u^{1/p})/u^{1/p} ∈ μ_p` 的剩余是 `1` ⟹ **须由单射性推出该比值是 `1`**。
它也是「`μ_p ⊆ F` ⟹ `μ_p ⊆ κ`」的来源（剩余侧 Kummer 类 `(ū)` 的定义前提）。

## 1 本件交付

| 声明 | 内容 |
|---|---|
| `geomSum_sub_eq` | 差商恒等式 `∑_{i<n} u^i - n = (u-1)·∑_{i<n}∑_{j<i} u^j`（纯环论，无多项式） |
| `isUnit_of_mul_left` | （局部小工具）`a*b` 是单位 ⟹ `a` 是单位 |
| **`isUnit_sub_one_of_pow_eq_one`** | ★★★★★ `u^n = 1`、`u ≠ 1`、`n` 是单位 ⟹ **`u - 1` 是单位** |
| **`residueUnits_injective_on_pow_eq_one`** | ★★★★★★★ **`μ_n ↪ κ^×` 单射** |
| `rootsOfUnityResidue_injective` | 论文口径（`𝒪[F]`） |

## 2 证明要点

记 `S := ∑_{i<n} u^i`、`D := ∑_{i<n}∑_{j<i} u^j`。两条恒等式：**望远镜** `S·(u-1) = u^n - 1 = 0`
（`geom_sum_mul`）与**差商** `S - n = (u-1)·D`。

关键一步**不需要** `S = 0`：把 `n = S - (u-1)D` 拆成「`S` 与 `(u-1)D` 之和是单位」，
由 `IsLocalRing.isUnit_or_isUnit_of_isUnit_add` 得其二为**单位**：
* 若 `(u-1)D` 是单位 ⟹ `u-1` 是单位（`isUnit_of_mul_left`）✓；
* 若 `S` 是单位，则 `S·(S-n) = 0` 给 `S = n`，代回望远镜得 `n·(u-1) = 0` ⟹ `u = 1`，与 `hne` 矛盾。

⟹ 本件**不需要** `HenselianRing`／`ValuativeRel`／完备性／拓扑来证明代数核心；
只有把 `ρ u = 1` 翻成 `u - 1 ∈ 𝔪` 时用到 `Hyp608.residue_units_eq_one_iff`（那一格需要 Hensel）。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open scoped BigOperators

namespace L20261018

section Abstract

variable (R : Type*) [CommRing R] [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)]
variable (n : ℕ) [NeZero n]

/-- **差商恒等式**（纯环论，无多项式）：`∑_{i<n} u^i - n = (u - 1) · ∑_{i<n} ∑_{j<i} u^j`。 -/
theorem geomSum_sub_eq (u : R) :
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

/-- 局部小工具：`a*b` 是单位 ⟹ `a` 是单位（交换环）。 -/
theorem isUnit_of_mul_left {a b : R} (h : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨w, hw⟩ := h
  have h1 : a * (b * ↑w⁻¹) = 1 := by
    calc a * (b * ↑w⁻¹) = (a * b) * ↑w⁻¹ := by ring
      _ = ↑w * ↑w⁻¹ := by rw [hw]
      _ = 1 := w.mul_inv
  exact ⟨⟨a, b * ↑w⁻¹, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/-- ★★★★★ `u^n = 1`、`u ≠ 1`、`n` 是单位 ⟹ `u - 1` 是单位。 -/
theorem isUnit_sub_one_of_pow_eq_one (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) (hne : u ≠ 1) :
    IsUnit (u - 1) := by
  classical
  set S := Finset.sum (Finset.range n) (fun i => u ^ i) with hS
  set D := Finset.sum (Finset.range n)
    (fun i => Finset.sum (Finset.range i) (fun j => u ^ j)) with hD
  have htel : S * (u - 1) = 0 := by
    rw [hS]
    have hgm := geom_sum_mul u n
    rw [hgm, hu, sub_self]
  have hsub : S - (n : R) = (u - 1) * D := by
    rw [hS, hD, geomSum_sub_eq]
  by_cases hD : IsUnit ((u - 1) * D)
  · exact isUnit_of_mul_left R hD
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

/-- ★★★★★★★ **`μ_n ↪ κ^×`**：单位群里的两个 `n` 次单位根若剩余相同，则它们相等。 -/
theorem residueUnits_injective_on_pow_eq_one (hn : IsUnit (n : R)) {ζ η : Rˣ}
    (hζ : (ζ : R) ^ n = 1) (hη : (η : R) ^ n = 1)
    (hres : residueUnits R ζ = residueUnits R η) : ζ = η := by
  classical
  set u : Rˣ := η⁻¹ * ζ with hu_def
  have hζu : ζ ^ n = 1 := Units.ext hζ
  have hηu : η ^ n = 1 := Units.ext hη
  have hun : u ^ n = 1 := by
    rw [hu_def, mul_pow, hζu, inv_pow, hηu, inv_one, one_mul]
  have hu : (u : R) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hun, Units.val_one]
  have hures : residueUnits R u = 1 := by
    rw [hu_def, map_mul, map_inv, hres]
    exact inv_mul_cancel _
  by_cases h1 : u = 1
  · rw [hu_def] at h1
    have : ζ = η := by
      have h2 := congrArg (fun x : Rˣ => η * x) h1
      simpa [hu_def, mul_assoc] using h2
    exact this
  · exfalso
    have hnev : (u : R) ≠ 1 := fun h => h1 (Units.ext h)
    have hunit : IsUnit ((u : R) - 1) :=
      isUnit_sub_one_of_pow_eq_one R n hn hu hnev
    have hmem : ((u : R) - 1) ∈ IsLocalRing.maximalIdeal R :=
      (residue_units_eq_one_iff R u).mp hures
    exact IsLocalRing.maximalIdeal.isMaximal R |>.ne_top
      (Ideal.eq_top_of_isUnit_mem (I := IsLocalRing.maximalIdeal R) hmem hunit)

end Abstract

/-! ## 论文口径：`𝒪[F]` 里的 `p` 次单位根在 `κ` 中单射 -/

section PaperLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  (p : ℕ) [NeZero p] [Fact p.Prime]

/-- ★★★★★ **论文口径**：`μ_p(𝒪[F]) ↪ κ^×`。`IsUnit (p : 𝒪[F])` 由 `char κ ≠ p` 供给。 -/
theorem rootsOfUnityResidue_injective (hp : IsUnit (p : ↥𝒪[F])) {ζ η : (↥𝒪[F])ˣ}
    (hζ : (ζ : ↥𝒪[F]) ^ p = 1) (hη : (η : ↥𝒪[F]) ^ p = 1)
    (hres : residueUnits ↥𝒪[F] ζ = residueUnits ↥𝒪[F] η) : ζ = η :=
  residueUnits_injective_on_pow_eq_one ↥𝒪[F] p hp hζ hη hres

end PaperLevel

end L20261018

#print axioms L20261018.geomSum_sub_eq
#print axioms L20261018.isUnit_of_mul_left
#print axioms L20261018.isUnit_sub_one_of_pow_eq_one
#print axioms L20261018.residueUnits_injective_on_pow_eq_one
#print axioms L20261018.rootsOfUnityResidue_injective
