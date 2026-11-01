import L20261018.Hyp352
import L20261018.Hyp308
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# R1264（S36 C 项第 7 步）：`𝒪[𝔽₇((t))]` 是 DVR、`v`／`ValCompat`、`π = X`

`PROMPT-S36` §④ 第 7 步。本文件把 `Hyp306`／`Hyp307`／`Hyp309` 的 DVR 机械
（`zval`／`vCompatHom`／`valCompat_of_dvr`／`exists_uniformizer_not_pow`）**接到函数域例子**上。

| 声明 | 内容 |
|---|---|
| **`isDiscreteValuationRing_O`** | ★★★★★ `IsDiscreteValuationRing ↥𝒪[K⸨X⸩]`（沿 `powerSeriesEquivO` 从 `K⟦X⟧` 搬） |
| **`pi`** | 一致化元 `π := X`（`Units.mk0 (ofPowerSeries X)`） |
| **`pi_val`** | `Valued.v π = exp (-1)`（`LaurentSeries.valuation_X_pow`） |
| **`maximalIdeal_O_eq_span_pi`** | `𝔪[F] = span {π}`（`X` 是一致化元） |
| **`irreducible_pi`** | `Irreducible π`（`↥𝒪[F]` 中） |
| **`zval_pi`** | `zval π = 1` |
| **`pi_hπ`** | ★★★★★ `vCompatHom π = Multiplicative.ofAdd 1` |
| **`valCompat_O`** | ★★★★★ `ValCompat (vCompatHom)`（`Hyp307.valCompat_of_dvr` 的实例化） |
| **`three_isUnit_O`** | `IsUnit (3 : ↥𝒪[F])`（论文的 `hp`） |
| **`not_exists_cube_pi`** | ★★★★ **`π` 不是 `F` 中的立方**（Capelli 的输入） |

## 为什么 `π = X`（而非 `exists_uniformizer_not_pow`）

`exists_uniformizer_not_pow` 需要 `[IsDiscreteValuationRing ↥𝒪[F]]` 并走 `Classical.choose`，
其产出是 **opaque** 的（S35 教训 14：`Classical.choose` 出的结构不 defeq 于规范对象）。
本文件直接取 `π = X`：`v X = 1` 由 `valuation_X_pow` 给出，`X` 不可约由
`𝔪 = span{X}` 给出（`maximalIdeal_eq_span_X` 沿 `e` 搬），后者又直接给出 `zval π = 1`。
-/

noncomputable section

open LaurentSeries ValuativeRel IsLocalRing
open scoped PowerSeries

namespace L20261018
namespace FqXt

variable {K : Type*} [Field K]

/-! ### 1. `↥𝒪[K⸨X⸩]` 是离散赋值环 -/

/-- `↥𝒪[K⸨X⸩]` 是主理想整环（沿 `powerSeriesEquivO` 从 `K⟦X⟧` 搬）。 -/
instance isPrincipalIdealRing_O : IsPrincipalIdealRing ↥𝒪[LaurentSeries K] :=
  IsPrincipalIdealRing.of_surjective (S := ↥𝒪[LaurentSeries K])
    (powerSeriesEquivO (K := K)).toRingHom
    (fun x => ⟨(powerSeriesEquivO (K := K)).symm x,
      (powerSeriesEquivO (K := K)).apply_symm_apply x⟩)

/-- ★★★★★ **`↥𝒪[K⸨X⸩]` 是离散赋值环**（论文第 4 章的 `[IsDiscreteValuationRing ↥𝒪[F]]`）。 -/
instance isDiscreteValuationRing_O : IsDiscreteValuationRing ↥𝒪[LaurentSeries K] where
  isUnit_or_isUnit_of_add_one := by
    intro a b hab
    have h : (powerSeriesEquivO (K := K)).symm a + (powerSeriesEquivO (K := K)).symm b = 1 := by
      rw [← map_add, hab, map_one]
    rcases isUnit_or_isUnit_of_add_one h with h' | h'
    · exact Or.inl (by simpa using IsUnit.map (powerSeriesEquivO (K := K)).toRingHom h')
    · exact Or.inr (by simpa using IsUnit.map (powerSeriesEquivO (K := K)).toRingHom h')
  not_a_field' := by
    intro hbot
    have h𝔪 : IsLocalRing.maximalIdeal K⟦X⟧ = ⊥ := by
      have h' : Ideal.map (powerSeriesEquivO (K := K)) (IsLocalRing.maximalIdeal K⟦X⟧) = ⊥ := by
        rw [map_maximalIdeal, hbot]
      exact (Ideal.map_eq_bot_iff_of_injective (powerSeriesEquivO (K := K)).injective).mp h'
    rw [PowerSeries.maximalIdeal_eq_span_X] at h𝔪
    exact PowerSeries.X_ne_zero (Ideal.span_singleton_eq_bot.mp h𝔪)

/-! ### 2. `π := X` -/

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `X` 在 `F = 𝔽₇((t))` 中非零。 -/
theorem ofPowerSeries_X_ne_zero :
    ((HahnSeries.ofPowerSeries ℤ (ZMod 7)) (PowerSeries.X : (ZMod 7)⟦X⟧) : LaurentSeries (ZMod 7))
      ≠ 0 := by
  intro h
  have h' : (HahnSeries.ofPowerSeries ℤ (ZMod 7)) (PowerSeries.X : (ZMod 7)⟦X⟧)
      = (HahnSeries.ofPowerSeries ℤ (ZMod 7)) 0 := by
    rw [map_zero]; exact h
  exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective h')

/-- ★★★★★ **一致化元 `π := X`**（`ℚ_[7]` 的 `q7Pi` 的函数域对应物）。 -/
def pi : (LaurentSeries (ZMod 7))ˣ :=
  Units.mk0 ((HahnSeries.ofPowerSeries ℤ (ZMod 7)) (PowerSeries.X : (ZMod 7)⟦X⟧))
    ofPowerSeries_X_ne_zero

/-- ★★★★ **`v π = exp (-1)`**（`X`-进赋值在 `X` 上取 `-1`）。 -/
theorem pi_val : (Valued.v (R := LaurentSeries (ZMod 7))) (pi : LaurentSeries (ZMod 7))
    = WithZero.exp (-(1 : ℤ)) := by
  have h := LaurentSeries.valuation_X_pow (ZMod 7) 1
  simpa [pi, LaurentSeries.coe_algebraMap] using h

/-- `π ∈ 𝒪[F]`。 -/
theorem pi_mem_O : (pi : LaurentSeries (ZMod 7)) ∈ 𝒪[LaurentSeries (ZMod 7)] :=
  (mem_O_iff_exists_powerSeries _).mpr ⟨PowerSeries.X, rfl⟩

/-- `π` 作为 `↥𝒪[F]` 的元素。 -/
def piO : ↥𝒪[LaurentSeries (ZMod 7)] := ⟨(pi : LaurentSeries (ZMod 7)), pi_mem_O⟩

/-- ★★★★ **`𝔪[F] = span {π}`**（`X` 是一致化元）。 -/
theorem maximalIdeal_O_eq_span_pi :
    IsLocalRing.maximalIdeal ↥𝒪[LaurentSeries (ZMod 7)] = Ideal.span {piO} := by
  rw [← map_maximalIdeal (K := ZMod 7), PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span,
    Set.image_singleton]
  congr 1

/-- ★★★★ **`π` 不可约**。 -/
theorem irreducible_piO : Irreducible (piO) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer (piO)).mpr
    maximalIdeal_O_eq_span_pi

/-- ★★★★★ **`zval π = 1`**。 -/
theorem zval_pi : zval (F := LaurentSeries (ZMod 7)) pi = 1 := by
  have h := zval_uniformizer (F := LaurentSeries (ZMod 7)) (π := piO)
    (irreducible_piO)
  simpa [piO, pi] using h

/-- ★★★★★ **`v π = ofAdd 1`**（论文的 `hπ`）。 -/
theorem pi_hπ :
    vCompatHom (F := LaurentSeries (ZMod 7)) pi = Multiplicative.ofAdd (1 : ℤ) := by
  rw [show vCompatHom (F := LaurentSeries (ZMod 7)) pi
    = Multiplicative.ofAdd (zval (F := LaurentSeries (ZMod 7)) pi) from rfl, zval_pi]

/-- ★★★★★ **`ValCompat (vCompatHom)`** 在函数域例子上的实例化。 -/
theorem valCompat_O : ValCompat (F := LaurentSeries (ZMod 7))
    (vCompatHom (F := LaurentSeries (ZMod 7))) :=
  valCompat_of_dvr (F := LaurentSeries (ZMod 7))

/-! ### 3. `3` 在 `↥𝒪[F]` 中可逆，`π` 不是立方 -/

/-- ★★★★ **`IsUnit (3 : ↥𝒪[F])`**（论文的 `hp`）。 -/
theorem three_isUnit_O : IsUnit (3 : ↥𝒪[LaurentSeries (ZMod 7)]) := by
  have h2 : powerSeriesEquivO (K := ZMod 7) (PowerSeries.C (3 : ZMod 7))
      = (3 : ↥𝒪[LaurentSeries (ZMod 7)]) := by
    refine Subtype.ext ?_
    rw [powerSeriesEquivO_apply, HahnSeries.ofPowerSeries_C]
    rfl
  have h : (powerSeriesEquivO (K := ZMod 7)).symm (3 : ↥𝒪[LaurentSeries (ZMod 7)])
      = PowerSeries.C (3 : ZMod 7) :=
    (powerSeriesEquivO (K := ZMod 7)).injective (by rw [RingEquiv.apply_symm_apply]; exact h2.symm)
  have hunit : IsUnit ((powerSeriesEquivO (K := ZMod 7)).symm
      (3 : ↥𝒪[LaurentSeries (ZMod 7)])) := by
    rw [h, PowerSeries.isUnit_iff_constantCoeff]
    simpa using (isUnit_iff_ne_zero.mpr (by decide : (3 : ZMod 7) ≠ 0))
  simpa using IsUnit.map (powerSeriesEquivO (K := ZMod 7)).toRingHom hunit

/-- ★★★★★ **`π` 不是 `F` 中的立方**（Capelli 判据的输入：`X³ - C π` 不可约）。

若 `b³ = π` 则取 `v`：`v b` 是 `ℤᵐ⁰` 中的非零元，故 `v b = ofAdd m`，
于是 `3m = -1`，与 `m ∈ ℤ` 矛盾。 -/
theorem not_exists_cube_pi :
    ∀ b : LaurentSeries (ZMod 7), b ^ 3 ≠ (pi : LaurentSeries (ZMod 7)) := by
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by decide : 3 ≠ 0)] at hb
    exact ofPowerSeries_X_ne_zero hb.symm
  have hval : ((Valued.v (R := LaurentSeries (ZMod 7))) b) ^ 3
      = (Valued.v (R := LaurentSeries (ZMod 7))) (pi : LaurentSeries (ZMod 7)) := by
    rw [← map_pow, hb]
  rw [pi_val] at hval
  have hne : (Valued.v (R := LaurentSeries (ZMod 7))) b ≠ 0 := by
    simpa using hb0
  obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (Valued.v (R := LaurentSeries (ZMod 7))) b = ↑m := by
    rcases hv : (Valued.v (R := LaurentSeries (ZMod 7))) b with _ | m
    · exact absurd hv hne
    · exact ⟨m, rfl⟩
  rw [hm, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_pow, WithZero.coe_inj] at hval
  have h3 : (3 : ℤ) * Multiplicative.toAdd m = -1 := by
    have := congrArg Multiplicative.toAdd hval
    simpa using this
  omega

end FqXt
end L20261018

#print axioms L20261018.FqXt.isDiscreteValuationRing_O
#print axioms L20261018.FqXt.pi_val
#print axioms L20261018.FqXt.maximalIdeal_O_eq_span_pi
#print axioms L20261018.FqXt.pi_hπ
#print axioms L20261018.FqXt.valCompat_O
#print axioms L20261018.FqXt.three_isUnit_O
#print axioms L20261018.FqXt.not_exists_cube_pi
