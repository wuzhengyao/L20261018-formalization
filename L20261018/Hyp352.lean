import L20261018.Hyp351
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian

/-!
# R1263（S36 C 项第 6 步）：`𝒪[𝔽₇((t))] ≅ 𝔽₇⟦X⟧` ⟹ Hensel ＋ 有限剩余域

`PROMPT-S36` §④ 第 6 步的两条路线，本文件走**路线甲（对应）**，并把需要的东西一次拿全：

| 声明 | 内容 |
|---|---|
| **`mem_O_iff`** | `x ∈ 𝒪[K⸨X⸩] ↔ Valued.v x ≤ 1`（`valuation` 与 `Valued.v` 的桥） |
| **`val_le_one_iff_coe`** | `Valued.v x ≤ 1 ↔ x 来自幂级数`（mathlib `val_le_one_iff_eq_coe` 的转写） |
| **`powerSeriesEquivO`** | ★★★★★ **`K⟦X⟧ ≃+* ↥𝒪[K⸨X⸩]`**（`algebraMap` 的像 = 整环） |
| **`map_maximalIdeal`** | `e(𝔪 K⟦X⟧) = 𝔪 𝒪[K⸨X⸩]`（局部环的唯一极大理想） |
| **`isAdicComplete_O`** | `IsAdicComplete 𝔪[K⸨X⸩] 𝒪[K⸨X⸩]`（沿 `e` 从 `K⟦X⟧` 搬） |
| **`henselianRing_O`** | ★★★★★ **`HenselianRing ↥𝒪[F] 𝔪[F]`**（`IsAdicComplete ⟹ Hensel`） |
| **`residueEquiv`** | `𝓀[𝔽₇((t))] ≃+* 𝔽₇`（`constantCoeff ∘ e.symm`） |
| **`finite_residueField`** | ★★★★★ **`Finite 𝓀[𝔽₇((t))]`** |

## 为什么这样走（L46／L47：先查库内）

* `Valuation.integer` 的载体就是 `{x | v x ≤ 1}`（`Valuation.integer` 的定义即如此），
  故 `𝒪` 层判据只需把 `valuation` 与 `Valued.v` 的比较关系对齐 —— 两者都由
  `Valuation.Compatible`（`vle_iff_le`）给出，**无需**重新证序关系。
* `K⟦X⟧` 的完备性：`IsAdicComplete (span {X}) K⟦X⟧`（`AdicCompletion/Completeness.lean:225`），
  `maximalIdeal K⟦X⟧ = span {X}`（`PowerSeries/Inverse.lean:289`），
  沿环同构搬完备性用 `IsAdicComplete.congr_ringEquiv`（`AdicCompletion/Topology.lean:99`）。
* Hensel **不必**自建：`IsAdicComplete.henselianRing`（`Henselian.lean:170`）。
-/

noncomputable section

open LaurentSeries ValuativeRel IsLocalRing
open scoped PowerSeries

namespace L20261018
namespace FqXt

variable {K : Type*} [Field K]

/-! ### 1. 整环的元级判据 -/

/-- ★★★★ **`x` 在 `𝒪[K⸨X⸩]` 中 ⟺ `Valued.v x ≤ 1`**。

`𝒪[R]` 是 `valuation R` 的整环（载体即 `{x | valuation R x ≤ 1}`），
而 `valuation R` 与 `Valued.v` 的比较关系一致（`Valuation.Compatible.vle_iff_le` 两次）。 -/
theorem mem_O_iff (x : LaurentSeries K) :
    x ∈ 𝒪[LaurentSeries K] ↔ (Valued.v (R := LaurentSeries K)) x ≤ 1 := by
  haveI hvc : (Valued.v (R := LaurentSeries K)).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff]
  constructor
  · intro h
    have h1 : x ≤ᵥ (1 : LaurentSeries K) :=
      (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (LaurentSeries K)) x 1).mpr
        (by simpa using h)
    simpa using (Valuation.Compatible.vle_iff_le
      (v := Valued.v (R := LaurentSeries K)) x 1).mp h1
  · intro h
    have h1 : x ≤ᵥ (1 : LaurentSeries K) :=
      (Valuation.Compatible.vle_iff_le
        (v := Valued.v (R := LaurentSeries K)) x 1).mpr (by simpa using h)
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (LaurentSeries K)) x 1).mp h1

/-- ★★★★ **整环的元素恰是幂级数**（`LaurentSeries.val_le_one_iff_eq_coe` 的转写）。 -/
theorem mem_O_iff_exists_powerSeries (x : LaurentSeries K) :
    x ∈ 𝒪[LaurentSeries K] ↔ ∃ f : K⟦X⟧, (HahnSeries.ofPowerSeries ℤ K) f = x :=
  mem_O_iff x |>.trans (LaurentSeries.val_le_one_iff_eq_coe K x)

/-! ### 2. `K⟦X⟧ ≃+* 𝒪[K⸨X⸩]` -/

/-- `K⟦X⟧` 到 `𝒪[K⸨X⸩]` 的环同态（`algebraMap` 打到整环里）。 -/
def powerSeriesToO : K⟦X⟧ →+* ↥𝒪[LaurentSeries K] :=
  RingHom.codRestrict (algebraMap K⟦X⟧ K⸨X⸩) 𝒪[LaurentSeries K] fun f => by
    rw [mem_O_iff_exists_powerSeries]
    exact ⟨f, rfl⟩

theorem powerSeriesToO_coe (f : K⟦X⟧) :
    ((powerSeriesToO (K := K) f : ↥𝒪[LaurentSeries K]) : LaurentSeries K)
      = (HahnSeries.ofPowerSeries ℤ K) f := rfl

theorem powerSeriesToO_injective : Function.Injective (powerSeriesToO (K := K)) := by
  intro f g h
  have h' : (HahnSeries.ofPowerSeries ℤ K) f = (HahnSeries.ofPowerSeries ℤ K) g := by
    simpa [powerSeriesToO_coe] using congrArg Subtype.val h
  exact HahnSeries.ofPowerSeries_injective h'

theorem powerSeriesToO_surjective : Function.Surjective (powerSeriesToO (K := K)) := by
  intro x
  obtain ⟨f, hf⟩ := (mem_O_iff_exists_powerSeries (K := K) (x : LaurentSeries K)).mp x.2
  exact ⟨f, Subtype.ext (by simpa [powerSeriesToO_coe] using hf)⟩

/-- ★★★★★ **`K⟦X⟧ ≃+* ↥𝒪[K⸨X⸩]`**（路线甲的载体同一性）。 -/
def powerSeriesEquivO : K⟦X⟧ ≃+* ↥𝒪[LaurentSeries K] :=
  RingEquiv.ofBijective (powerSeriesToO (K := K))
    ⟨powerSeriesToO_injective, powerSeriesToO_surjective⟩

@[simp]
theorem powerSeriesEquivO_apply (f : K⟦X⟧) :
    ((powerSeriesEquivO (K := K) f : ↥𝒪[LaurentSeries K]) : LaurentSeries K)
      = (HahnSeries.ofPowerSeries ℤ K) f := rfl

/-! ### 3. 极大理想的对应 -/

/-- ★★★★ **极大理想沿 `e` 对应**（局部环的唯一极大理想）。 -/
theorem map_maximalIdeal :
    Ideal.map (powerSeriesEquivO (K := K)) (IsLocalRing.maximalIdeal K⟦X⟧)
      = IsLocalRing.maximalIdeal ↥𝒪[LaurentSeries K] :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.IsMaximal.map_bijective (powerSeriesEquivO (K := K)) (powerSeriesEquivO (K := K)).bijective
      (IsLocalRing.maximalIdeal.isMaximal _))

/-! ### 4. 完备性与 Hensel -/

/-- ★★★★★ **`𝒪[K⸨X⸩]` 在极大理想处 adic 完备**（从 `K⟦X⟧` 沿 `e` 搬）。 -/
instance isAdicComplete_O :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥𝒪[LaurentSeries K])
      ↥𝒪[LaurentSeries K] := by
  have h := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal K⟦X⟧)
    (powerSeriesEquivO (K := K))).mpr (by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance)
  rwa [map_maximalIdeal] at h

/-- ★★★★★ **`𝒪[𝔽₇((t))]` 是 Hensel 环**（论文第 4 章的核心假设之一）。 -/
instance henselianRing_O :
    HenselianRing ↥𝒪[LaurentSeries K] (IsLocalRing.maximalIdeal ↥𝒪[LaurentSeries K]) :=
  IsAdicComplete.henselianRing _ _

end FqXt

/-! ### 5. 剩余域 `𝓀[𝔽₇((t))] ≅ 𝔽₇` -/

namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- ★★★★★ **剩余域 `𝓀[𝔽₇((t))] ≃+* 𝔽₇`**。

三步：`𝓀[𝒪] = ↥𝒪 ⧸ 𝔪 ≃ K⟦X⟧ ⧸ 𝔪`（沿 `powerSeriesEquivO`，用 `map_maximalIdeal`）、
`≃ K⟦X⟧ ⧸ ker constantCoeff`（`ker_coeff_eq_max_ideal`）、`≃ 𝔽₇`（`constantCoeff` 满射）。 -/
def residueEquiv : IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)] ≃+* ZMod 7 :=
  ((Ideal.quotientEquiv (IsLocalRing.maximalIdeal (ZMod 7)⟦X⟧)
      (IsLocalRing.maximalIdeal ↥𝒪[LaurentSeries (ZMod 7)])
      (powerSeriesEquivO (K := ZMod 7))
      (map_maximalIdeal (K := ZMod 7)).symm).symm.trans
    (Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal (k := ZMod 7)).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (PowerSeries.constantCoeff_surj (R := ZMod 7)))

/-- ★★★★★ **`𝔽₇((t))` 的剩余域有限**（`Hyp321`／`Hyp332` 所需的 `[Finite (ResidueField)]`）。 -/
instance finite_residueField :
    Finite (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)]) :=
  Finite.of_equiv _ (residueEquiv).symm.toEquiv

end FqXt
end L20261018

#print axioms L20261018.FqXt.mem_O_iff
#print axioms L20261018.FqXt.powerSeriesEquivO
#print axioms L20261018.FqXt.map_maximalIdeal
#print axioms L20261018.FqXt.isAdicComplete_O
#print axioms L20261018.FqXt.henselianRing_O
#print axioms L20261018.FqXt.residueEquiv
#print axioms L20261018.FqXt.finite_residueField
