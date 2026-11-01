import Hyp353
import Hyp294
import Hyp310

/-!
# R1265（S36 C 项第 8 步之一）：`2` 与 `π` 都不是立方（Capelli 的输入）

`Hyp331`／`Hyp332` 的 `hne` 需要 `kc_T (2) ≠ 0`，其唯一输入是「`2` 不是 `F` 中的立方」。
本文件在 `F = 𝔽₇((t))` 上把它落地，并顺带给出 Capelli 所需的两条 `Fact`／`Module.Finite`。

| 声明 | 内容 |
|---|---|
| **`ofPowerSeries_C_eq`** | 常数项嵌入：`ofPowerSeries (C c) = c`（于 `F`） |
| **`rho`** | ★★★★ 剩余映射 `↥𝒪[F] →+* 𝔽₇` ＝ `constantCoeff ∘ e.symm` |
| **`rho_twoO`** | `rho 2 = 2` |
| **`not_exists_cube_two`** | ★★★★★ **`2` 不是 `F` 中的立方**（`kc_T 2 ≠ 0` 的输入） |
| **`pi_irred`** | `Fact (Irreducible (X^3 - C π))`（Capelli ＋ `not_exists_cube_pi`） |
| **`pi_fin`** | `Module.Finite F (AdjoinRoot (X^3 - C π))` |

## 为什么 `b ∈ 𝒪[F]` 能白拿

由 `b³ = 2` 得 `(v b)³ = v 2 ≤ 1`（`2 ∈ 𝒪` 只需 `2 = ofPowerSeries (C 2)`），
故 `v b ≤ 1`，即 `b ∈ 𝒪` —— **不需要**知道 `v 2 = 1`（那需要"常数是单位"的额外事实）。
落到剩余域后 `2 = c₀³`（`c₀ := constantCoeff (e.symm b)`），而 `𝔽₇` 中 `2` 不是立方（`decide`）。
-/

noncomputable section

open LaurentSeries ValuativeRel IsLocalRing Polynomial
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 常数项嵌入：`ofPowerSeries (C c) = HahnSeries.C c`（于 `F`）。 -/
theorem ofPowerSeries_C_eq (c : ZMod 7) :
    ((HahnSeries.ofPowerSeries ℤ (ZMod 7)) (PowerSeries.C c) : LaurentSeries (ZMod 7))
      = HahnSeries.C c := by
  rw [HahnSeries.ofPowerSeries_C]

/-- `2 ∈ 𝒪[F]`。 -/
theorem two_mem_O : (2 : LaurentSeries (ZMod 7)) ∈ 𝒪[LaurentSeries (ZMod 7)] :=
  (mem_O_iff_exists_powerSeries _).mpr ⟨PowerSeries.C 2, by
    rw [ofPowerSeries_C_eq]
    exact (rfl : HahnSeries.C (2 : ZMod 7) = (2 : LaurentSeries (ZMod 7)))⟩

/-- `2` 作为 `↥𝒪[F]` 的元素。 -/
def twoO : ↥𝒪[LaurentSeries (ZMod 7)] := ⟨2, two_mem_O⟩

/-- ★★★★ **剩余映射** `↥𝒪[𝔽₇((t))] →+* 𝔽₇`：`constantCoeff ∘ e.symm`。

（`PowerSeries.constantCoeff` 的核是 `K⟦X⟧` 的极大理想，故 `rho` 的核是 `𝔪[F]`；
本文件只用它做**取值**，不用核。） -/
def rho : ↥𝒪[LaurentSeries (ZMod 7)] →+* ZMod 7 :=
  (PowerSeries.constantCoeff (R := ZMod 7)).comp
    (powerSeriesEquivO (K := ZMod 7)).symm.toRingHom

theorem symm_twoO : (powerSeriesEquivO (K := ZMod 7)).symm twoO = PowerSeries.C 2 := by
  have h : powerSeriesEquivO (K := ZMod 7) (PowerSeries.C 2) = twoO :=
    Subtype.ext (ofPowerSeries_C_eq 2)
  exact (powerSeriesEquivO (K := ZMod 7)).injective (by rw [RingEquiv.apply_symm_apply]; exact h.symm)

/-- ★★★★ **`rho` 在 `2` 上取值 `2`**。 -/
theorem rho_twoO : rho twoO = 2 := by
  simp [rho, symm_twoO]

/-- ★★★★★ **`2` 不是 `F = 𝔽₇((t))` 中的立方**。

设 `b³ = 2`。取 `v`：`(v b)³ = v 2 ≤ 1` ⟹ `v b ≤ 1` ⟹ `b ∈ 𝒪[F]`。
沿 `e.symm` 与 `constantCoeff` 得 `(rho b)³ = rho 2 = 2`，而 `𝔽₇` 中无立方根为 `2`（`decide`）。 -/
theorem not_exists_cube_two :
    ∀ b : LaurentSeries (ZMod 7), b ^ 3 ≠ (2 : LaurentSeries (ZMod 7)) := by
  intro b hb
  have hbO : b ∈ 𝒪[LaurentSeries (ZMod 7)] := by
    rw [mem_O_iff]
    have hv2 : (Valued.v (R := LaurentSeries (ZMod 7))) (2 : LaurentSeries (ZMod 7)) ≤ 1 := by
      have := two_mem_O
      rwa [mem_O_iff] at this
    have hp : ((Valued.v (R := LaurentSeries (ZMod 7))) b) ^ 3 ≤ 1 := by
      rw [← map_pow, hb]
      exact hv2
    by_contra hle
    rw [not_le] at hle
    exact absurd hp (not_le.mpr (by
      simpa using one_lt_pow₀ hle (by norm_num : (3 : ℕ) ≠ 0)))
  have h := congrArg rho (show (⟨b, hbO⟩ : ↥𝒪[LaurentSeries (ZMod 7)]) ^ 3 = twoO from
    Subtype.ext hb)
  rw [map_pow, rho_twoO] at h
  exact (by decide : ∀ x : ZMod 7, x ^ 3 ≠ 2) _ h

/-- ★★★★ **`X³ - C π` 不可约**（Capelli ＋ `π` 非立方）。 -/
instance pi_irred : Fact (Irreducible (X ^ 3 - C (pi : LaurentSeries (ZMod 7)))) :=
  ⟨(capelli_irreducible_iff (F := LaurentSeries (ZMod 7)) (p := 3) (by decide)).mpr
    not_exists_cube_pi⟩

/-- ★★★★ **`F(π^{1/3})` 在 `F` 上有限。 -/
instance pi_fin :
    Module.Finite (LaurentSeries (ZMod 7)) (AdjoinRoot (X ^ 3 - C (pi : LaurentSeries (ZMod 7)))) :=
  moduleFinite_adjoinRoot (p := 3) (pi : LaurentSeries (ZMod 7))

end FqXt
end L20261018

#print axioms L20261018.FqXt.not_exists_cube_two
#print axioms L20261018.FqXt.pi_irred
#print axioms L20261018.FqXt.pi_fin
