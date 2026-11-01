import L20261018.Witness.Step020_f7_mu3_primitive_root
import Mathlib.RingTheory.LaurentSeries

/-!
# R1262（S36 C 项第 5 步）：把 `μ₃` 从 `𝔽₇` 搬到 `𝔽₇((t))`

`Hyp350` 已在 `𝔽₇` 上给出 `IsPrimitiveRoot (2 : ZMod 7) 3` 与 `HasEnoughRootsOfUnity (ZMod 7) 3`。
本轮把它们沿**常数嵌入** `HahnSeries.C : K →+* K⸨X⸩`（`LaurentSeries K = HahnSeries ℤ K`）
搬到函数域 `F = 𝔽₇((t))`：

* `isPrimitiveRoot_C_two` —— `IsPrimitiveRoot (HahnSeries.C 2) 3`（`IsPrimitiveRoot.map_of_injective`）；
* `hasEnoughRootsOfUnity_laurentSeries_zmod7_three` —— `HasEnoughRootsOfUnity F 3`
  （`cyc` 半由 mathlib 的**一般**结果 `rootsOfUnity.isCyclic (R) (k)` 直接给：
  `[CommRing R] [IsDomain R] [NeZero k]`，**不**需要 `R` 是有限域）。

⟹ 论文假设 `μ_p ⊂ F`（`p = 3`）在函数域例子 `𝔽₇((t))` 上落地。`char F = 7 ≠ 3` 由 `ZMod 7` 保证。
-/

noncomputable section

open LaurentSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 常数嵌入 `𝔽₇ → 𝔽₇((t))` 是**单射**环同态（`HahnSeries.C_injective`）。 -/
theorem C_injective_zmod7 :
    Function.Injective (HahnSeries.C : ZMod 7 →+* LaurentSeries (ZMod 7)) :=
  HahnSeries.C_injective

/-- ★★★★ **`2` 在 `𝔽₇((t))` 中仍是三次本原单位根**（沿常数嵌入搬运）。 -/
theorem isPrimitiveRoot_C_two :
    IsPrimitiveRoot (HahnSeries.C (2 : ZMod 7) : LaurentSeries (ZMod 7)) 3 :=
  isPrimitiveRoot_two_zmod7.map_of_injective HahnSeries.C_injective

/-- ★★★★★ **`𝔽₇((t))` 含三次本原单位根**（论文假设 `μ_p ⊂ F` 的函数域见证）。 -/
instance hasEnoughRootsOfUnity_laurentSeries_zmod7_three :
    HasEnoughRootsOfUnity (LaurentSeries (ZMod 7)) 3 where
  prim := ⟨_, isPrimitiveRoot_C_two⟩
  cyc := rootsOfUnity.isCyclic (LaurentSeries (ZMod 7)) 3

/-- 自检：`char 𝔽₇((t)) = 7`，故 `3 ≠ 0`（论文要求 `char K ≠ p`，`p = 3`）。 -/
theorem three_ne_zero_laurentSeries : (3 : LaurentSeries (ZMod 7)) ≠ 0 := by
  intro h0
  have e : (3 : LaurentSeries (ZMod 7)) = HahnSeries.C (3 : ZMod 7) := rfl
  rw [e] at h0
  exact (by decide : (3 : ZMod 7) ≠ 0) (HahnSeries.C_injective (by rw [h0]; exact (map_zero _).symm))

/-- ★★★ **`3` 在 `𝔽₇((t))` 中可逆**（`three_isUnit_F` 的函数域对应物）。 -/
theorem three_isUnit_laurentSeries : IsUnit (3 : LaurentSeries (ZMod 7)) :=
  isUnit_iff_ne_zero.mpr three_ne_zero_laurentSeries

end FqXt
end L20261018

#print axioms L20261018.FqXt.isPrimitiveRoot_C_two
#print axioms L20261018.FqXt.hasEnoughRootsOfUnity_laurentSeries_zmod7_three
