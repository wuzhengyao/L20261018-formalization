import L20261018.Witness.Step019_f7_two_order_three
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# R1261（S35 C 项第 4 步）：`𝔽₇` 的 `μ₃` 与本原根组装

用 `Hyp349` 的三条算术事实组装 `IsPrimitiveRoot (2 : ZMod 7) 3`
（`dvd_of_pow_eq_one` 靠 `l % 3` 分类），再给 `HasEnoughRootsOfUnity (ZMod 7) 3`
（`cyc` 半 = `rootsOfUnity.isCyclic (ZMod 7) 3`，注意它是**函数**）。
-/

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- ★★★★ **`2` 是 `𝔽₇` 的三次本原单位根**。 -/
theorem isPrimitiveRoot_two_zmod7 : IsPrimitiveRoot (2 : ZMod 7) 3 where
  pow_eq_one := two_pow_three_zmod7
  dvd_of_pow_eq_one := by
    intro l hl
    have hmod : (2 : ZMod 7) ^ (l % 3) = 1 := by
      have hdecomp : l = 3 * (l / 3) + l % 3 := by omega
      rw [hdecomp, pow_add, pow_mul, two_pow_three_zmod7, one_pow, one_mul] at hl
      exact hl
    have hlt : l % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases h : l % 3
    · exact Nat.dvd_of_mod_eq_zero h
    · exact absurd hmod two_ne_one_zmod7
    · exact absurd hmod two_sq_ne_one_zmod7

/-- ★★★★ **`𝔽₇` 含三次本原单位根**。 -/
instance hasEnoughRootsOfUnity_zmod7_three : HasEnoughRootsOfUnity (ZMod 7) 3 where
  prim := ⟨2, isPrimitiveRoot_two_zmod7⟩
  cyc := rootsOfUnity.isCyclic (ZMod 7) 3

end FqXt
end L20261018

#print axioms L20261018.FqXt.isPrimitiveRoot_two_zmod7
