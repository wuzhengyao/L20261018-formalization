import Hyp348

/-!
# R1260（S35 C 项第 3 步）：`𝔽₇` 上 `2` 的阶为 3（算术见证）

`2³ = 8 ≡ 1`、`2 ≠ 1`、`2² = 4 ≠ 1` ⟹ `2` 是三次本原单位根。
本文件只机检这三条**算术事实**（下一步再用它们组装 `IsPrimitiveRoot`／
`HasEnoughRootsOfUnity`）；`orderOf` 在本 mathlib 里不能直接 `decide`，故先绕开它。
-/

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `2³ = 1` 于 `𝔽₇`。 -/
theorem two_pow_three_zmod7 : (2 : ZMod 7) ^ 3 = 1 := by decide

/-- `2 ≠ 1` 于 `𝔽₇`。 -/
theorem two_ne_one_zmod7 : (2 : ZMod 7) ≠ 1 := by decide

/-- `2² ≠ 1` 于 `𝔽₇`（阶不是 1 或 2）。 -/
theorem two_sq_ne_one_zmod7 : (2 : ZMod 7) ^ 2 ≠ 1 := by decide

end FqXt
end L20261018

#print axioms L20261018.FqXt.two_pow_three_zmod7
