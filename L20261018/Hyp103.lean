import L20261018.Hyp102
/-!
# 3.6 组装（六）：`ZMod p` 的 `NeZero 2` 独立成件（R929）

`A.theorem_3_6` 要 `[NeZero (2 : k)]`，实例化处 `k = ZMod p`。`Hyp92`／`Hyp101` 里都是**局部
`haveI`**，无法跨文件引用（与 `hNU` 同一个教训，R927）⟹ 独立成件。

论文固定 `p` 为**奇**素数，故 `hp2 : p ≠ 2` 时 `2 ≠ 0` 在 `ZMod p` 中。

## 主结果

* **`neZero_two_zmod`**：`NeZero (2 : ZMod p)`（`p` 为奇素数）。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Assemble36

/-- **`ZMod p` 中 `2 ≠ 0`**（`p` 为奇素数）—— `A.theorem_3_6` 的 `[NeZero (2 : k)]` 前提。 -/
theorem neZero_two_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : NeZero (2 : ZMod p) where
  out := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using h)
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    exact hp2 (le_antisymm hple hpge)

end Assemble36

#print axioms Assemble36.neZero_two_zmod
