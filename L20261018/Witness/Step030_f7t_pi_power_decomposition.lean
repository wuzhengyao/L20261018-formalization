import L20261018.Witness.Step029_f7t_zval_powers

/-!
# R1271（S36 C 项 末步之五）：`a = (π^q)³ · (π^i · 𝒪ˣ)` 分解（`i ∈ [0,3)`）

`HANDOFF` §S36 计划 **(H-B)** 的组装核心（纯群论部分，不含 `ZMod 3` 的记账）：

```
任意 a : Fˣ，取 n := zval a，i := n % 3、q := n / 3；
则 u := a·(π^n)⁻¹ 的阶为 0 ⟹ u = unitsToF v（Hyp359）；
而 π^n = (π^q)³ · π^i（n = 3q+i）⟹  a = (π^q)³ · (π^i · unitsToF v)。
```

| 声明 | 内容 |
|---|---|
| **`pi_decomp`** | ★★★★★ `∃ i q v, 0 ≤ i ∧ i < 3 ∧ a = (π^q)³ · (π^i · unitsToF v)` |

下一轮只需把 `i ∈ [0,3)` 打包成 `ZMod 3`，即可得满射
`ZMod 3 × 𝓀ˣ ↠ Fˣ/(Fˣ)³` ⟹ `Finite (Fˣ/(Fˣ)³)`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LaurentSeries ValuativeRel IsLocalRing Polynomial
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- ★★★★★ **`π`-分解**：`a = (π^q)³ · (π^i · unitsToF v)`，其中 `i = zval a % 3 ∈ [0,3)`。

⟹ `Fˣ/(Fˣ)³` 的每个类都由 `(i, residue v)` 决定，而 `i` 只取三个值、`residue v` 落在有限群 `𝓀ˣ` 里。 -/
theorem pi_decomp (a : (LaurentSeries (ZMod 7))ˣ) :
    ∃ (i q : ℤ) (v : (↥𝒪[LaurentSeries (ZMod 7)])ˣ),
      0 ≤ i ∧ i < 3 ∧ a = (pi ^ q) ^ (3 : ℤ) * (pi ^ i * unitsToF v) := by
  set n : ℤ := zval (F := LaurentSeries (ZMod 7)) a with hn
  set i : ℤ := n % 3 with hi
  set q : ℤ := n / 3 with hq
  have hi0 : 0 ≤ i := Int.emod_nonneg n (by norm_num)
  have hi3 : i < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hn3 : n = 3 * q + i := by
    have h := Int.mul_ediv_add_emod n 3
    rw [hq, hi]
    omega
  -- `u := a · (π^n)⁻¹` 的阶为 0
  have hzval : zval (F := LaurentSeries (ZMod 7)) (a * (pi ^ n)⁻¹) = 0 := by
    rw [zval_mul, zval_inv, zval_pi_zpow, hn]
    ring
  obtain ⟨v, hv⟩ := exists_unit_of_zval_eq_zero hzval
  refine ⟨i, q, v, hi0, hi3, ?_⟩
  -- `π^n = (π^q)³ · π^i`
  have hpi : pi ^ n = (pi ^ q) ^ (3 : ℤ) * pi ^ i := by
    rw [← zpow_mul, ← zpow_add]
    congr 1
    omega
  rw [hv, hpi]
  set X : (LaurentSeries (ZMod 7))ˣ := (pi ^ q) ^ (3 : ℤ) with hX
  set Y : (LaurentSeries (ZMod 7))ˣ := pi ^ i with hY
  show a = X * (Y * (a * (X * Y)⁻¹))
  rw [show X * (Y * (a * (X * Y)⁻¹)) = (X * Y) * a * (X * Y)⁻¹ by group]
  rw [mul_comm (X * Y) a, mul_assoc, mul_inv_cancel, mul_one]

end FqXt
end L20261018

#print axioms L20261018.FqXt.pi_decomp
