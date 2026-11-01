import L20261018.Hyp358

/-!
# R1270（S36 C 项 末步之四）：`zval` 的 `ℤ`-幂与「阶 0 ⟹ 是 `𝒪` 的单位」

`HANDOFF` §S36 计划 **(H-B)** 的第 1、2 块（`Finite (Fˣ/(Fˣ)³)` 的分解基础）：

| 声明 | 内容 |
|---|---|
| **`zval_pi_pow`** | `zval (π^n) = n`（`n : ℕ`） |
| **`zval_inv`** | `zval a⁻¹ = - zval a` |
| **`zval_pi_zpow`** | ★★★★ `zval (π^n) = n`（`n : ℤ`） |
| **`exists_unit_of_zval_eq_zero`** | ★★★★★ `zval a = 0 ⟹ a ∈ 像 (↥𝒪ˣ → Fˣ)`（`mem_integer_vCompat` ＋ 非 `𝔪` ⟹ 单位） |
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

/-- ★★★★ **`zval (π^n) = n`**（`n : ℕ`）。 -/
theorem zval_pi_pow (n : ℕ) :
    zval (F := LaurentSeries (ZMod 7)) (pi ^ n) = (n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, zval_one]; norm_num
  | succ n ih =>
    rw [pow_succ, zval_mul, ih, zval_pi]
    push_cast
    ring

/-- ★★★★ **`zval` 取逆变号**。 -/
theorem zval_inv (a : (LaurentSeries (ZMod 7))ˣ) :
    zval (F := LaurentSeries (ZMod 7)) a⁻¹ = - zval (F := LaurentSeries (ZMod 7)) a := by
  have h := zval_mul (F := LaurentSeries (ZMod 7)) a a⁻¹
  rw [mul_inv_cancel, zval_one] at h
  omega

/-- ★★★★ **`zval (π^n) = n`**（`n : ℤ`）。 -/
theorem zval_pi_zpow (n : ℤ) :
    zval (F := LaurentSeries (ZMod 7)) (pi ^ n) = n := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, zval_one]
  | succ n ih => rw [zpow_add, zpow_one, zval_mul, ih, zval_pi]
  | pred n ih =>
    rw [zpow_sub_one, zval_mul, ih, zval_inv, zval_pi]
    ring

/-- ★★★★★ **阶为 `0` 的单位来自 `↥𝒪ˣ`**。

`zval a = 0` ⟹ `a ∈ 𝒪[F]`（`mem_integer_vCompat`）且 `a ∉ 𝔪[F]`（`mem_maximalIdeal_vCompat`）
⟹ `a` 是 `↥𝒪[F]` 的单位 ⟹ 取 `v : ↥𝒪ˣ`。 -/
theorem exists_unit_of_zval_eq_zero {a : (LaurentSeries (ZMod 7))ˣ}
    (ha : zval (F := LaurentSeries (ZMod 7)) a = 0) :
    ∃ v : (↥𝒪[LaurentSeries (ZMod 7)])ˣ,
      unitsToF v = a := by
  have hmem : (a : LaurentSeries (ZMod 7)) ∈ 𝒪[LaurentSeries (ZMod 7)] :=
    mem_integer_vCompat (F := LaurentSeries (ZMod 7)) a (by rw [toAdd_vCompatHom, ha])
  have hnotmem : (⟨(a : LaurentSeries (ZMod 7)), hmem⟩ : ↥𝒪[LaurentSeries (ZMod 7)]) ∉ mF'' := by
    rw [mem_maximalIdeal_vCompat (F := LaurentSeries (ZMod 7)) a hmem, toAdd_vCompatHom, ha]
    exact lt_irrefl 0
  obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.mp hnotmem
  refine ⟨v, ?_⟩
  ext
  rw [Units.coe_map, hv]
  rfl

end FqXt
end L20261018

#print axioms L20261018.FqXt.zval_pi_zpow
#print axioms L20261018.FqXt.exists_unit_of_zval_eq_zero
