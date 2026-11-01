import L20261018.Hyp369

/-!
# R1283（S36 C 项 · `hK1` 基建 #1）：`exists_unit_rep` 的 `valLinOf` 层移植

`Hyp122.exists_unit_rep` 是 `ℚ_[7]` 版 `hK1`（`finrank (ker v̄) = 1`）证明的第一块：
「`ker v̄` 的每个元素都是某个**单位**的 Kummer 类」。它的陈述带 `valLin`／`normalizedValuation`
（局部域专属），本文件把它移植到本战役一般的 `v : Fˣ →* Multiplicative ℤ` 层
（取 `v = vCompatHom`、`F = 𝔽₇((t))`）。

| 声明 | 内容 |
|---|---|
| `zval_pow` | `zval (x^n) = n * zval x` |
| **`exists_unit_rep_F`** | ★★★★★ `valLinOf v hp y = 0 ⟹ ∃ u, zval u = 0 ∧ kc u = y` |

**证明骨架**（照 `Hyp122`，只把局部域零件换成 `Hyp353`／`Hyp359` 已机检的）：
`y = kc a`（`kummerClass_surjective`）→ `val y = 0` 即 `zval a ≡ 0 (mod 3)`（`valLinOf_kummerClass`）
→ 写 `zval a = 3m` → 取 `u := a * (π^{-m})³`：
`zval u = 3m + 3·(-m) = 0`（`zval_mul`／`zval_pow`／`zval_pi_zpow`），
而 `kc u = kc a`（`kummerClass_mul_pow_eq`：乘一个 `p` 次幂不改 Kummer 类）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open scoped PowerSeries

namespace L20261018
namespace FqXt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : HasEnoughRootsOfUnity (LaurentSeries (ZMod 7)) 3 :=
  hasEnoughRootsOfUnity_laurentSeries_zmod7_three

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- `zval (x^n) = n * zval x`。 -/
theorem zval_pow (x : (LaurentSeries (ZMod 7))ˣ) (n : ℕ) :
    zval (F := LaurentSeries (ZMod 7)) (x ^ n) = n * zval (F := LaurentSeries (ZMod 7)) x := by
  induction n with
  | zero => rw [pow_zero, zval_one]; norm_num
  | succ n ih => rw [pow_succ, zval_mul, ih]; push_cast; ring

/-- ★★★★★ **`ker v̄` 的每个元素都是某个「阶 0 单位」的 Kummer 类**（`valLinOf` 层）。 -/
theorem exists_unit_rep_F
    {y : GaloBase.V (LaurentSeries (ZMod 7)) 3}
    (hy : valLinOf (F := LaurentSeries (ZMod 7)) (p := 3)
      (vCompatHom (F := LaurentSeries (ZMod 7))) three_isUnit_laurentSeries y = 0) :
    ∃ u : (LaurentSeries (ZMod 7))ˣ,
      zval (F := LaurentSeries (ZMod 7)) u = 0 ∧
        KummerBridge.kummerClass (LaurentSeries (ZMod 7)) 3 three_isUnit_laurentSeries u = y := by
  obtain ⟨a, rfl⟩ := KummerV.kummerClass_surjective (F := LaurentSeries (ZMod 7)) (p := 3)
    three_isUnit_laurentSeries y
  -- `val (kc a) = 0` ⟹ `zval a ≡ 0 (mod 3)`
  have hva0 : valOfUnitOf (p := 3) (vCompatHom (F := LaurentSeries (ZMod 7))) a = 0 := by
    rw [← valLinOf_kummerClass]
    exact hy
  have hva : ((Multiplicative.toAdd (vCompatHom (F := LaurentSeries (ZMod 7)) a) : ℤ) :
      ZMod 3) = 0 := hva0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hva
  obtain ⟨m, hm⟩ := hva
  have hm' : zval (F := LaurentSeries (ZMod 7)) a = 3 * m := by
    rw [← toAdd_vCompatHom]
    exact hm
  -- `u := a * (π^{-m})³`
  refine ⟨a * (pi ^ (-m)) ^ 3, ?_, ?_⟩
  · rw [zval_mul, zval_pow, zval_pi_zpow, hm']
    ring
  · rw [kummerClass_mul_pow_eq]

end FqXt
end L20261018

#print axioms L20261018.FqXt.zval_pow
#print axioms L20261018.FqXt.exists_unit_rep_F
