import Hyp360

/-!
# R1272（S36 C 项 末步之六）：**`Finite (Fˣ/(Fˣ)³)`**

`HANDOFF` §S36 第 5 轮的组装：把 `Hyp360.pi_decomp` 的 `(i, residue v)` 打包成**有限**索引集
`Fin 3 × 𝓀ˣ`（用 `Fin 3` 而非 `ZMod 3`，省掉 `ZMod.val` 的记账），得到满射

```
σ : Fin 3 × 𝓀ˣ ↠ Fˣ/(Fˣ)³,   σ (k, c) := [π^k · lift c]
```

| 声明 | 内容 |
|---|---|
| **`mk_eq_of_eq_cube_mul`** | `b = c³·d ⟹ [b] = [d]`（`QuotientGroup.eq` ＋ `mem_powerSubgroup_iff`） |
| **`sigma`** | `Fin 3 × 𝓀ˣ → Fˣ/(Fˣ)³` |
| **`sigma_surjective`** | ★★★★★ 满射（`pi_decomp` ＋ `Hyp358.powerClass_eq_of_unitsResidue_eq`） |
| **`finite_powerClassQuotient`** | ★★★★★★ **`Finite (powerClassQuotient (LaurentSeries (ZMod 7))ˣ 3)`** |
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

/-- 局部记号：`F = 𝔽₇((t))` 的立方类商。 -/
local notation "Q3" => TauCeti.powerClassQuotient (LaurentSeries (ZMod 7))ˣ 3

/-- ★★★★ **相差一个立方 ⟹ 同类**。 -/
theorem mk_eq_of_eq_cube_mul {b c d : (LaurentSeries (ZMod 7))ˣ}
    (h : b = c ^ 3 * d) :
    (QuotientGroup.mk b : Q3) = QuotientGroup.mk d := by
  rw [QuotientGroup.eq, TauCeti.mem_powerSubgroup_iff]
  refine ⟨c⁻¹, ?_⟩
  rw [h, show (c⁻¹ : (LaurentSeries (ZMod 7))ˣ) ^ 3 = (c ^ 3)⁻¹ from inv_pow c 3, mul_inv_rev,
    mul_comm d⁻¹ ((c ^ 3)⁻¹), mul_assoc, inv_mul_cancel, mul_one]

/-- 满射 `Fin 3 × 𝓀ˣ ↠ Fˣ/(Fˣ)³`：`(k, c) ↦ [π^k · lift c]`。 -/
noncomputable def sigma :
    Fin 3 × (IsLocalRing.ResidueField ↥𝒪[LaurentSeries (ZMod 7)])ˣ → Q3 :=
  fun p => QuotientGroup.mk (pi ^ ((p.1.val : ℕ) : ℤ) *
    unitsToF (Classical.choose (unitsResidue_surjective p.2)))

/-- ★★★★★ **`sigma` 满射**。

给定 `a : Fˣ`，`pi_decomp` 给出 `i ∈ [0,3)`、`q`、`v` 使 `a = (π^q)³·(π^i·unitsToF v)`；
于是 `[a] = [π^i·unitsToF v]`（`mk_eq_of_eq_cube_mul`），
而 `[unitsToF v] = [unitsToF (lift (residue v))]`（`Hyp358`），
且 `i = i.toNat`（`i ≥ 0`）⟹ `[a] = sigma (⟨i.toNat, _⟩, residue v)`。 -/
theorem sigma_surjective : Function.Surjective (sigma) := by
  rintro ⟨a⟩
  obtain ⟨i, q, v, hi0, hi3, hdec⟩ := pi_decomp a
  -- 第一步：`[a] = [π^i · unitsToF v]`
  have h1 : (QuotientGroup.mk a : Q3) = QuotientGroup.mk (pi ^ i * unitsToF v) :=
    mk_eq_of_eq_cube_mul hdec
  -- 第二步：把 `π^i` 换成 `π^(i.toNat)`，`unitsToF v` 换成其剩余的提升
  have hcast : pi ^ i = pi ^ ((i.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hi0]
  have hbase : (QuotientGroup.mk (unitsToF v) : Q3)
      = QuotientGroup.mk (unitsToF (Classical.choose (unitsResidue_surjective (unitsResidue v)))) :=
    powerClass_eq_of_unitsResidue_eq v _ (Classical.choose_spec (unitsResidue_surjective (unitsResidue v))).symm
  refine ⟨(⟨i.toNat, by omega⟩, unitsResidue v), ?_⟩
  show (QuotientGroup.mk (pi ^ ((i.toNat : ℕ) : ℤ) *
      unitsToF (Classical.choose (unitsResidue_surjective (unitsResidue v)))) : Q3) = QuotientGroup.mk a
  rw [h1, ← hcast, QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hbase]

/-- ★★★★★★ **`Fˣ/(Fˣ)³` 有限**。 -/
instance finite_powerClassQuotient : Finite (Q3) :=
  Finite.of_surjective sigma sigma_surjective

end FqXt
end L20261018

#print axioms L20261018.FqXt.sigma_surjective
#print axioms L20261018.FqXt.finite_powerClassQuotient
