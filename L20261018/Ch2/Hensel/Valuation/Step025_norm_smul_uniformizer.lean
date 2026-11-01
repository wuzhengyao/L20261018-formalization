import L20261018.Ch2.Hensel.Valuation.Step024_normalization_sum_coeff

/-!
# R1046（**S29 · ④.1 的零件**）：`N(sᵐ · x) = πᵐ · N(x)`

极小性论证（④.1）要算 `N(sⁿ·x)`。`Hyp173` 的乘性/幂性以 `S` 一般形式给出，需要
`[Module.Free F L] [Module.Finite F L] [Nontrivial L]`。本文件在模型
`L = AdjoinRoot_F(X^p − Cπ)` 上把这三个实例落实，并机检范数公式。

| 声明 | 内容 |
|---|---|
| **`free_adjoinRoot_uniformizer_f`** | `Module.Free F L` |
| **`finite_adjoinRoot_uniformizer_f`** | `Module.Finite F L` |
| **`nontrivial_adjoinRoot_uniformizer_f`** | `Nontrivial L`（由 `finrank = p > 0`） |
| **`norm_pow_root_mul`** | **`N(sᵐ·x) = πᵐ · N(x)`** |
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section NormPowRoot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- `X^p − Cπ` 在 `F` 上首一。 -/
theorem monic_X_pow_sub_C_uniformizer (π : Fˣ) : (X ^ p - C (π : F)).Monic :=
  monic_X_pow_sub_C _ (Fact.out : p.Prime).pos.ne'

/-- 模型在 `F` 上**自由**。 -/
theorem free_adjoinRoot_uniformizer_f (π : Fˣ) :
    Module.Free F (AdjoinRoot (X ^ p - C (π : F))) :=
  Polynomial.Monic.free_adjoinRoot (monic_X_pow_sub_C_uniformizer (F := F) p π)

/-- 模型在 `F` 上**有限**。 -/
theorem finite_adjoinRoot_uniformizer_f (π : Fˣ) :
    Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
  Polynomial.Monic.finite_adjoinRoot (monic_X_pow_sub_C_uniformizer (F := F) p π)

/-- 模型**非平凡**（`finrank = p > 0`）。 -/
theorem nontrivial_adjoinRoot_uniformizer_f (π : Fˣ) :
    Nontrivial (AdjoinRoot (X ^ p - C (π : F))) := by
  haveI : Module.Free F (AdjoinRoot (X ^ p - C (π : F))) :=
    free_adjoinRoot_uniformizer_f (F := F) p π
  haveI : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    finite_adjoinRoot_uniformizer_f (F := F) p π
  exact Module.nontrivial_of_finrank_pos
    (by rw [finrank_adjoinRoot_uniformizer (F := F) p π]; exact (Fact.out : p.Prime).pos)

/-- **`N(sᵐ·x) = πᵐ · N(x)`**。 -/
theorem norm_pow_root_mul (π : Fˣ) (hp2 : p ≠ 2)
    (x : AdjoinRoot (X ^ p - C (π : F))) (m : ℕ) :
    Algebra.norm F ((AdjoinRoot.root (X ^ p - C (π : F))) ^ m * x)
      = (π : F) ^ m * Algebra.norm F x := by
  haveI : Nontrivial (AdjoinRoot (X ^ p - C (π : F))) :=
    nontrivial_adjoinRoot_uniformizer_f (F := F) p π
  haveI : Module.Free F (AdjoinRoot (X ^ p - C (π : F))) :=
    free_adjoinRoot_uniformizer_f (F := F) p π
  haveI : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    finite_adjoinRoot_uniformizer_f (F := F) p π
  rw [norm_mul (k := F) (S := AdjoinRoot (X ^ p - C (π : F))),
    norm_pow (k := F) (S := AdjoinRoot (X ^ p - C (π : F))),
    norm_root_uniformizer_adjoinRoot (F := F) p hp2 π]

end NormPowRoot

end L20261018

#print axioms L20261018.nontrivial_adjoinRoot_uniformizer_f
#print axioms L20261018.norm_pow_root_mul
