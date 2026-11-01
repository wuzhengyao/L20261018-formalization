import L20261018.Ch2.Hensel.Valuation.Step018_left_mul_matrix_entrywise

/-!
# R1037（路径 A · **·b·iii ②（二）c**）：逐元公式（求和组装完成）

修复 R1036 登记的卡点：`(∑ x, ⇑(B.repr …)) i` → `∑ x, ⇑(B.repr …) i` 需要给
`Finset.sum_apply` 的 `g` **补上显式 `⇑`**（`(… : Fin p → F)`），而不是传 `Finsupp` 本身。

| 声明 | 内容 |
|---|---|
| **`leftMulMatrix_apply_eq`** | `(leftMulMatrix B y) i j = Σ_k cₖ · π^((k+j)/p) · [(i:ℕ) = (k+j)%p]` |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section EntryFormulaFull

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **逐元公式（完整）**。 -/
theorem leftMulMatrix_apply_eq (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → F) (i j : Fin p) :
    (Algebra.leftMulMatrix B (sumCoeff (F := F) p π c)) i j
      = ∑ k : Fin p, (c (k : ℕ) * (π : F) ^ (((k : ℕ) + (j : ℕ)) / p)
          * (if (i : ℕ) = ((k : ℕ) + (j : ℕ)) % p then 1 else 0) : F) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [sumCoeff_mul_basis (F := F) p π hB c j]
  rw [sumCoeffShift, map_sum]
  rw [Finset.sum_apply' (s := Finset.univ) i]
  exact Finset.sum_congr rfl fun k _ => repr_smul_coeff (F := F) p π hB c k i j

end EntryFormulaFull

end L20261018

#print axioms L20261018.leftMulMatrix_apply_eq
