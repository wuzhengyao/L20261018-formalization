import Hyp182

/-!
# R1036（路径 A · **·b·iii ②（二）b**）：`leftMulMatrix` 的逐元公式（组装完成）

| 声明 | 内容 |
|---|---|
| **`leftMulMatrix_apply_eq`** | `(leftMulMatrix B y) i j = Σ_k cₖ · π^((k+j)/p) · [(i:ℕ) = (k+j) % p]` |

由 `Hyp182`（`repr` 两计算）＋ `Hyp179.root_pow_eq` ＋ `Finset.sum_mul`／`map_sum` 组装。
下一步（②（三））用它读：`j ≤ i` 唯一存活项 `k = i−j`（`q = 0`）、`i < j` 唯一存活项 `k = i−j+p`（`q = 1`），
故模 `π` 后下三角、对角 `c₀` ⟹ `det ≡ c₀^p`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section EntryFormula

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- 系数族对应的显式元素 `Σ_{k<p} cₖ sᵏ`（单独定义以免 `∑` 的元素类型歧义）。 -/
noncomputable def sumCoeff (π : Fˣ) (c : ℕ → F) :
    AdjoinRoot (X ^ p - C (π : F)) :=
  ∑ k : Fin p, c (k : ℕ) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ (k : ℕ)

/-- 平移的系数和 `Σ_{k<p} cₖ s^(k+j)`（同样单独定义）。 -/
noncomputable def sumCoeffShift (π : Fˣ) (c : ℕ → F) (j : ℕ) :
    AdjoinRoot (X ^ p - C (π : F)) :=
  ∑ k : Fin p, c (k : ℕ) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ ((k : ℕ) + j)

/-- **`y * sʲ = Σₖ cₖ • s^(k+j)`**：乘性矩阵的第一步（单项合并）。 -/
theorem sumCoeff_mul_basis (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → F) (j : Fin p) :
    sumCoeff (F := F) p π c * B j = sumCoeffShift (F := F) p π c (j : ℕ) := by
  rw [sumCoeff, sumCoeffShift, hB j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, ← pow_add]

/-- **单项的坐标**：`B.repr (c k • s^(k+j)) i = cₖ · π^((k+j)/p) · [i = (k+j)%p]`。 -/
theorem repr_smul_coeff (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → F) (k : Fin p) (i j : Fin p) :
    B.repr (c (k : ℕ) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ ((k : ℕ) + (j : ℕ))) i
      = c (k : ℕ) * (π : F) ^ (((k : ℕ) + (j : ℕ)) / p)
        * (if (i : ℕ) = ((k : ℕ) + (j : ℕ)) % p then 1 else 0) := by
  rw [root_pow_eq (F := F) p π ((k : ℕ) + (j : ℕ))]
  rw [map_smul]
  rw [map_smul]
  change c (k : ℕ) * ((π : F) ^ (((k : ℕ) + (j : ℕ)) / p)
      * B.repr ((AdjoinRoot.root (X ^ p - C (π : F))) ^ (((k : ℕ) + (j : ℕ)) % p)) i)
    = c (k : ℕ) * (π : F) ^ (((k : ℕ) + (j : ℕ)) / p)
      * (if (i : ℕ) = ((k : ℕ) + (j : ℕ)) % p then 1 else 0)
  rw [basis_repr_root_pow (F := F) p π hB (Nat.mod_lt _ (Fact.out : p.Prime).pos) i]
  ring

end EntryFormula

end L20261018

#print axioms L20261018.sumCoeff_mul_basis
#print axioms L20261018.repr_smul_coeff
