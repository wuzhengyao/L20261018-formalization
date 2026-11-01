import L20261018.Hyp184

/-!
# R1038（路径 A · **S28 第 1 步**）：矩阵结构（对角侧 `j ≤ i`）

从 `Hyp184.leftMulMatrix_apply_eq`（和形式）
`M i j = Σ_k cₖ · π^((k+j)/p) · [(i:ℕ) = (k+j)%p]` 读出：

| 情形 | 结论 |
|---|---|
| **`(j:ℕ) ≤ (i:ℕ)`** | **`M i j = c ((i:ℕ) − (j:ℕ))`** |

**论证**：`k + j < 2p`，故 `(k+j)%p = i` 只有两种可能：
`k+j = i`（`q = 0`，存活，`k = i−j`）或 `k+j = i+p`（`q = 1`，则 `k = i−j+p ≥ p`，不可能）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section MatrixStructure

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **对角侧**：`j ≤ i` 时 `M i j = c (i − j)`。 -/
theorem leftMulMatrix_entry_of_le (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → F) {i j : Fin p} (hji : (j : ℕ) ≤ (i : ℕ)) :
    (Algebra.leftMulMatrix B (sumCoeff (F := F) p π c)) i j = c ((i : ℕ) - (j : ℕ)) := by
  rw [leftMulMatrix_apply_eq (F := F) p π hB c i j]
  have hlt : (i : ℕ) - (j : ℕ) < p := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
  rw [Finset.sum_eq_single (⟨(i : ℕ) - (j : ℕ), hlt⟩ : Fin p)]
  · -- 主项
    have hsum : ((⟨(i : ℕ) - (j : ℕ), hlt⟩ : Fin p) : ℕ) + (j : ℕ) = (i : ℕ) :=
      Nat.sub_add_cancel hji
    rw [hsum, Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt]
    simp
  · -- 其余项为零
    intro b _ hbne
    have hbj2 : (b : ℕ) + (j : ℕ) < 2 * p := by
      have h1 := b.isLt
      have h2 := j.isLt
      omega
    have hne : (i : ℕ) ≠ ((b : ℕ) + (j : ℕ)) % p := by
      intro heq
      rcases Nat.lt_or_ge ((b : ℕ) + (j : ℕ)) p with hlt' | hge'
      · rw [Nat.mod_eq_of_lt hlt'] at heq
        have : (b : ℕ) = (i : ℕ) - (j : ℕ) := by omega
        exact hbne (Fin.ext (by rw [this]))
      · have hmod : ((b : ℕ) + (j : ℕ)) % p = (b : ℕ) + (j : ℕ) - p := by
          rw [Nat.mod_eq_sub_mod hge']
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod] at heq
        have hb := b.isLt
        omega
    rw [if_neg hne]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **反对角侧**：`i < j` 时 `M i j = π · c (i + p − j)`。 -/
theorem leftMulMatrix_entry_of_lt (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (c : ℕ → F) {i j : Fin p} (hij : (i : ℕ) < (j : ℕ)) :
    (Algebra.leftMulMatrix B (sumCoeff (F := F) p π c)) i j
      = (π : F) * c ((i : ℕ) + p - (j : ℕ)) := by
  rw [leftMulMatrix_apply_eq (F := F) p π hB c i j]
  have hlt : (i : ℕ) + p - (j : ℕ) < p := by
    have := i.isLt
    omega
  rw [Finset.sum_eq_single (⟨(i : ℕ) + p - (j : ℕ), hlt⟩ : Fin p)]
  · -- 主项：`k + j = i + p`
    have hsum : ((⟨(i : ℕ) + p - (j : ℕ), hlt⟩ : Fin p) : ℕ) + (j : ℕ) = (i : ℕ) + p := by
      have h := i.isLt
      simp only [Fin.val_mk]
      omega
    rw [hsum]
    have hmod : ((i : ℕ) + p) % p = (i : ℕ) := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    have hdiv : ((i : ℕ) + p) / p = 1 := by
      rw [show (i : ℕ) + p = (i : ℕ) + p * 1 by ring,
        Nat.add_mul_div_left _ _ (Fact.out : p.Prime).pos, Nat.div_eq_of_lt i.isLt,
        Nat.zero_add]
    rw [hmod, hdiv, if_pos rfl, mul_one, pow_one, Fin.val_mk, mul_comm]
  · -- 其余项为零
    intro b _ hbne
    have hbj2 : (b : ℕ) + (j : ℕ) < 2 * p := by
      have h1 := b.isLt
      have h2 := j.isLt
      omega
    have hne : (i : ℕ) ≠ ((b : ℕ) + (j : ℕ)) % p := by
      intro heq
      rcases Nat.lt_or_ge ((b : ℕ) + (j : ℕ)) p with hlt' | hge'
      · rw [Nat.mod_eq_of_lt hlt'] at heq
        have hjle : (j : ℕ) ≤ (b : ℕ) + (j : ℕ) := Nat.le_add_left _ _
        omega
      · have hmod : ((b : ℕ) + (j : ℕ)) % p = (b : ℕ) + (j : ℕ) - p := by
          rw [Nat.mod_eq_sub_mod hge']
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod] at heq
        have : (b : ℕ) = (i : ℕ) + p - (j : ℕ) := by omega
        exact hbne (Fin.ext (by rw [this]))
    rw [if_neg hne]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

end MatrixStructure

end L20261018

#print axioms L20261018.leftMulMatrix_entry_of_le
#print axioms L20261018.leftMulMatrix_entry_of_lt
