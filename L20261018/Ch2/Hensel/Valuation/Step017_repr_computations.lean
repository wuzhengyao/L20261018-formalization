import L20261018.Ch2.Hensel.Valuation.Step016_explicit_basis_powers

/-!
# R1035（路径 A · **·b·iii ②（二）a**）：`repr` 的两条核心计算

`leftMulMatrix` 的逐元公式需要知道显式基 `B`（`Hyp181`：`B i = sⁱ`）下的坐标：

| 声明 | 内容 |
|---|---|
| **`basis_repr_root_pow`** | `r < p` 时 `B.repr (sʳ) i = if (i:ℕ) = r then 1 else 0` |
| **`basis_repr_smul_root_pow`** | `B.repr (πᵠ • sʳ) i = πᵠ * (if (i:ℕ) = r then 1 else 0)` |

配合 `Hyp179.root_pow_eq`（`sᵐ = π^(m/p) • s^(m%p)`）即得
`(leftMulMatrix B y) i j = Σ_k cₖ · π^((k+j)/p) · [(i:ℕ) = (k+j) % p]`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section ReprCalc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`B.repr (sʳ) i`**：`r < p` 时是单位向量。 -/
theorem basis_repr_root_pow (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    {r : ℕ} (hr : r < p) (i : Fin p) :
    B.repr ((AdjoinRoot.root (X ^ p - C (π : F))) ^ r) i = if (i : ℕ) = r then 1 else 0 := by
  conv_lhs => rw [← hB ⟨r, hr⟩]
  rw [Module.Basis.repr_self]
  by_cases h : i = ⟨r, hr⟩
  · subst h
    simp
  · have h' : ¬ ((i : ℕ) = r) := fun hh => h (Fin.ext hh)
    simp [h, h']

/-- **`B.repr (πᵠ • sʳ) i`**：乘性因子提到前面。 -/
theorem basis_repr_smul_root_pow (π : Fˣ) {B : Module.Basis (Fin p) F
      (AdjoinRoot (X ^ p - C (π : F)))}
    (hB : ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ))
    (q : ℕ) {r : ℕ} (hr : r < p) (i : Fin p) :
    B.repr ((π : F) ^ q • (AdjoinRoot.root (X ^ p - C (π : F))) ^ r) i
      = (π : F) ^ q * (if (i : ℕ) = r then 1 else 0) := by
  rw [map_smul]
  change (π : F) ^ q * B.repr ((AdjoinRoot.root (X ^ p - C (π : F))) ^ r) i
    = (π : F) ^ q * (if (i : ℕ) = r then 1 else 0)
  rw [basis_repr_root_pow (F := F) p π hB hr i]

end ReprCalc

end L20261018

#print axioms L20261018.basis_repr_root_pow
#print axioms L20261018.basis_repr_smul_root_pow
