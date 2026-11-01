import L20261018.Hyp180

/-!
# R1034（路径 A · **·b·iii ②（二）预备**）：`Fin p`-索引的显式基 `B i = sⁱ`

矩阵元计算要在 `Matrix (Fin p) (Fin p) F` 上做，但 `AdjoinRoot.powerBasis hne` 的基是
`Basis (Fin pb.dim) F L`，而 `pb.dim = p` 只是**定理**（不是定义相等）。本轮用
`Basis.reindex` ＋ `finCongr` 把它搬到 `Fin p`：

```
B := (AdjoinRoot.powerBasis hne).basis.reindex (finCongr hdim.symm)
B i = pb.gen ^ (i : ℕ) = s ^ (i : ℕ)
```

| 声明 | 内容 |
|---|---|
| **`basis_root_pow`** | `∃ B : Basis (Fin p) F L, ∀ i, B i = s^(i:ℕ)` |
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section BasisFin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`Fin p`-索引的显式基**：`B i = sⁱ`。 -/
theorem basis_root_pow (π : Fˣ) :
    ∃ B : Module.Basis (Fin p) F (AdjoinRoot (X ^ p - C (π : F))),
      ∀ i : Fin p, B i = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (i : ℕ) := by
  have hne : (X ^ p - C (π : F)) ≠ 0 := by
    intro h
    have hd := congrArg (fun f : F[X] => f.natDegree) h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at hd
    exact (Fact.out : p.Prime).ne_zero hd
  have hdim : (AdjoinRoot.powerBasis (K := F) (f := X ^ p - C (π : F)) hne).dim = p :=
    (AdjoinRoot.powerBasis_dim hne).trans natDegree_X_pow_sub_C
  refine ⟨(AdjoinRoot.powerBasis (K := F) (f := X ^ p - C (π : F)) hne).basis.reindex
    (finCongr hdim), ?_⟩
  intro i
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
  simp

end BasisFin

end L20261018

#print axioms L20261018.basis_root_pow
