import L20261018.Hyp173

/-!
# R1027（路径 A · **A1′·2·b·iv 的前提**）：`s^p = π`（模型内）＋ `s^{pn} = π^n` ＋ `gen = s` 的幂基

整性判据（`N(x)` 单位 ⟹ `x ∈ 𝒪_F[s]`）的装配需要把 `Hyp170`（系数清分母，乘 `π` 的幂）
搬到「乘 `s` 的幂」上，并需要 `x` 的坐标分解。本轮打地基：

| 声明 | 内容 |
|---|---|
| **`root_pow_eq_algebraMap`** | 模型内 `s^p = algebraMap π` |
| **`root_pow_mul`** | `s ^ (p * n) = (π : F) ^ n` |
| **`powerBasis_root`** | `AdjoinRoot.powerBasis` 的 `gen = s`、`dim = p` |

> 下一轮：坐标分解 `x = Σ_{i<p} aᵢ sⁱ`（`PowerBasis.basis`）＋ `Hyp170` ⟹
> `∃ n, s^n * x ∈ 𝒪_F[s]`（·b·iv 的归一化步）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel Polynomial

namespace L20261018

section RootPow

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- 模型内 **`s^p = of π`**（`s` 的 `p` 次幂就是 `π`）。 -/
theorem root_pow_eq_of (π : Fˣ) :
    (AdjoinRoot.root (X ^ p - C (π : F))) ^ p = AdjoinRoot.of (X ^ p - C (π : F)) (π : F) := by
  have hmk : AdjoinRoot.mk (X ^ p - C (π : F)) ((X : F[X]) ^ p)
      = AdjoinRoot.of (X ^ p - C (π : F)) (π : F) := by
    have hsub : AdjoinRoot.mk (X ^ p - C (π : F)) ((X : F[X]) ^ p)
        - AdjoinRoot.mk (X ^ p - C (π : F)) (C (π : F)) = 0 := by
      rw [← map_sub]
      have hpoly : ((X : F[X]) ^ p) - C (π : F) = (X ^ p - C (π : F)) := rfl
      rw [hpoly, AdjoinRoot.mk_self]
    have hCa : AdjoinRoot.mk (X ^ p - C (π : F)) (C (π : F))
        = AdjoinRoot.of (X ^ p - C (π : F)) (π : F) := AdjoinRoot.mk_C (π : F)
    have h1 : AdjoinRoot.mk (X ^ p - C (π : F)) ((X : F[X]) ^ p)
        = AdjoinRoot.mk (X ^ p - C (π : F)) (C (π : F)) := sub_eq_zero.mp hsub
    rw [h1, hCa]
  calc (AdjoinRoot.root (X ^ p - C (π : F))) ^ p
      = (AdjoinRoot.mk (X ^ p - C (π : F)) X) ^ p := by rw [AdjoinRoot.mk_X]
    _ = AdjoinRoot.mk (X ^ p - C (π : F)) ((X : F[X]) ^ p) := by rw [map_pow]
    _ = AdjoinRoot.of (X ^ p - C (π : F)) (π : F) := hmk

/-- **`s ^ (p * n) = of (π ^ n)`**。 -/
theorem root_pow_mul (π : Fˣ) (n : ℕ) :
    (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p * n)
      = AdjoinRoot.of (X ^ p - C (π : F)) ((π : F) ^ n) := by
  rw [pow_mul, root_pow_eq_of, ← map_pow]

/-- 模型的幂基：`gen = s`、`dim = p`。 -/
theorem powerBasis_root_gen (π : Fˣ) :
    ∃ (hne : (X ^ p - C (π : F)) ≠ 0),
      (AdjoinRoot.powerBasis (K := F) hne).gen = AdjoinRoot.root (X ^ p - C (π : F)) ∧
      (AdjoinRoot.powerBasis (K := F) hne).dim = p := by
  have hne : (X ^ p - C (π : F)) ≠ 0 := by
    intro h
    have hdeg := congrArg (fun f : F[X] => f.natDegree) h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at hdeg
    exact (Fact.out : p.Prime).ne_zero hdeg
  exact ⟨hne, AdjoinRoot.powerBasis_gen hne,
    (AdjoinRoot.powerBasis_dim hne).trans natDegree_X_pow_sub_C⟩

end RootPow

end L20261018

#print axioms L20261018.root_pow_eq_of
#print axioms L20261018.root_pow_mul
#print axioms L20261018.powerBasis_root_gen
