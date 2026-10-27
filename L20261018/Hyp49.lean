import L20261018.Hyp48
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# `(f)` 的「`E` 分裂 `D`」一步（用 `(1a)` 解除）

论文 `(f)`（`lem:basic-inclusions`(1)）的证明链第一环是：

> 在 `E` 上 `(a_1)` 与 `(a_2)` 都变为零，定义 `def:decomposable` 表明 `E` 分裂 `D`。

这里 `D ≃ (a_1,b_1)_F ⊗_F (a_2,b_2)_F` 是可分解除代数。本战役此前把这一步归入具名假设
`[[hyp-symbol-cup]]`；`Hyp48`（`(1a)`）已把所需的**退化支**机检：

    a = α^p ⟹ (a,b)_ζ ≅ M_p(K)      （Hyp48.nonempty_algEquiv）

本文件把它包成论文能用的形状：

* `IsSplit K A`：`A ≅ M_n(K)`（即 `A` 分裂）；
* `IsSplit.symbolAlg`（一般形式 `IsSplit.symbolAlg_of_isPow`）：第一槽为 `p` 次幂的符号代数分裂；
* `IsSplit.tensor`：两个分裂代数的张量积仍分裂（`Matrix.kroneckerAlgEquiv`）；
* **`IsSplit.tensorSymbolAlg`**：**`D = (a_1,b_1) ⊗ (a_2,b_2)` 在两个第一槽都是 `p` 次幂时分裂**
  —— 这就是 `(f)` 需要的那一步；论文情形取 `K := E`。

⟹ `[[hyp-symbol-cup]]` 中「`E` 分裂 `D` ⟹ …」这一半的**判据**（符号代数在第一槽成 `p` 次幂时分裂）
已完全机检；假设里剩下的只是**类层面**的 `[(a,b)_F] = (a)∪(b)`（`cor:symbol-cup` 的一般形式，
服务于 3.2(1)(2) 与 `(f)`(3)，那是 Merkurjev–Suslin 级的外部输入）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolSplit

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime]

/-- **分裂**：`A` 同构于某个全矩阵代数 `M_n(K)`。 -/
def IsSplit (K : Type u) [Field K] (A : Type u) [Ring A] [Algebra K A] : Prop :=
  ∃ n : ℕ, Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

namespace IsSplit

variable {A B : Type u} [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- 分裂性沿 `K`-代数同构搬运。 -/
theorem of_algEquiv (h : IsSplit K A) (e : A ≃ₐ[K] B) : IsSplit K B := by
  obtain ⟨n, ⟨eA⟩⟩ := h
  exact ⟨n, ⟨e.symm.trans eA⟩⟩

/-- **张量积保持分裂**：`M_m ⊗ M_n ≅ M_{mn}`（`Matrix.kroneckerAlgEquiv` ＋ 指标重排）。 -/
theorem tensor (hA : IsSplit K A) (hB : IsSplit K B) : IsSplit K (TensorProduct K A B) := by
  obtain ⟨m, ⟨eA⟩⟩ := hA
  obtain ⟨n, ⟨eB⟩⟩ := hB
  refine ⟨m * n, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.congr eA eB).trans
    ((Matrix.kroneckerAlgEquiv (Fin m) (Fin n) K).trans
      (Matrix.reindexAlgEquiv K K finProdFinEquiv))

end IsSplit

section Symbol

variable {ζ b : K} {α : Kˣ}

/-- **`(1a)` 的「分裂」形状**：第一槽是 `p` 次幂的符号代数与 `M_p(K)` 同构。 -/
theorem symbolAlg (hζ : IsPrimitiveRoot ζ p) (hb : b ≠ 0) (α : Kˣ) :
    IsSplit K (SymbolPres.SymbolAlg K p ((α : K) ^ p) b ζ) :=
  ⟨p, SymbolMatrix.nonempty_algEquiv hζ hb α⟩

/-- 把 `a` 写成 `p` 次幂的形式。 -/
theorem symbolAlg_of_isPow (hζ : IsPrimitiveRoot ζ p) (hb : b ≠ 0) {a : K}
    (ha : ∃ α : Kˣ, a = (α : K) ^ p) :
    IsSplit K (SymbolPres.SymbolAlg K p a b ζ) := by
  obtain ⟨α, rfl⟩ := ha
  exact symbolAlg hζ hb α

/-- **`(f)` 的「`E` 分裂 `D`」**：可分解除代数 `D = (a_1,b_1)_K ⊗_K (a_2,b_2)_K`
在两个第一槽都是 `p` 次幂时分裂。

论文情形取 `K := E`（`a_i ∈ E^{×p}`），即得「`E` 分裂 `D`」那一步。 -/
theorem tensorSymbolAlg (hζ : IsPrimitiveRoot ζ p) {b₁ b₂ : K} (hb₁ : b₁ ≠ 0)
    (hb₂ : b₂ ≠ 0) (α₁ α₂ : Kˣ) :
    IsSplit K (TensorProduct K
      (SymbolPres.SymbolAlg K p ((α₁ : K) ^ p) b₁ ζ)
      (SymbolPres.SymbolAlg K p ((α₂ : K) ^ p) b₂ ζ)) :=
  (symbolAlg (p := p) hζ hb₁ α₁).tensor (symbolAlg (p := p) hζ hb₂ α₂)

/-- 同上，但用「存在 `p` 次根」的形式陈述（更接近论文：`a_i ∈ E^{×p}`）。 -/
theorem tensorSymbolAlg_of_isPow (hζ : IsPrimitiveRoot ζ p) {b₁ b₂ a₁ a₂ : K}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (h₁ : ∃ α : Kˣ, a₁ = (α : K) ^ p)
    (h₂ : ∃ α : Kˣ, a₂ = (α : K) ^ p) :
    IsSplit K (TensorProduct K
      (SymbolPres.SymbolAlg K p a₁ b₁ ζ) (SymbolPres.SymbolAlg K p a₂ b₂ ζ)) := by
  obtain ⟨α₁, rfl⟩ := h₁
  obtain ⟨α₂, rfl⟩ := h₂
  exact tensorSymbolAlg hζ hb₁ hb₂ α₁ α₂

end Symbol

end SymbolSplit
