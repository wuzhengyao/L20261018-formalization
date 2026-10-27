import L20261018.Hyp47
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# 缺口 1 残余：**退化支** `(a,b)_ζ ≅ M_p(K)`（第一段：模型与三条关系）

`(f)` 需要的恰是**退化支**：`a = α^p` 时符号代数 `(a,b)_ζ = K⟨x,y⟩/(x^p−a, y^p−b, yx−ζxy)`
同构于 `M_p(K)`（而**不是**循环交叉积——平凡扩张上后者只有 `dim 1`；两者只在 Brauer 群一致，
见 `Hyp41`）。论文 `def:decomposable` 的循环代数认同自带 `a ∉ F^{×p}` 前提，故**不覆盖**这一支。

按 `Hyp47.nonempty_algEquiv_of_finrank`，只需在 `M_p(K)` 里给出两个显式矩阵 `X, Y`：

* `Xmat = diag(α ζ^{-i})_{i ∈ Fin p}`（特征值互不相同：`α ≠ 0` 且 `ζ` 本原），
* `Ymat` = 带 `b` 的循环移位（`e_i ↦ e_{i+1}`，`e_{p-1} ↦ b e_0`），

并证三条关系：`X^p = a`、`Y^p = b`、`Y X = ζ (X Y)`；再证 `X, Y` 生成 `M_p(K)`（下一段）。

## 主结果

* `Xmat_pow`／`Ymat_pow`／`Ymat_mul_Xmat`：三条关系（`X^p = a`、`Y^p = b`、`Y X = ζ (X Y)`）。
* `Ymat_pow_apply`：`(Y^k)_{ij}` 的一般条目公式；`Ymat_pow` 是其 `k = p` 特例。
* `mem_diagonal_single`：**Lagrange 幂等元**给出所有对角单位 `E_{ii}`。
* `mem_E`：**所有矩阵单位** `E_{ji}` 都在生成子代数里（`Y^{j-i}` 搬 `E_{ii}`，绕回时多一个 `b`）。
* `adjoin_eq_top`：`Algebra.adjoin K {Xmat, Ymat} = ⊤`（矩阵单位张成）。
* **`nonempty_algEquiv`**（**本文件的主定理，(1a) 收口**）：
  `a = α^p` ⟹ `SymbolPres.SymbolAlg K p a b ζ ≃ₐ[K] M_p(K)`。

## 这一步对 `(f)` 的意义

`(f)` 的证明中「在 `E` 上 `(a_i)` 变为零 ⟹ `E` 分裂 `D`」一步需要的正是**退化支**：
`a_i ∈ E^{×p}` 时 `(a_i,b_i)_E ≅ M_p(E)`，故其 Brauer 类平凡、`E` 分裂。论文
`def:decomposable` 的循环代数认同自带 `a ∉ F^{×p}` 前提，**不覆盖**这一支——若只照它走，
恰好漏掉 `(f)` 需要的全部情形。（非退化支 `(1b)` 见下一轮。）
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace SymbolMatrix

universe u

open Matrix

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime]

/-- 对角生成元 `X = diag(α ζ^{-i})`。特征值 `α ζ^{-i}` 两两不同（`a = α^p` 时它们的 `p` 次幂全等于 `a`）。 -/
noncomputable def Xmat (ζ : K) (α : Kˣ) : Matrix (Fin p) (Fin p) K :=
  Matrix.diagonal (fun i : Fin p => (α : K) * (ζ⁻¹) ^ (i : ℕ))

/-- 带 `b` 的循环移位生成元：`e_i ↦ e_{i+1}`（`i < p-1`）、`e_{p-1} ↦ b e_0`。 -/
noncomputable def Ymat (b : K) : Matrix (Fin p) (Fin p) K :=
  Matrix.of (fun i j : Fin p =>
    if (i : ℕ) = (j : ℕ) + 1 then (1 : K)
    else if (i : ℕ) = 0 ∧ (j : ℕ) = p - 1 then b else 0)

variable {ζ : K} {α : Kˣ} {b : K}

namespace Basic

theorem of_apply (i j : Fin p) :
    Ymat (p := p) b i j =
      (if (i : ℕ) = (j : ℕ) + 1 then (1 : K)
        else if (i : ℕ) = 0 ∧ (j : ℕ) = p - 1 then b else 0) := by
  simp only [Ymat, Matrix.of_apply]

/-- `b` 的移位在 `0` 之外的指标上只看 `i = j + 1`。 -/
theorem Ymat_apply_of_ne_zero (i j : Fin p) (h1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Ymat (p := p) b i j
      = (if (i : ℕ) = 0 ∧ (j : ℕ) = p - 1 then b else 0) := by
  rw [of_apply, if_neg h1]

/-- `(Y * diag d)_{ij} = Y_{ij} d_j`。 -/
theorem Ymat_mul_diagonal (d : Fin p → K) (i j : Fin p) :
    (Ymat (p := p) b * Matrix.diagonal d) i j = Ymat (p := p) b i j * d j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hk
    rw [Matrix.diagonal_apply, if_neg hk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- `(diag d * Y)_{ij} = d_i Y_{ij}`。 -/
theorem diagonal_mul_Ymat (d : Fin p → K) (i j : Fin p) :
    (Matrix.diagonal d * Ymat (p := p) b) i j = d i * Ymat (p := p) b i j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro k _ hk
    rw [Matrix.diagonal_apply, if_neg (Ne.symm hk), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Basic

/-! ### `X ^ p = a` -/

theorem Xmat_pow (hζ : IsPrimitiveRoot ζ p) (α : Kˣ) :
    Xmat (p := p) ζ α ^ p
      = algebraMap K (Matrix (Fin p) (Fin p) K) ((α : K) ^ p) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [Xmat, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_eq_diagonal_iff]
  intro i
  simp only [Pi.pow_apply]
  have hβ : (ζ⁻¹ : K) ^ ((i : ℕ) * p) = 1 := by
    have h2 : (ζ : K) ^ ((i : ℕ) * p) = 1 := by
      rw [mul_comm ((i : ℕ)) p, pow_mul, hζ.pow_eq_one, one_pow]
    rw [inv_pow, h2, inv_one]
  rw [mul_pow, ← pow_mul, hβ, mul_one]
  simp

/-! ### `Y X = ζ (X Y)` -/

/-- 特征值的比值：`Y_{ij} ≠ 0` 处必有 `x_j = ζ x_i`。 -/
theorem eigenvalue_relation (hζ : IsPrimitiveRoot ζ p) (α : Kˣ) (i j : Fin p)
    (hY : Ymat (p := p) b i j ≠ 0) :
    (α : K) * (ζ⁻¹) ^ (j : ℕ) = ζ * ((α : K) * (ζ⁻¹) ^ (i : ℕ)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  have hβp : (ζ⁻¹ : K) ^ p = 1 := by
    rw [inv_pow, hζ.pow_eq_one, inv_one]
  have hβζ : (ζ⁻¹ : K) * ζ = 1 := inv_mul_cancel₀ hζ0
  rw [Basic.of_apply] at hY
  by_cases h1 : (i : ℕ) = (j : ℕ) + 1
  · have hi : (i : ℕ) = (j : ℕ) + 1 := h1
    have hβi : (ζ⁻¹ : K) ^ (i : ℕ) = (ζ⁻¹) ^ (j : ℕ) * ζ⁻¹ := by
      rw [hi, pow_succ]
    rw [hβi]
    have hstep : ζ * ((α : K) * ((ζ⁻¹) ^ (j : ℕ) * ζ⁻¹))
        = ((α : K) * (ζ⁻¹) ^ (j : ℕ)) * (ζ * ζ⁻¹) := by ring
    rw [hstep, mul_inv_cancel₀ hζ0, mul_one]
  · by_cases h2 : (i : ℕ) = 0 ∧ (j : ℕ) = p - 1
    · obtain ⟨hi0, hj⟩ := h2
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hβ : (ζ⁻¹ : K) ^ (p - 1) = ζ := by
        have hstep : (ζ : K) ^ (p - 1) * ζ = 1 := by
          rw [← pow_succ, Nat.sub_one_add_one (by omega : p ≠ 0), hζ.pow_eq_one]
        have h2' : (ζ : K) ^ (p - 1) = ζ⁻¹ := by
          calc (ζ : K) ^ (p - 1) = ζ ^ (p - 1) * 1 := by rw [mul_one]
            _ = ζ ^ (p - 1) * (ζ * ζ⁻¹) := by rw [mul_inv_cancel₀ hζ0]
            _ = ζ ^ (p - 1) * ζ * ζ⁻¹ := by rw [mul_assoc]
            _ = 1 * ζ⁻¹ := by rw [hstep]
            _ = ζ⁻¹ := one_mul _
        rw [inv_pow, h2', inv_inv]
      rw [hi0, hj, pow_zero, mul_one, hβ]
      ring
    · exfalso
      rw [if_neg h1, if_neg h2] at hY
      exact hY rfl

/-- **关系 3**：`Y X = ζ (X Y)`。 -/
theorem Ymat_mul_Xmat (hζ : IsPrimitiveRoot ζ p) (b : K) (α : Kˣ) :
    Ymat (p := p) b * Xmat (p := p) ζ α
      = algebraMap K (Matrix (Fin p) (Fin p) K) ζ
          * (Xmat (p := p) ζ α * Ymat (p := p) b) := by
  ext i j
  rw [Xmat, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul,
    Basic.Ymat_mul_diagonal, Basic.diagonal_mul_Ymat]
  by_cases hY : Ymat (p := p) b i j = 0
  · rw [hY, zero_mul, mul_zero, mul_zero]
  · have h := eigenvalue_relation (p := p) (b := b) hζ α i j hY
    have halg : (algebraMap K (Fin p → K)) ζ i = ζ := by simp
    rw [h, halg]
    ring

/-! ### `Y ^ p = b`（带 `b` 的循环移位的 `p` 次幂） -/

/-- 前一指标：`i > 0` 时 `Y` 在列 `i-1` 处取 `1`。 -/
theorem Ymat_apply_pred (i j : Fin p) (hi : (i : ℕ) ≠ 0) (h1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Ymat (p := p) b i j = (if (j : ℕ) = (i : ℕ) - 1 then (1 : K) else 0) := by
  rw [Basic.of_apply, if_neg h1]
  have h2 : ¬ ((i : ℕ) = 0 ∧ (j : ℕ) = p - 1) := fun h => hi h.1
  rw [if_neg h2]
  have : ((i : ℕ) = (j : ℕ) + 1) ↔ ((j : ℕ) = (i : ℕ) - 1) := by omega
  by_cases h : (j : ℕ) = (i : ℕ) - 1
  · rw [if_pos h]; exact absurd (this.mpr h) h1
  · rw [if_neg h]

/-- 一般次幂的条目公式：`(Y^k)_{ij} = 1`（`i = j + k`）、`b`（`i + p = j + k`）、否则 `0`。 -/
theorem Ymat_pow_apply (k : ℕ) (hk : k ≤ p) (i j : Fin p) :
    (Ymat (p := p) b ^ k) i j =
      (if (i : ℕ) = (j : ℕ) + k then (1 : K)
        else if (i : ℕ) + p = (j : ℕ) + k then b else 0) := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply, if_pos rfl, if_pos (by omega : (i : ℕ) = (i : ℕ) + 0)]
    · rw [Matrix.one_apply, if_neg hij,
        if_neg (by omega : ¬ ((i : ℕ) = (j : ℕ) + 0)),
        if_neg (by have := i.isLt; have := j.isLt; omega : ¬ ((i : ℕ) + p = (j : ℕ) + 0))]
  | succ k ih =>
    have hk' : k ≤ p := by omega
    rw [pow_succ', Matrix.mul_apply]
    by_cases hi0 : (i : ℕ) = 0
    · -- `i = 0`：只剩 `l = p-1`（值 `b`）
      have hlt : 0 < p := by have := (Fact.out : p.Prime).two_le; omega
      set lm : Fin p := ⟨p - 1, by omega⟩ with hlm
      rw [Finset.sum_eq_single lm]
      · have hY : Ymat (p := p) b i lm = b := by
          rw [Basic.of_apply]
          have h1 : (i : ℕ) ≠ (lm : ℕ) + 1 := by simp [hlm]; omega
          have h2 : ((i : ℕ) = 0 ∧ (lm : ℕ) = p - 1) := by simp [hlm, hi0]
          rw [if_neg h1, if_pos h2]
        rw [hY, ih hk' lm j]
        have hA : ¬ ((i : ℕ) = (j : ℕ) + (k + 1)) := by omega
        have hB : ((i : ℕ) + p = (j : ℕ) + (k + 1)) ↔ ((j : ℕ) + k = p - 1) := by
          simp [hi0]; omega
        have hC : ((lm : ℕ) = (j : ℕ) + k) ↔ ((j : ℕ) + k = p - 1) := by
          simp [hlm]; omega
        by_cases hcase : (j : ℕ) + k = p - 1
        · rw [if_pos (hC.mpr hcase), if_neg hA, if_pos (hB.mpr hcase), mul_one]
        · have hC' : ¬ ((lm : ℕ) = (j : ℕ) + k) := fun h => hcase (hC.mp h)
          have hD' : ¬ ((lm : ℕ) + p = (j : ℕ) + k) := by simp [hlm]; omega
          have hB' : ¬ ((i : ℕ) + p = (j : ℕ) + (k + 1)) := fun h => hcase (hB.mp h)
          rw [if_neg hC', if_neg hD', if_neg hA, if_neg hB', mul_zero]
      · intro l _ hl
        rw [Basic.of_apply]
        have h1 : (i : ℕ) ≠ (l : ℕ) + 1 := by omega
        have h2 : ¬ ((i : ℕ) = 0 ∧ (l : ℕ) = p - 1) := by
          intro hh; exact hl (Fin.ext (by simp [hlm]; omega))
        rw [if_neg h1, if_neg h2, zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ lm) hmem
    · -- `i > 0`：只剩 `l = i-1`（值 `1`）
      have hlt : 0 < p := by have := (Fact.out : p.Prime).two_le; omega
      obtain ⟨iv, hiv⟩ : ∃ iv : ℕ, (i : ℕ) = iv + 1 := ⟨(i : ℕ) - 1, by omega⟩
      set lm : Fin p := ⟨iv, by omega⟩ with hlm
      have hlmv : (lm : ℕ) = iv := by simp [hlm]
      rw [Finset.sum_eq_single lm]
      · have hY : Ymat (p := p) b i lm = 1 := by
          rw [Basic.of_apply]
          rw [if_pos (by omega : (i : ℕ) = (lm : ℕ) + 1)]
        rw [hY, ih hk' lm j, one_mul]
        have hA : ((i : ℕ) = (j : ℕ) + (k + 1)) ↔ ((lm : ℕ) = (j : ℕ) + k) := by omega
        have hB : ((i : ℕ) + p = (j : ℕ) + (k + 1)) ↔ ((lm : ℕ) + p = (j : ℕ) + k) := by omega
        by_cases hcase : (lm : ℕ) = (j : ℕ) + k
        · rw [if_pos hcase, if_pos (hA.mpr hcase)]
        · rw [if_neg hcase, if_neg (fun h => hcase (hA.mp h))]
          by_cases hcase2 : (lm : ℕ) + p = (j : ℕ) + k
          · rw [if_pos hcase2, if_pos (hB.mpr hcase2)]
          · rw [if_neg hcase2, if_neg (fun h => hcase2 (hB.mp h))]
      · intro l _ hl
        rw [Basic.of_apply]
        have h1 : (i : ℕ) ≠ (l : ℕ) + 1 := by
          intro h; exact hl (Fin.ext (by omega))
        have h2 : ¬ ((i : ℕ) = 0 ∧ (l : ℕ) = p - 1) := fun h => hi0 h.1
        rw [if_neg h1, if_neg h2, zero_mul]
      · intro hmem; exact absurd (Finset.mem_univ lm) hmem

/-- **`Y ^ p = b · 1`**。 -/
theorem Ymat_pow :
    Ymat (p := p) b ^ p = algebraMap K (Matrix (Fin p) (Fin p) K) b := by
  ext i j
  rw [Ymat_pow_apply p le_rfl i j, Matrix.algebraMap_eq_diagonal]
  have hb : ((algebraMap K (Fin p → K)) b) = fun _ => b := rfl
  rw [hb, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_neg (by omega : ¬ ((i : ℕ) = (i : ℕ) + p)),
      if_pos (by omega : (i : ℕ) + p = (i : ℕ) + p), if_pos rfl]
  · rw [if_neg (by have := i.isLt; have := j.isLt; omega : ¬ ((i : ℕ) = (j : ℕ) + p)),
      if_neg (by have := i.isLt; have := j.isLt; omega : ¬ ((i : ℕ) + p = (j : ℕ) + p)),
      if_neg hij]

/-! ### 生成性：`X, Y` 生成整个 `M_p(K)`

三步：① Lagrange 幂等元给出对角单位 `E_{ii}`；② 用 `Y^k` 把 `E_{ii}` 搬成所有矩阵单位
`E_{ji}`；③ 矩阵单位张成 `M_p(K)`。 -/

/-- 特征值 `x_i = α ζ^{-i}`。 -/
noncomputable def xval (ζ : K) (α : Kˣ) (i : Fin p) : K := (α : K) * (ζ⁻¹) ^ (i : ℕ)

/-- 生成元集合。 -/
noncomputable abbrev gens (ζ : K) (α : Kˣ) (b : K) : Set (Matrix (Fin p) (Fin p) K) :=
  {Xmat (p := p) ζ α, Ymat (p := p) b}

/-- 由 `X, Y` 生成的 `K`-子代数。 -/
noncomputable abbrev genAlg (ζ : K) (α : Kˣ) (b : K) :
    Subalgebra K (Matrix (Fin p) (Fin p) K) :=
  Algebra.adjoin K (gens (p := p) ζ α b)

theorem Xmat_eq_diagonal (ζ : K) (α : Kˣ) :
    Xmat (p := p) ζ α = Matrix.diagonal (xval ζ α) := rfl

/-- 特征值两两不同（`ζ` 本原 ＋ `α ≠ 0`）。 -/
theorem xval_injective (hζ : IsPrimitiveRoot ζ p) (α : Kˣ) {i j : Fin p}
    (h : xval ζ α i = xval ζ α j) : i = j := by
  have hα : (α : K) ≠ 0 := α.ne_zero
  have h1 : (ζ⁻¹) ^ (i : ℕ) = (ζ⁻¹) ^ (j : ℕ) := by
    simp only [xval] at h
    exact mul_left_cancel₀ hα h
  have h2 : (ζ : K) ^ (i : ℕ) = (ζ : K) ^ (j : ℕ) := by
    have hinv := congrArg (fun t : K => t⁻¹) h1
    simpa [inv_pow] using hinv
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h2)

/-- 矩阵单位 `E_{ji}`：第 `(j,i)` 元为 `1`。 -/
def E (j i : Fin p) : Matrix (Fin p) (Fin p) K := Matrix.single j i 1

theorem E_apply (j i a b : Fin p) :
    E (p := p) (K := K) j i a b = if j = a ∧ i = b then (1 : K) else 0 := by
  simp only [E, Matrix.single_apply]

theorem E_self_eq_diagonal (i : Fin p) :
    E (p := p) (K := K) i i
      = Matrix.diagonal (fun k => if k = i then (1 : K) else 0) := by
  ext a b
  rw [E_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases hai : a = i
    · rw [if_pos hai, if_pos ⟨hai.symm, hai.symm⟩]
    · rw [if_neg hai, if_neg (fun h : i = a ∧ i = a => hai h.1.symm)]
  · rw [if_neg hab, if_neg (fun h : i = a ∧ i = b => hab (by rw [← h.1, ← h.2]))]

/-! #### 第一步：Lagrange 幂等元给出 `E_{ii}` -/

/-- 每个 Lagrange 因子 `(x_i - x_j)⁻¹ (X - x_j)` 都是对角阵。 -/
theorem lagrangeFactor_eq (ζ : K) (α : Kˣ) (i j : Fin p) :
    (algebraMap K (Matrix (Fin p) (Fin p) K) ((xval ζ α i - xval ζ α j)⁻¹)
        * (Xmat ζ α - algebraMap K (Matrix (Fin p) (Fin p) K) (xval ζ α j)))
      = Matrix.diagonal
          (fun k => (xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j)) := by
  rw [Xmat_eq_diagonal, Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal]
  rfl

/-- 单个 Lagrange 因子在生成子代数里。 -/
theorem lagrangeFactor_mem (ζ : K) (α : Kˣ) (b : K) (i j : Fin p) :
    Matrix.diagonal (fun k => (xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j))
      ∈ genAlg (p := p) ζ α b := by
  rw [← lagrangeFactor_eq ζ α i j]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.sub_mem _ (Algebra.subset_adjoin (by simp))
      (Subalgebra.algebraMap_mem _ _))

/-- 部分积（逐点积之对角阵）在生成子代数里。 -/
theorem prod_diagonal_mem (ζ : K) (α : Kˣ) (b : K) (i : Fin p) (s : Finset (Fin p)) :
    Matrix.diagonal
        (fun k => ∏ j ∈ s, ((xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j)))
      ∈ genAlg (p := p) ζ α b := by
  induction s using Finset.induction with
  | empty =>
    have h : (fun k : Fin p => ∏ j ∈ (∅ : Finset (Fin p)),
        ((xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j))) = fun _ => (1 : K) := by
      funext k
      rw [Finset.prod_empty]
    rw [h, Matrix.diagonal_one]
    exact Subalgebra.one_mem _
  | insert a s ha ih =>
    have h : (fun k : Fin p => ∏ j ∈ insert a s,
        ((xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j)))
        = fun k => ((xval ζ α i - xval ζ α a)⁻¹ * (xval ζ α k - xval ζ α a))
            * (∏ j ∈ s, ((xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j))) := by
      funext k
      rw [Finset.prod_insert ha]
    rw [h, ← Matrix.diagonal_mul_diagonal]
    exact Subalgebra.mul_mem _ (lagrangeFactor_mem ζ α b i a) ih

/-- 逐点求值：`∏_{j≠i} (x_i - x_j)⁻¹ (x_k - x_j) = δ_{ki}`。 -/
theorem prod_pointwise (hζ : IsPrimitiveRoot ζ p) (α : Kˣ) (i : Fin p) :
    (fun k : Fin p => ∏ j ∈ Finset.univ.erase i,
        ((xval ζ α i - xval ζ α j)⁻¹ * (xval ζ α k - xval ζ α j)))
      = fun k => if k = i then (1 : K) else 0 := by
  funext k
  by_cases hk : k = i
  · rw [hk, if_pos rfl, Finset.prod_eq_one]
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hne : xval ζ α i - xval ζ α j ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hji (xval_injective hζ α h).symm
    exact inv_mul_cancel₀ hne
  · rw [if_neg hk]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
      (by rw [sub_self, mul_zero])

/-- **第一步**：对角单位 `E_{ii}` 在生成子代数里。 -/
theorem mem_diagonal_single (hζ : IsPrimitiveRoot ζ p) (α : Kˣ) (b : K) (i : Fin p) :
    Matrix.diagonal (fun k : Fin p => if k = i then (1 : K) else 0)
      ∈ genAlg (p := p) ζ α b := by
  have h := prod_diagonal_mem ζ α b i (Finset.univ.erase i)
  rwa [prod_pointwise hζ α i] at h

/-! #### 第二步：用 `Y^k` 把 `E_{ii}` 搬成所有矩阵单位 `E_{ji}` -/

/-- 右乘 `E ii` 取第 `i` 列。 -/
theorem mul_E_apply (M : Matrix (Fin p) (Fin p) K) (i l m : Fin p) :
    (M * E (p := p) (K := K) i i) l m
      = M l i * (if m = i then (1 : K) else 0) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [E_apply]
    by_cases hm : m = i
    · rw [if_pos ⟨rfl, hm.symm⟩, if_pos hm]
    · rw [if_neg (fun h : i = i ∧ i = m => hm h.2.symm), if_neg hm]
  · intro n _ hn
    rw [E_apply, if_neg (fun h : i = n ∧ i = m => hn h.1.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- 左乘 `E jj` 取第 `j` 行。 -/
theorem E_mul_apply (M : Matrix (Fin p) (Fin p) K) (j l m : Fin p) :
    (E (p := p) (K := K) j j * M) l m = (if l = j then (1 : K) else 0) * M j m := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [E_apply]
    by_cases hl : l = j
    · rw [if_pos ⟨hl.symm, rfl⟩, if_pos hl]
    · rw [if_neg (fun h : j = l ∧ j = j => hl h.1.symm), if_neg hl]
  · intro n _ hn
    rw [E_apply, if_neg (fun h : j = l ∧ j = n => hn h.2.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- 夹在 `E jj` 与 `E ii` 之间：只剩 `(j,i)` 元。 -/
theorem E_conj_apply (M : Matrix (Fin p) (Fin p) K) (j i l m : Fin p) :
    (E (p := p) (K := K) j j * (M : Matrix (Fin p) (Fin p) K) * E (p := p) (K := K) i i) l m
      = (if l = j then (1 : K) else 0) * (M j i * (if m = i then (1 : K) else 0)) := by
  rw [mul_E_apply, E_mul_apply, mul_assoc]

/-- `E j i` 的条目形式（把 `∧` 拆成两个 `=`）。 -/
theorem E_apply_eq (j i l m : Fin p) :
    E (p := p) (K := K) j i l m = (if l = j then (1 : K) else 0) * (if m = i then (1 : K) else 0) := by
  rw [E_apply]
  by_cases hl : l = j
  · by_cases hm : m = i
    · rw [if_pos ⟨hl.symm, hm.symm⟩, if_pos hl, if_pos hm, mul_one]
    · rw [if_neg (fun h : j = l ∧ i = m => hm h.2.symm), if_pos hl, if_neg hm, one_mul]
  · rw [if_neg (fun h : j = l ∧ i = m => hl h.1.symm), if_neg hl, zero_mul]

/-- **第二步**：所有矩阵单位都在生成子代数里（`b ≠ 0`）。 -/
theorem mem_E (hζ : IsPrimitiveRoot ζ p) (hb : b ≠ 0) (j i : Fin p) :
    E (p := p) (K := K) j i ∈ genAlg (p := p) ζ α b := by
  have hY : Ymat (p := p) b ∈ genAlg (p := p) ζ α b := Algebra.subset_adjoin (by simp)
  have hdj : E (p := p) (K := K) j j ∈ genAlg (p := p) ζ α b := by
    rw [E_self_eq_diagonal]
    exact mem_diagonal_single hζ α b j
  have hdi : E (p := p) (K := K) i i ∈ genAlg (p := p) ζ α b := by
    rw [E_self_eq_diagonal]
    exact mem_diagonal_single hζ α b i
  by_cases hle : (i : ℕ) ≤ (j : ℕ)
  · -- `j ≥ i`：`k = j - i`，`(Y^k)_{ji} = 1`，故 `E jj * Y^k * E ii = E ji`
    have hk : (j : ℕ) - (i : ℕ) ≤ p := by have := j.isLt; omega
    have hval : (Ymat (p := p) b ^ ((j : ℕ) - (i : ℕ))) j i = 1 := by
      rw [Ymat_pow_apply (p := p) ((j : ℕ) - (i : ℕ)) hk j i]
      rw [if_pos (by omega : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)))]
    have hmem : E (p := p) (K := K) j j * Ymat (p := p) b ^ ((j : ℕ) - (i : ℕ)) * E i i
        ∈ genAlg (p := p) ζ α b :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hdj (Subalgebra.pow_mem _ hY _)) hdi
    have hEq : E (p := p) (K := K) j j * Ymat (p := p) b ^ ((j : ℕ) - (i : ℕ)) * E i i
        = E (p := p) (K := K) j i := by
      ext l m
      rw [E_conj_apply, hval, E_apply_eq, one_mul]
    rwa [hEq] at hmem
  · -- `j < i`：`k = j + p - i`，`(Y^k)_{ji} = b`，故 `E jj * Y^k * E ii = b • E ji`
    have hlt : (j : ℕ) < (i : ℕ) := Nat.lt_of_not_le hle
    have hk : (j : ℕ) + p - (i : ℕ) ≤ p := by have := i.isLt; omega
    have h1 : ¬ ((j : ℕ) = (i : ℕ) + ((j : ℕ) + p - (i : ℕ))) := by
      have := i.isLt; omega
    have h2 : (j : ℕ) + p = (i : ℕ) + ((j : ℕ) + p - (i : ℕ)) := by
      have := i.isLt; omega
    have hval : (Ymat (p := p) b ^ ((j : ℕ) + p - (i : ℕ))) j i = b := by
      rw [Ymat_pow_apply (p := p) ((j : ℕ) + p - (i : ℕ)) hk j i, if_neg h1, if_pos h2]
    have hmem : E (p := p) (K := K) j j * Ymat (p := p) b ^ ((j : ℕ) + p - (i : ℕ)) * E i i
        ∈ genAlg (p := p) ζ α b :=
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hdj (Subalgebra.pow_mem _ hY _)) hdi
    have hEq : E (p := p) (K := K) j j * Ymat (p := p) b ^ ((j : ℕ) + p - (i : ℕ)) * E i i
        = b • E (p := p) (K := K) j i := by
      ext l m
      rw [E_conj_apply, hval, Matrix.smul_apply, E_apply_eq, smul_eq_mul]
      ring
    have hbE : b • E (p := p) (K := K) j i ∈ genAlg (p := p) ζ α b := by
      rw [← hEq]
      exact hmem
    have hfinal : E (p := p) (K := K) j i
        = b⁻¹ • (b • E (p := p) (K := K) j i) := by
      rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [hfinal]
    exact Subalgebra.smul_mem _ hbE b⁻¹

/-! #### 第三步：矩阵单位张成 `M_p(K)`，故生成子代数是 `⊤` -/

theorem adjoin_eq_top (hζ : IsPrimitiveRoot ζ p) (hb : b ≠ 0) :
    genAlg (p := p) ζ α b = ⊤ := by
  refine le_antisymm le_top (fun M _ => ?_)
  have hdecomp : M = ∑ j : Fin p, ∑ i : Fin p, M j i • E (p := p) (K := K) j i := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, E_apply_eq, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [if_pos rfl, if_pos rfl, one_mul, mul_one]
      · intro m _ hm
        rw [if_pos rfl, if_neg (fun h : b = m => hm h.symm), one_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (fun h : a = j => hj h.symm), zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hdecomp]
  exact Subalgebra.sum_mem _ (fun j _ => Subalgebra.sum_mem _ (fun i _ =>
    Subalgebra.smul_mem _ (mem_E (α := α) hζ hb j i) (M j i)))

/-! ### 退化支主定理：`(a,b)_ζ ≅ M_p(K)`（`a = α^p`） -/

/-- **`(1a)` 退化支**：若 `a = α^p`，则符号代数 `(a,b)_ζ` 同构于全矩阵代数 `M_p(K)`。
这是 `(f)`（`N ⊆ S`）所缺的那一步：`a_i` 在 `E` 中成为 `p` 次幂时 `(a_i,b_i)_E ≅ M_p(E)`，
故 `E` 分裂 `D`——**不需要**循环交叉积的认同（后者只在 `a ∉ K^{×p}` 时成立）。 -/
theorem nonempty_algEquiv (hζ : IsPrimitiveRoot ζ p) (hb : b ≠ 0) (α : Kˣ) :
    Nonempty (SymbolPres.SymbolAlg K p ((α : K) ^ p) b ζ
      ≃ₐ[K] Matrix (Fin p) (Fin p) K) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h1 : Xmat (p := p) ζ α ^ p = algebraMap K (Matrix (Fin p) (Fin p) K) ((α : K) ^ p) :=
    Xmat_pow hζ α
  have h2 : Ymat (p := p) b ^ p = algebraMap K (Matrix (Fin p) (Fin p) K) b := Ymat_pow
  have h3 : Ymat (p := p) b * Xmat (p := p) ζ α
      = algebraMap K (Matrix (Fin p) (Fin p) K) ζ
        * (Xmat (p := p) ζ α * Ymat (p := p) b) := Ymat_mul_Xmat hζ b α
  have hsurj : Function.Surjective
      (SymbolPres.SymbolAlg.liftOf (p := p) ((α : K) ^ p) b ζ
        (Xmat (p := p) ζ α) (Ymat (p := p) b) h1 h2 h3) := by
    refine SymbolPres.SymbolAlg.liftOf_surjective_of_adjoin_eq_top (p := p) _ _ h1 h2 h3 ?_
    exact adjoin_eq_top hζ hb
  have hdim : Module.finrank K (Matrix (Fin p) (Fin p) K) = p * p := by
    rw [Module.finrank_matrix K K (Fin p) (Fin p), Fintype.card_fin, Module.finrank_self,
      mul_one]
  exact SymbolPres.SymbolAlg.nonempty_algEquiv_of_finrank (p := p) hp
    (Xmat (p := p) ζ α) (Ymat (p := p) b) h1 h2 h3 hsurj hdim

end SymbolMatrix