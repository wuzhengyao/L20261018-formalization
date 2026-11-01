import L20261018.Hyp19

/-!
# 第 4 章 T1：`lem:basis-change`（第一槽基变换）

论文 `raw/L20261018.tex:1571`（`\label{lem:basis-change}`）：

> 设 $p$ 为奇素数，$F$ 为特征 $0$ 且含有 $\mu_p$ 的域。取 $a_i,b_i\in F^\times$，记
> $\alpha_i=(a_i)$、$\beta_i=(b_i)\in H^1(F,\mu_p)$ … 对任意 $A\in\operatorname{GL}_2(\Fp)$，
> 令 $\alpha'=A\alpha$、$\beta'=(A^{-1})^T\beta$，则
> $\alpha_1\cup\beta_1+\alpha_2\cup\beta_2=\alpha'_1\cup\beta'_1+\alpha'_2\cup\beta'_2$。

论文的证明（`:1581–1597`）只用**双线性**与 $BA=I_2$（$B=A^{-1}$）：

$$\sum_i\alpha_i'\cup\beta_i'=\sum_{i,j,k}A_{ij}B_{ki}\,\alpha_j\cup\beta_k
=\sum_{j,k}\Bigl(\sum_i B_{ki}A_{ij}\Bigr)\alpha_j\cup\beta_k=\sum_j\alpha_j\cup\beta_j.$$

本文件照该证明，分两层：

* **抽象层**（`cup_sum_sum`／`cup_basis_change`）：对**任意** $k$-双线性 `cup` 成立
  ——不需要斜对称、不需要非退化（论文证明也没用）。这是论文证明真正用到的东西；
* **论文层**（`basis_change_kummer`）：`cup = GaloBase.cup`、`α_j = (a_j)`、`β_l = (b_l)`，
  即论文的真实对象，只带论文自身的假设（`p` 素、`μ_p ⊂ F`、`char F ∤ p`）。

**陈述保真注**：论文陈述里的 `α₁,α₂` 线性无关与 `ind(D)=p²` **本条引理证明不用**，Lean 版故不加
（前提更弱 ⟹ 结论更强，方向正确；这是「Lean 版比论文版更一般」，不是缩范围）。

## 记法层踩坑（L49）

`cup (∑ j, c j • x j) (∑ l, d l • y l)` 里 `cup` 是 `V →ₗ[k] V →ₗ[k] H2`，故：
* `rw [map_sum]` 会匹配**最外层**（即先展开第二槽），不是先展开第一槽；
* `rw [LinearMap.map_smul]` 同样先匹配最外层（第二槽）——**必须用带第二参数的
  `LinearMap.map_sum₂`／`LinearMap.map_smul₂`** 才能唯一确定是第一槽。
-/

open Matrix

set_option maxHeartbeats 2000000

namespace L20261018

/-! ## 1. 抽象层 -/

section Abstract

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- 双线性展开（论文 `:1582` 的第一行）：
`cup (∑_j c_j • x_j) (∑_l d_l • y_l) = ∑_j ∑_l (c_j * d_l) • cup (x_j) (y_l)`。 -/
theorem cup_sum_sum (cup : V →ₗ[k] V →ₗ[k] H2) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → k) (d : κ → k) (x : ι → V) (y : κ → V) :
    cup (∑ j, c j • x j) (∑ l, d l • y l)
      = ∑ j, ∑ l, (c j * d l) • cup (x j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearMap.map_smul₂]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.map_smul, smul_smul]

/-- **`lem:basis-change` 的线性代数内核**：对任意双线性 `cup` 与任意
`A : Matrix (Fin 2) (Fin 2) k`（`A.det` 为单位），第一槽作 `A`、第二槽作 `(A⁻¹)ᵀ`
的变换不改变 `∑_i α_i ∪ β_i`。

论文 `:1582–1595` 的原证明：全式展成 `∑_{i,j,l} A_{ij}(A⁻¹)_{li} α_j∪β_l`，
对调求和，再用 `A⁻¹A = 1` 得 `∑_i (A⁻¹)_{li}A_{ij} = δ_{jl}`。 -/
-- @source file=raw/L20261018.tex locator=label:lem:basis-change quote="\alpha_1\cup\beta_1+\alpha_2\cup\beta_2=\alpha'_1\cup\beta'_1+\alpha'_2\cup\beta'_2."
theorem cup_basis_change (cup : V →ₗ[k] V →ₗ[k] H2) (A : Matrix (Fin 2) (Fin 2) k)
    (hA : IsUnit A.det) (α β : Fin 2 → V) :
    (∑ i, cup (∑ j, A i j • α j) (∑ l, A⁻¹ l i • β l))
      = ∑ j, cup (α j) (β j) := by
  -- 系数恒等式：`∑_i (A⁻¹)_{li} A_{ij} = δ_{jl}`（由 `A⁻¹ * A = 1`，论文 `:1592`）
  have hcoef : ∀ j l : Fin 2, (∑ i, A⁻¹ l i * A i j) = if j = l then (1 : k) else 0 := by
    intro j l
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul A hA) l) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [h]
    by_cases hjl : j = l
    · subst hjl; simp
    · have hlj : ¬ (l = j) := fun h' => hjl h'.symm
      simp [hjl, hlj]
  -- 对调求和：`∑_i ∑_j ∑_l f i j l = ∑_j ∑_l ∑_i f i j l`
  have hswap : (∑ i, ∑ j, ∑ l, (A i j * A⁻¹ l i) • cup (α j) (β l))
      = ∑ j, ∑ l, ∑ i, (A⁻¹ l i * A i j) • cup (α j) (β l) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_comm]
  calc (∑ i, cup (∑ j, A i j • α j) (∑ l, A⁻¹ l i • β l))
      = ∑ i, ∑ j, ∑ l, (A i j * A⁻¹ l i) • cup (α j) (β l) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact cup_sum_sum cup (fun j => A i j) (fun l => A⁻¹ l i) α β
    _ = ∑ j, ∑ l, (∑ i, A⁻¹ l i * A i j) • cup (α j) (β l) := by
        rw [hswap]
        simp only [Finset.sum_smul]
    _ = ∑ j, cup (α j) (β j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hcj : ∀ l, (∑ i, A⁻¹ l i * A i j) = if j = l then (1 : k) else 0 :=
          fun l => hcoef j l
        simp only [hcj]
        rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hlj
          have hne : ¬ (j = l) := fun h => hlj h.symm
          simp [hne]
        · intro hj
          exact absurd (Finset.mem_univ j) hj

end Abstract

/-! ## 2. 论文层（真实对象） -/

section Paper

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`lem:basis-change`（论文真实对象）**：`α_j = (a_j)`、`β_l = (b_l)` 是
`Fˣ → H¹(F,μ_p)` 的 Kummer 类，`cup = GaloBase.cup`。

论文陈述额外假设的 `α₁,α₂` 线性无关、`D` 的指数 $p^2$ **未被本条引理使用**，故不列入
（前提更弱）。 -/
-- @source file=raw/L20261018.tex locator=label:lem:basis-change quote="\alpha_1\cup\beta_1+\alpha_2\cup\beta_2=\alpha'_1\cup\beta'_1+\alpha'_2\cup\beta'_2."
theorem basis_change_kummer (hp : IsUnit (p : F))
    (a b : Fin 2 → Fˣ) (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (hA : IsUnit A.det) :
    (∑ i, GaloBase.cup (K := F) (p := p)
        (∑ j, A i j • KummerBridge.kummerClass F p hp (a j))
        (∑ l, A⁻¹ l i • KummerBridge.kummerClass F p hp (b l)))
      = ∑ j, GaloBase.cup (K := F) (p := p)
          (KummerBridge.kummerClass F p hp (a j)) (KummerBridge.kummerClass F p hp (b j)) :=
  cup_basis_change (GaloBase.cup (K := F) (p := p)) A hA _ _

end Paper

end L20261018

#print axioms L20261018.cup_sum_sum
#print axioms L20261018.cup_basis_change
#print axioms L20261018.basis_change_kummer
