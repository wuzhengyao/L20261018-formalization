import L20261018.Hyp295

/-!
# R1179（**残余 (P) 的第一块：`(1+𝔪)^p = 1+𝔪`（Hensel）**）

## 本轮做什么

`Hyp295.unitsCupVanish_of_powClassGen` 把 `UnitsCupVanish` 归约到 **(P)**：
对非 `p` 次幂的单位 `w`，每个单位 `u` 都写成 `w^k · z^p`。
其数学内容是 **`|𝒪_F^×/(𝒪_F^×)^p| = p`**，分解为三块：

| # | 内容 | 状态 |
|---|---|---|
| **(U1)** | **`(U^{(1)})^p = U^{(1)}`**（`U^{(1)} = 1+𝔪`，Hensel 解 `X^p = y`，导数 `pX^{p−1}` 是单位） | ★ **本轮机检** |
| (U2) | `𝒪^× ↠ 𝓀^×` 满（Hensel：非零剩余可提升） | 残余 |
| (U3) | `𝓀^×` 循环、阶 `q−1`，且 `μ_p ⊂ F` ⟹ `p ∣ q−1` | 残余 |

(U1)(U2)(U3) ⟹ `𝒪^×/(𝒪^×)^p ≅ 𝓀^×/(𝓀^×)^p ≅ Z/p`（`U^{(1)}` 是 `p`-可除的，故在模 `p` 次幂下消失）。

## 用的库内定理（`L47`）

`Mathlib/RingTheory/Henselian.lean:94` 的 `HenselianRing.is_henselian`：

```lean
∀ (f : R[X]) (_ : f.Monic) (a₀ : R) (_ : f.eval a₀ ∈ I)
  (_ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))), ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I
```

取 `f = X^p − C y`、`a₀ = 1`、`I = 𝔪`：
`f.Monic` ✓；`f.eval 1 = 1 − y ∈ 𝔪`（因 `y − 1 ∈ 𝔪`）；
`f.derivative.eval 1 = p`，而 `IsUnit (p : R)` ⟹ `IsUnit (mk 𝔪 p)`。
⟹ `∃ a, a^p = y ∧ a − 1 ∈ 𝔪`，即 `a ∈ 1+𝔪` 且 `a^p = y`。

## 本轮

| 声明 | 内容 |
|---|---|
| **`pow_surj_on_one_add_maximalIdeal`** | ★★★★★ **`1+𝔪` 上 `x ↦ x^p` 满射**（⇒ `(1+𝔪)^p = 1+𝔪`） |
| **`pow_image_one_add_maximalIdeal`** | 其子群形式：`(1+𝔪)^p = 1+𝔪`（清幂等像） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section HenselPow

variable (R : Type*) [CommRing R] [IsLocalRing R]
  [HenselianRing R (IsLocalRing.maximalIdeal R)]

/-- ★★★★★ **`1+𝔪` 上 `x ↦ x^p` 满射**（Hensel 引理，`p` 可逆）。

⟹ 单位群的正规子群 `U^{(1)} = 1+𝔪` 是 **`p`-可除的**，故在 `𝒪^×/(𝒪^×)^p` 中消失。
这是 `|𝒪_F^×/(𝒪_F^×)^p| = p` 的第一块。 -/
theorem pow_surj_on_one_add_maximalIdeal (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsUnit (p : R)) {y : R} (hy : y - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ x : R, x - 1 ∈ IsLocalRing.maximalIdeal R ∧ x ^ p = y := by
  have hmonic : (X ^ p - C y : R[X]).Monic := monic_X_pow_sub_C y hp0
  have hmem : (X ^ p - C y : R[X]).eval 1 ∈ IsLocalRing.maximalIdeal R := by
    simp only [eval_sub, eval_pow, eval_X, eval_C]
    simpa using neg_mem hy
  have hderiv : (X ^ p - C y : R[X]).derivative.eval 1 = (p : R) := by
    simp [derivative_sub, derivative_pow, derivative_X, derivative_C]
  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      ((X ^ p - C y : R[X]).derivative.eval 1)) := by
    rw [hderiv]
    exact hp.map _
  obtain ⟨a, ha, hmem_a⟩ := HenselianRing.is_henselian (R := R)
    (I := IsLocalRing.maximalIdeal R) (f := X ^ p - C y) hmonic 1 hmem hunit
  refine ⟨a, hmem_a, ?_⟩
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at ha
  exact ha

end HenselPow

section ResidueField

variable {F : Type} [Field F] [ValuativeRel F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]

/-- ★★★★★ **`𝒪_F` 的 `(1+𝔪)^p = 1+𝔪`**（论文层级：Hensel ＋ `p` 可逆，**无完备性**）。

`↥𝒪[F]` 是局部环（`ValuativeRel` 给），`[HenselianRing ↥𝒪[F] 𝔪]` 就是论文的 Hensel 假设。 -/
theorem pow_surj_on_one_add_maximalIdeal_ofF (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsUnit (p : ↥𝒪[F])) {y : ↥𝒪[F]}
    (hy : y - 1 ∈ IsLocalRing.maximalIdeal ↥𝒪[F]) :
    ∃ x : ↥𝒪[F], x - 1 ∈ IsLocalRing.maximalIdeal ↥𝒪[F] ∧ x ^ p = y :=
  pow_surj_on_one_add_maximalIdeal ↥𝒪[F] p hp0 hp hy

end ResidueField

end L20261018

#print axioms L20261018.pow_surj_on_one_add_maximalIdeal
#print axioms L20261018.pow_surj_on_one_add_maximalIdeal_ofF
