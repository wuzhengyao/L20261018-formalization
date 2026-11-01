import L20261018.Ch2.Hensel.Valuation.Step011_uniformizer_clear_denominators

/-!
# R1029（路径 A · **A1′·2·b·iv（二）**）：坐标分解 `x = Σ_{i<p} aᵢ sⁱ`

模型 `L = F[X]/(X^p − π)` 里每个元素都有唯一坐标 `aᵢ`（`i < p`）。本轮走**多项式除法**路线
（`modByMonic` ＋ `as_sum_range'`），**绕开** `PowerBasis` 的 `Fin pb.dim` 重索引问题：

* `mk f g = mk f (g %ₘ f)`（因 `mk f f = 0`）；
* `(g %ₘ f).natDegree < p`（`degree_modByMonic_lt` ＋ `natDegree_X_pow_sub_C`）；
* `g %ₘ f = Σ_{i<p} monomial i (coeff i)`（`as_sum_range'`）；
* `mk f (monomial i c) = of c * s^i`。

| 声明 | 内容 |
|---|---|
| **`exists_coeff_adjoinRoot`** | `∀ x, ∃ a : ℕ → F, x = Σ_{i<p} aᵢ • sⁱ` |

> 下一轮：把本件 ＋ `Hyp170` ＋ `Hyp175`（单调性，取 max）＋ `Hyp174.root_pow_mul` 合成
> 「`∃ n, s^n x` 的系数全在 `𝒪_F`」。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel Polynomial

namespace L20261018

section Coords

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **坐标分解**：模型里每个元素都是 `Σ_{i<p} aᵢ sⁱ`。 -/
theorem exists_coeff_adjoinRoot (π : Fˣ) (x : AdjoinRoot (X ^ p - C (π : F))) :
    ∃ a : ℕ → F, x = ∑ i ∈ Finset.range p,
      a i • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i := by
  obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective x
  have hmonic : (X ^ p - C (π : F)).Monic :=
    monic_X_pow_sub_C _ (Fact.out : p.Prime).pos.ne'
  -- 1. `mk f g = mk f (g %ₘ f)`
  have hmod : AdjoinRoot.mk (X ^ p - C (π : F)) g
      = AdjoinRoot.mk (X ^ p - C (π : F)) (g %ₘ (X ^ p - C (π : F))) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div g (X ^ p - C (π : F))]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  -- 2. 次数界 `natDegree (g %ₘ f) < p`
  have hne_f : (X ^ p - C (π : F)) ≠ 0 := by
    intro h
    have hd := congrArg (fun f : F[X] => f.natDegree) h
    rw [natDegree_X_pow_sub_C, natDegree_zero] at hd
    exact (Fact.out : p.Prime).ne_zero hd
  have hdegf : (X ^ p - C (π : F)).degree = (p : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hne_f, natDegree_X_pow_sub_C]
  have hdeg : (g %ₘ (X ^ p - C (π : F))).natDegree < p := by
    by_cases hzero : g %ₘ (X ^ p - C (π : F)) = 0
    · rw [hzero, Polynomial.natDegree_zero]
      exact (Fact.out : p.Prime).pos
    · rw [Polynomial.natDegree_lt_iff_degree_lt hzero]
      have hlt := Polynomial.degree_modByMonic_lt g hmonic
      rwa [hdegf] at hlt
  -- 3. 对一般 `r`（`natDegree < p`）：`mk f r = Σ_{i<p} r.coeff i • sⁱ`
  have key : ∀ r : F[X], r.natDegree < p →
      AdjoinRoot.mk (X ^ p - C (π : F)) r
        = ∑ i ∈ Finset.range p, (r.coeff i) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i := by
    intro r hr
    have hterm : ∀ i : ℕ, AdjoinRoot.mk (X ^ p - C (π : F)) (Polynomial.monomial i (r.coeff i))
        = (r.coeff i) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i := by
      intro i
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C,
        AdjoinRoot.mk_X, Algebra.smul_def]
      rfl
    have hsum' : r = ∑ i ∈ Finset.range p, Polynomial.monomial i (r.coeff i) :=
      Polynomial.as_sum_range' r p hr
    conv_lhs => rw [hsum']
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  refine ⟨fun i => (g %ₘ (X ^ p - C (π : F))).coeff i, ?_⟩
  rw [← hg, hmod]
  exact key (g %ₘ (X ^ p - C (π : F))) hdeg

end Coords

end L20261018

#print axioms L20261018.exists_coeff_adjoinRoot
