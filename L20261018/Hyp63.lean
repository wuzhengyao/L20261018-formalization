import L20261018.Hyp62
/-!
# `(1b)` 第三阶段（五）：**`Y ^ p = b`**

在 `CP = CrossedProduct (carryCocycle b)` 里，`Y = u_gen`，幂公式（`Hyp60`）给

    Y ^ p = inc (∏_{i<p} c(gen^i, gen)) · u_{gen^p}
          = inc (∏_{i<p} bL^{⌊(i+1)/p⌋}) · 1        （`carryExp_gen_pow_of_lt`）
          = inc (bL^{∑_{i<p} ⌊(i+1)/p⌋}) · 1        （`Finset.prod_pow_eq_pow_sum`）
          = inc bL · 1 = algebraMap b               （`sum_div_range`）

这就是 `(1b)` 里 `u_σ^p = b` 的余环计算。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **正规化**：`c(1,1) = 1`（carry 余环）。 -/
theorem carryFun_one_one (b : Kˣ) :
    (carryCocycle (p := p) (a := a) hζ ha b).toFun 1 1 = 1 := by
  show carryFun (p := p) (a := a) hζ ha b 1 1 = 1
  rw [carryFun, carryExp_one, add_zero, Nat.zero_div, pow_zero]

/-- **乘积**：`∏_{i<p} c(gen^i, gen) = bL`（在 `L` 中）。 -/
theorem prod_carryFun (b : Kˣ) :
    (∏ i ∈ Finset.range p,
        ((carryCocycle (p := p) (a := a) hζ ha b).toFun (gen hζ ha ^ i) (gen hζ ha) : L K p a))
      = algebraMap K (L K p a) (b : K) := by
  have hfac : ∀ i ∈ Finset.range p,
      ((carryCocycle (p := p) (a := a) hζ ha b).toFun (gen hζ ha ^ i) (gen hζ ha) : L K p a)
        = ((bL (p := p) (a := a) b : (L K p a)ˣ) : L K p a) ^ ((i + 1) / p) := by
    intro i hi
    rw [Finset.mem_range] at hi
    show (((bL (p := p) (a := a) b) ^
        ((carryExp (p := p) (a := a) hζ ha (gen hζ ha ^ i)
          + carryExp (p := p) (a := a) hζ ha (gen hζ ha)) / p) : (L K p a)ˣ) : L K p a) = _
    rw [carryExp_gen_pow_of_lt (p := p) (a := a) hζ ha i hi, carryExp_gen, Units.val_pow_eq_pow_val]
  rw [Finset.prod_congr rfl hfac, Finset.prod_pow_eq_pow_sum, sum_div_range p (Fact.out : p.Prime).pos,
    pow_one]
  rfl

/-- **`Y ^ p = algebraMap b`**（`(1b)` 的余环计算 `u_σ^p = b`）。 -/
theorem Y_pow (b : Kˣ) :
    Y (carryCocycle (p := p) (a := a) hζ ha b) (gen hζ ha) ^ p
      = algebraMap K (CrossedProduct (carryCocycle (p := p) (a := a) hζ ha b)) (b : K) := by
  rw [Y, basis_pow _ (carryFun_one_one (p := p) (a := a) hζ ha b) (gen hζ ha) p,
    prod_carryFun (p := p) (a := a) hζ ha b, gen_pow_eq_one (p := p) (a := a) hζ ha,
    basis_one_eq_one _ (carryFun_one_one (p := p) (a := a) hζ ha b), mul_one]
  exact AlgHom.commutes (CrossedProduct.inc (carryCocycle (p := p) (a := a) hζ ha b)) (b : K)

end

end SymbolCarryCocycle
