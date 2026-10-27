import L20261018.Hyp65
/-!
# `(1b)` 第三阶段（八）：`Algebra.adjoin K {X, Y} = ⊤`

* `ofAdd_one_pow_eq`：`(ofAdd 1)^n = ofAdd n`（`Multiplicative (ZMod p)` 里）；
* `gen_pow_carryExp`：**任意 `σ` 都是 `gen` 的 `carryExp σ` 次幂**（`expEquiv` 单射）；
* **`adjoin_genSet_eq_top`**：`Basis.sum_repr` 拆 `z = Σ_σ l_σ • basis σ`，
  `l • basis σ = inc l * basis σ`（`CrossedProduct.smul_def`），两块砖 ＋ 乘法封闭 ⟹ `adjoin = ⊤`。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

universe u

/-- **`(ofAdd 1)^n = ofAdd n`**。 -/
theorem ofAdd_one_pow_eq (p n : ℕ) [NeZero p] :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ^ n
      = Multiplicative.ofAdd (n : ZMod p) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero]; rfl
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ]; rfl

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  [Fintype (L K p a ≃ₐ[K] L K p a)]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **任意 `σ` 是 `gen` 的 `carryExp σ` 次幂**。 -/
theorem gen_pow_carryExp (σ : L K p a ≃ₐ[K] L K p a) :
    gen hζ ha ^ carryExp (p := p) (a := a) hζ ha σ = σ := by
  apply (expEquiv (p := p) (a := a) hζ ha).injective
  rw [map_pow, gen, MulEquiv.apply_symm_apply, ofAdd_one_pow_eq]
  show Multiplicative.ofAdd (((carryExp (p := p) (a := a) hζ ha σ : ℕ)) : ZMod p)
    = expEquiv (p := p) (a := a) hζ ha σ
  rw [carryExp, ZMod.natCast_zmod_val]
  rfl

/-- **`Algebra.adjoin K {X, Y} = ⊤`**。 -/
theorem adjoin_genSet_eq_top (b : Kˣ) :
    Algebra.adjoin K (genSet hζ ha b) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  rw [← (CrossedProduct.basis (cYC hζ ha b)).sum_repr z]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [CrossedProduct.smul_def]
  have hσ : CrossedProduct.basis (cYC hζ ha b) σ
      = CrossedProduct.basis (cYC hζ ha b) (gen hζ ha ^ carryExp (p := p) (a := a) hζ ha σ) := by
    rw [gen_pow_carryExp]
  rw [hσ]
  exact mul_mem (inc_mem_adjoin_gen (p := p) (a := a) hζ ha b _)
    (basis_mem_adjoin_gen (p := p) (a := a) hζ ha b _)

end

end SymbolCarryCocycle
