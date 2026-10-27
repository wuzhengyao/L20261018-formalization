import L20261018.Hyp64
/-!
# `(1b)` 第三阶段（七）：满射性收口 —— `Algebra.adjoin K {X, Y} = ⊤`

在 `CP = CrossedProduct (carryCocycle b)` 里：

* 任意 `inc l`（`l : L`）都在 `adjoin K {X}` 里（`Hyp64.adjoin_alpha` ＋ `inc_mem_adjoin`）；
* `basis (gen^i) = inc(∏)⁻¹ * Y^i`（`Hyp60.basis_pow` 取逆），故每个基元素都在 `adjoin K {X, Y}` 里；
* `Basis.sum_repr` 把任意元素写成 `Σ_σ inc(l_σ) * basis σ` ⟹ 全部落入 `adjoin`。
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

/-- carry 余环。 -/
noncomputable def cYC (b : Kˣ) : TwoCocycle K (L K p a) := carryCocycle hζ ha b

/-- 生成元集合 `{X, Y}`。 -/
noncomputable def genSet (b : Kˣ) : Set (CrossedProduct (cYC hζ ha b)) :=
  {X (cYC hζ ha b) (α (K := K) (p := p) (a := a)), Y (cYC hζ ha b) (gen hζ ha)}

/-- **`inc l` 在 `adjoin K {X}` 里**（对任意 `l : L`）。 -/
theorem inc_mem_adjoin_gen (b : Kˣ) (l : L K p a) :
    CrossedProduct.inc (cYC hζ ha b) l ∈ Algebra.adjoin K (genSet hζ ha b) := by
  have h : CrossedProduct.inc (cYC hζ ha b) l
      ∈ Algebra.adjoin K (Set.singleton (CrossedProduct.inc (cYC hζ ha b)
          (α (K := K) (p := p) (a := a)))) :=
    inc_mem_adjoin (p := p) (a := a) hζ ha b (by rw [adjoin_alpha]; exact trivial)
  refine Algebra.adjoin_mono ?_ h
  intro x hx
  have hx' : x = CrossedProduct.inc (cYC hζ ha b) (α (K := K) (p := p) (a := a)) :=
    Set.mem_singleton_iff.mp hx
  rw [hx']
  exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- **基元素在 `adjoin K {X, Y}` 里**。 -/
theorem basis_mem_adjoin_gen (b : Kˣ) (i : ℕ) :
    CrossedProduct.basis (cYC hζ ha b) (gen hζ ha ^ i) ∈
      Algebra.adjoin K (genSet hζ ha b) := by
  set σ := gen hζ ha with hσ
  set A := Algebra.adjoin K (genSet hζ ha b) with hA
  -- 乘积单元
  set prod : L K p a := ∏ j ∈ Finset.range i, ((cYC hζ ha b).toFun (σ ^ j) σ : L K p a) with hprod
  have h1 : (cYC hζ ha b).toFun 1 1 = 1 := carryFun_one_one (p := p) (a := a) hζ ha b
  have hp := basis_pow (cYC hζ ha b) h1 σ i
  -- `inc prod ∈ A`，故 `inc prod⁻¹ ∈ A`
  have hinc : CrossedProduct.inc (cYC hζ ha b) prod ∈ A := inc_mem_adjoin_gen (p := p) (a := a) hζ ha b prod
  have hinv : CrossedProduct.inc (cYC hζ ha b) prod⁻¹ ∈ A := inc_mem_adjoin_gen (p := p) (a := a) hζ ha b prod⁻¹
  have hY : CrossedProduct.basis (cYC hζ ha b) σ ∈ A := by
    rw [hA]
    exact Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  -- `basis (σ^i) = inc (prod⁻¹) * (basis σ)^i`
  have hprod_ne : prod ≠ 0 := by
    rw [hprod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _
  have hkey : CrossedProduct.basis (cYC hζ ha b) (σ ^ i)
      = CrossedProduct.inc (cYC hζ ha b) prod⁻¹ * CrossedProduct.basis (cYC hζ ha b) σ ^ i := by
    rw [hp, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hprod_ne, map_one, one_mul]
  rw [hkey]
  exact MulMemClass.mul_mem hinv (Subalgebra.pow_mem _ hY i)

end

end SymbolCarryCocycle
