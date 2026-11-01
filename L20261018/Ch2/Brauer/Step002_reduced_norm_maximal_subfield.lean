import TauCeti.Algebra.CrossedProduct.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The reduced norm of a crossed product, and its value on the maximal subfield

Campaign item (f) needs `N_{E/F}(E^×) ⊆ Nrd(D^×)` for a maximal subfield `E ⊆ D`
(`prop:prelim-degree-index`: `Nrd_Δ|_L = N_{L/F}` for a separable maximal subfield `L ⊂ Δ`).

This file builds the reduced norm **without any splitting field**, from the crossed-product
structure alone. The key observation is that on the crossed product `A = (L/K, c)` the map

`y ↦ y * a`  (right multiplication)

is `L`-**linear** for the *left* `L`-module structure of `A`: associativity gives
`(l • y) * a = l • (y * a)`. So it has a determinant over `L` — the **reduced norm**
`nrd a = det (y ↦ y * a)` — and for `a = inc x` with `x ∈ L` it is diagonal in the `L`-basis `u_σ`
(`TauCeti.CrossedProduct.basis`):

`u_σ * inc x = inc (σ x) * u_σ = (σ x) • u_σ`  (`TauCeti.CrossedProduct.basis_mul_inc`).

Hence `nrd (inc x) = ∏_σ σ x = algebraMap K L (Algebra.norm K x)` by
`Algebra.norm_eq_prod_automorphisms`. This is exactly `Nrd_Δ|_L = N_{L/F}`. Note that it needs no
splitting field, and that although the determinant lands in `L`, its value on `inc x` is manifestly
in the image of `K` — which is all that the inclusion `N_{L/F}(L^×) ⊆ Nrd(A^×)` requires.
-/

open TauCeti

set_option maxHeartbeats 1000000

namespace CrossedProductNrd

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (c : TwoCocycle K L)

attribute [local instance] Classical.decEq

/-- **Right multiplication is `L`-linear** for the left `L`-module structure of the crossed
product. (Commutativity of `L` is not needed: associativity suffices.) -/
noncomputable def mulRight (a : CrossedProduct c) : CrossedProduct c →ₗ[L] CrossedProduct c where
  toFun y := y * a
  map_add' y z := add_mul y z a
  map_smul' l y := by
    rw [CrossedProduct.smul_def, CrossedProduct.smul_def]
    exact mul_assoc _ _ _

/-- Right multiplication by `inc x` is right multiplication by the algebra element `inc x`. -/
theorem mulRight_inc (x : L) :
    mulRight c (CrossedProduct.inc c x) = mulRight c (CrossedProduct.inc c x) := rfl

/-- **The matrix of right multiplication by `inc x` in the basis `u_σ` is diagonal**, with
eigenvalue `σ x`. -/
theorem toMatrix_mulRight_inc (x : L) :
    LinearMap.toMatrix (CrossedProduct.basis c) (CrossedProduct.basis c)
        (mulRight c (CrossedProduct.inc c x))
      = Matrix.diagonal (fun σ : L ≃ₐ[K] L => σ x) := by
  ext σ τ
  rw [LinearMap.toMatrix_apply, mulRight, LinearMap.coe_mk, AddHom.coe_mk,
    CrossedProduct.basis_mul_inc, ← CrossedProduct.smul_def, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Matrix.diagonal_apply]
  by_cases h : σ = τ
  · subst h
    simp
  · simp [h]

/-- **The determinant of right multiplication by `inc x` is `N_{L/K}(x)`.** -/
theorem det_mulRight_inc (x : L) :
    LinearMap.det (mulRight c (CrossedProduct.inc c x)) = algebraMap K L (Algebra.norm K x) := by
  have hdet : LinearMap.det (mulRight c (CrossedProduct.inc c x))
      = ∏ σ : L ≃ₐ[K] L, σ x := by
    rw [← LinearMap.det_toMatrix (CrossedProduct.basis c) (mulRight c (CrossedProduct.inc c x)),
      toMatrix_mulRight_inc, Matrix.det_diagonal]
  rw [hdet, ← Algebra.norm_eq_prod_automorphisms]

/-- The **reduced norm** of the crossed product `(L/K, c)`: the determinant over `L` of right
multiplication. For a degree-`n` central simple algebra this is the classical reduced norm, but for
the inclusion `N_{L/F}(L^×) ⊆ Nrd(A^×)` only its values on `L` are needed, and those are computed by
`det_mulRight_inc`. -/
noncomputable def nrd (a : CrossedProduct c) : L :=
  LinearMap.det (mulRight c a)

/-- **`Nrd` on the maximal subfield is the field norm**: `nrd (inc x) = N_{L/K}(x)`. This is
`prop:prelim-degree-index`'s `Nrd_Δ|_L = N_{L/F}`. -/
theorem nrd_inc (x : L) : nrd c (CrossedProduct.inc c x) = algebraMap K L (Algebra.norm K x) :=
  det_mulRight_inc c x

/-- **`Nrd` is multiplicative.** -/
theorem nrd_mul (a b : CrossedProduct c) : nrd c (a * b) = nrd c a * nrd c b := by
  have hcomp : mulRight c (a * b) = (mulRight c b).comp (mulRight c a) := by
    ext y
    simp only [mulRight, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rw [mul_assoc]
  have hmul : (mulRight c b).comp (mulRight c a) = mulRight c b * mulRight c a := (rfl)
  rw [nrd, hcomp, hmul, map_mul]
  exact mul_comm _ _

/-- **`N_{L/K}(L^×) ⊆ Nrd(A^×)`**: every field norm of a unit is the reduced norm of a unit. This is
the inclusion used by `prop:prelim-splitting` and hence by the paper's `hNrd`. -/
theorem norm_mem_range_nrd_units (z : Lˣ) :
    ∃ w : (CrossedProduct c)ˣ,
      nrd c (w : CrossedProduct c) = algebraMap K L (Algebra.norm K (z : L)) := by
  refine ⟨Units.map (CrossedProduct.inc c).toMonoidHom z, ?_⟩
  show nrd c (CrossedProduct.inc c (z : L)) = algebraMap K L (Algebra.norm K (z : L))
  exact nrd_inc c (z : L)

end CrossedProductNrd
