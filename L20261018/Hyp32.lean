import L20261018.Hyp25
import TauCeti.Algebra.CrossedProduct.BrauerClass
import TauCeti.Algebra.CentralSimple.SkolemNoether

/-!
# `(f)` gap 2: the reduced norm is independent of the presentation

`Hyp21` defines the reduced norm of a crossed product `A = (L/K, c)` as the `L`-determinant of right
multiplication, and `Hyp25` proves it is invariant under **`L`-linear** algebra isomorphisms (in
particular under change of cocycle representative). The paper's `prop:prelim-splitting` (2) asks for
more: Gille–Szamuely, *Central Simple Algebras and Galois Cohomology*, **Prop. 2.6.3** (together with
Construction 2.6.4) asserts that `Nrd` does not depend on the splitting field or the matrix
representation — i.e. it is invariant under **arbitrary** `K`-algebra isomorphisms, not just the ones
preserving the `L`-module structure.

GS prove this by Galois descent (the `det` on `M_n(K)` is `G`-compatible, hence descends). This file
takes a different route, which is exactly the point: **Skolem–Noether replaces the descent**. Every
`K`-algebra isomorphism between finite-dimensional central simple algebras is conjugation by a unit
(`TauCeti.skolemNoether`), and the `L`-valued determinant is multiplicative (`Hyp21.nrd_mul`) while
`L` is commutative, so conjugation does not change it. No honest change of presentation can,
therefore, move `Nrd`.

## Main results

* `CrossedProductNrd.nrd_one`, `nrd_inv_unit`, `nrd_conj_unit`: `nrd` is a multiplicative map on
  units and is conjugation-invariant.
* `CrossedProductNrd.nrd_algEquiv_self`: **every `K`-algebra automorphism** of a crossed product
  preserves `nrd` — this is the `L`-linear hypothesis of `Hyp25` removed in the automorphism case.
* `CrossedProductNrd.nrd_algEquiv_of_cohomologous`: for cohomologous cocycles (i.e. for two
  presentations of the same Brauer class over the same `L`), **every** `K`-algebra isomorphism
  `CrossedProduct w ≃ₐ[K] CrossedProduct z` preserves `nrd`. This is GS Prop. 2.6.3 (2)'s
  "independence of the choice of splitting field and matrix representation" in the form the paper's
  `hNrd` consumes.
* `CrossedProductNrd.exists_nrd_eq_norm_of_algEquiv`: hence the inclusion
  `N_{L/K}(L^×) ⊆ Nrd(A^×)` (`Hyp21.norm_mem_range_nrd_units`) holds for **any** `K`-algebra model
  of the class, not just for one chosen crossed-product presentation.

## Reconnaissance note (CLAUDE.md rule 23 / L46)

Searched by content (not by name) for `reduced norm`, `reducedNorm`, `nrd`, `CSA`, `involution`,
`Witt` across `raw/TauCeti` (15,662 files), `raw/openai-math-formalized-algebra` (31,863),
`raw/alphaproof-nexus-formalized` (66), `raw/fermats-last-theorem` (69,992) and Mathlib
(`~/mathlib4/Mathlib`, 8,631 files): **no library has a general reduced norm**. The only occurrences
are degree-`2` (quaternion) ones — `TauCeti.QuaternionAlgebra.normForm_eq_of_algEquiv` and
`raw/fermats-last-theorem/Definitions/Def_QuaternionAlgebra_ReducedNorm.lean`. So gap 2 has to be
built here, on top of `TauCeti`'s Skolem–Noether.
-/

open TauCeti

set_option maxHeartbeats 1000000
-- `nrd` needs the `Module.Free`/`Module.Finite` instances for `CrossedProduct c`, which come from
-- `[FiniteDimensional K L] [IsGalois K L]`; the linter's syntactic check does not see that use.
set_option linter.unusedSectionVars false

namespace CrossedProductNrd

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable {z w : TwoCocycle K L}

/-- The reduced norm of `1` is `1`. -/
theorem nrd_one (c : TwoCocycle K L) : nrd c (1 : CrossedProduct c) = 1 := by
  show LinearMap.det (mulRight c 1) = 1
  rw [show mulRight c (1 : CrossedProduct c) = LinearMap.id from ?_, LinearMap.det_id]
  ext y
  simp [mulRight]

/-- The reduced norm of an inverse unit is the inverse of the reduced norm. -/
theorem nrd_inv_unit (c : TwoCocycle K L) (u : (CrossedProduct c)ˣ) :
    nrd c ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c) = (nrd c (u : CrossedProduct c))⁻¹ := by
  have h : nrd c (u : CrossedProduct c) *
      nrd c ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c) = 1 := by
    rw [← nrd_mul,
      show (u : CrossedProduct c) * ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c) = 1 from by
        simp,
      nrd_one]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- **Conjugation by a unit preserves the reduced norm.** `nrd` is multiplicative (`nrd_mul`) and
takes values in the commutative ring `L`, so the two factors cancel. -/
theorem nrd_conj_unit (c : TwoCocycle K L) (u : (CrossedProduct c)ˣ) (a : CrossedProduct c) :
    nrd c ((u : CrossedProduct c) * a * ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c))
      = nrd c a := by
  have hu : nrd c (u : CrossedProduct c) ≠ 0 := by
    have h1 : nrd c (u : CrossedProduct c) *
        nrd c ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c) = 1 := by
      rw [← nrd_mul,
        show (u : CrossedProduct c) * ((u⁻¹ : (CrossedProduct c)ˣ) : CrossedProduct c) = 1 from by
          simp,
        nrd_one]
    exact left_ne_zero_of_mul_eq_one h1
  rw [nrd_mul, nrd_mul, nrd_inv_unit, mul_right_comm, mul_inv_cancel₀ hu, one_mul]

/-- **Every `K`-algebra automorphism of a crossed product preserves the reduced norm.** By
Skolem–Noether (`TauCeti.exists_unit_conj_of_algEquiv`) every such automorphism is conjugation by a
unit, and conjugation is invisible to `nrd` (`nrd_conj_unit`). -/
theorem nrd_algEquiv_self (c : TwoCocycle K L) (e : CrossedProduct c ≃ₐ[K] CrossedProduct c)
    (a : CrossedProduct c) : nrd c (e a) = nrd c a := by
  obtain ⟨u, hu⟩ := exists_unit_conj_of_algEquiv K e
  rw [hu a]
  exact nrd_conj_unit c u a

/-- **(f) gap 2 closed: the reduced norm is independent of the presentation.** For cohomologous
cocycles `z`, `w` on the same Galois extension `L/K` — i.e. for two presentations of the same Brauer
class — **every** `K`-algebra isomorphism `φ : CrossedProduct w ≃ₐ[K] CrossedProduct z` preserves the
reduced norm.

This removes the `L`-linearity hypothesis of `Hyp25.nrd_algEquiv`: the cohomologous model isomorphism
`CrossedProduct.algEquivOfCoboundary` is `L`-linear (so `Hyp25` applies to it), and any other
isomorphism differs from it by an automorphism of `CrossedProduct w`, which Skolem–Noether makes
inner, hence `nrd`-invisible (`nrd_algEquiv_self`). -/
theorem nrd_algEquiv_of_cohomologous (hzw : z.Cohomologous w)
    (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z) (a : CrossedProduct w) :
    nrd z (φ a) = nrd w a := by
  obtain ⟨b, hb⟩ := hzw
  obtain ⟨u, hu⟩ := skolemNoether K
    (f := (CrossedProduct.algEquivOfCoboundary b hb : CrossedProduct w →ₐ[K] CrossedProduct z))
    (g := (φ : CrossedProduct w →ₐ[K] CrossedProduct z))
  have hua : φ a = (u : CrossedProduct z) * (CrossedProduct.algEquivOfCoboundary b hb a) *
      ((u⁻¹ : (CrossedProduct z)ˣ) : CrossedProduct z) := hu a
  rw [hua, nrd_conj_unit]
  exact nrd_algEquivOfCoboundary b hb a

/-- **The reduced-norm image on units is unchanged by any `K`-algebra isomorphism** between
cohomologous crossed products. -/
theorem nrd_image_eq_of_algEquiv (hzw : z.Cohomologous w)
    (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z) :
    (Set.range fun u : (CrossedProduct w)ˣ => nrd w (u : CrossedProduct w))
      = (Set.range fun v : (CrossedProduct z)ˣ => nrd z (v : CrossedProduct z)) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨Units.map φ.toMonoidHom u, nrd_algEquiv_of_cohomologous hzw φ (u : CrossedProduct w)⟩
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map φ.symm.toMonoidHom v, ?_⟩
    show nrd w (φ.symm (v : CrossedProduct z)) = nrd z (v : CrossedProduct z)
    rw [← nrd_algEquiv_of_cohomologous hzw φ (φ.symm (v : CrossedProduct z)),
      AlgEquiv.apply_symm_apply]

/-- **(f) in the sharpest presentation-free form.** The field norm of every unit of the maximal
subfield `L` is the reduced norm of a unit of **every** crossed-product presentation of the class,
in *any* chosen presentation: `Hyp21.norm_mem_range_nrd_units` transported along an arbitrary
`K`-algebra isomorphism `φ`, using `nrd_algEquiv_of_cohomologous`. -/
theorem exists_nrd_eq_norm_of_algEquiv (hzw : z.Cohomologous w)
    (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z) (y : Lˣ) :
    ∃ v : (CrossedProduct z)ˣ,
      nrd z (v : CrossedProduct z) = algebraMap K L (Algebra.norm K (y : L)) := by
  obtain ⟨u, hu⟩ := norm_mem_range_nrd_units w y
  exact ⟨Units.map φ.toMonoidHom u, by
    show nrd z (φ (u : CrossedProduct w)) = algebraMap K L (Algebra.norm K (y : L))
    rw [nrd_algEquiv_of_cohomologous hzw φ (u : CrossedProduct w), hu]⟩

end CrossedProductNrd
