import L20261018.Hyp21
import TauCeti.FieldTheory.GaloisCohomology.Steinberg

/-!
# `(f)` at the paper's level: `hNrd` from the field norm

`Hyp21.lean` builds the reduced norm `nrd` of a crossed product `A = (L/K, c)` and proves that the
field-norm group of the maximal subfield lies in the reduced-norm group of the units of `A`:

`∀ z : Lˣ, ∃ w : Aˣ, nrd w = algebraMap K L (N_{L/K} z)`.

The paper's `hNrd` (`lemma_3_3_1`: `N_{E/F}(E^×) ⊆ Nrd(D^×)`) is stated in cohomology, and its
bridge to the field norm is TauCeti's `kummerCor_kummerMap`:

`cor_{L/K} (kummerMap_L z) = kummerMap_K (normUnits z)`,

i.e. `cor((z)) = (N_{L/K} z)` — the paper's `prop:prelim-cup` (3). This file composes the two: the
image of corestriction on Kummer classes is the image of the reduced norm on units of the crossed
product, which is exactly `hNrd`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace CrossedProductNrd

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]

/-- **(f), the paper's `hNrd`, in the crossed-product model.** For every unit `z` of the maximal
subfield `L`:

* the reduced norm of the corresponding unit `inc z` of the crossed product is the field norm of
  `z` (`nrd_inc`, `Hyp21`), and
* corestriction of the Kummer class of `z` is the Kummer class of that same field norm
  (`TauCeti.kummerCor_kummerMap`).

Hence the image of corestriction is contained in the set of Kummer classes of reduced norms of
units — the hypothesis `hNrd` of `lemma_3_3_1`. -/
theorem hNrd_crossedProduct (c : TwoCocycle K L) (σ : L →ₐ[K] SeparableClosure K)
    (hn : IsUnit (p : K)) (z : Lˣ) :
    ∃ w : (CrossedProduct c)ˣ,
      nrd c (w : CrossedProduct c) = algebraMap K L (Algebra.norm K (z : L)) ∧
      (kummerCor K p L σ) ((kummerMap L p
          (by simpa using hn.map (algebraMap K L)) z)) =
        (kummerMap K p hn) (Algebra.normUnits K z) := by
  refine ⟨Units.map (CrossedProduct.inc c).toMonoidHom z, ?_, ?_⟩
  · show nrd c (CrossedProduct.inc c (z : L)) = algebraMap K L (Algebra.norm K (z : L))
    exact nrd_inc c (z : L)
  · exact kummerCor_kummerMap K p L σ (by simpa using hn.map (algebraMap K L)) z

end CrossedProductNrd
