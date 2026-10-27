import L20261018.Hyp21
import TauCeti.Algebra.CrossedProduct.Cohomologous

/-!
# `(f)`: the reduced-norm image depends only on the cohomology class of the cocycle

`Hyp21.lean` defines the reduced norm of a crossed product `A = (L/K, c)` as the `L`-determinant of
right multiplication, and proves `nrd (inc x) = N_{L/K}(x)`.

The paper's `prop:prelim-splitting` (2) says the reduced norm is *independent of the choice of
splitting field and matrix representation* (Gille–Szamuely, *Central Simple Algebras and Galois
Cohomology*, §2.6 / Prop. 2.6.3). This file proves the corresponding invariance **within the
crossed-product setting**: cohomologous cocycles give crossed products with the same reduced-norm
image. The mechanism is TauCeti's `CrossedProduct.algEquivOfCoboundary`, which is `L`-linear
(`algEquivOfCoboundary_smul`) — so it conjugates the right-multiplication operators, and conjugation
does not change a determinant (`LinearMap.det_conj`).

Consequently the inclusion `N_{L/K}(L^×) ⊆ nrd(A^×)` (`Hyp21`) holds for **every** representative of
the Brauer class, not just one chosen cocycle.
-/

open TauCeti

set_option maxHeartbeats 1000000

namespace CrossedProductNrd

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable {z w : TwoCocycle K L}

/-- An `L`-linear algebra equivalence of crossed products, as an `L`-linear equivalence. -/
noncomputable def algEquivToLinearEquiv (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z)
    (hφ : ∀ (x : L) (a : CrossedProduct w), φ (x • a) = x • φ a) :
    CrossedProduct w ≃ₗ[L] CrossedProduct z where
  toFun := φ
  map_add' := fun a b => map_add φ a b
  map_smul' := hφ
  invFun := φ.symm
  left_inv := fun a => φ.symm_apply_apply a
  right_inv := fun a => φ.apply_symm_apply a

/-- **Conjugating right multiplication**: for an `L`-linear algebra equivalence `φ`, right
multiplication by `a` on the source is conjugate to right multiplication by `φ a` on the target. -/
theorem mulRight_conj (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z)
    (hφ : ∀ (x : L) (a : CrossedProduct w), φ (x • a) = x • φ a) (a : CrossedProduct w) :
    ((algEquivToLinearEquiv φ hφ : CrossedProduct w →ₗ[L] CrossedProduct z) ∘ₗ mulRight w a ∘ₗ
        (((algEquivToLinearEquiv φ hφ).symm : CrossedProduct z ≃ₗ[L] CrossedProduct w) :
          CrossedProduct z →ₗ[L] CrossedProduct w))
      = mulRight z (φ a) := by
  apply LinearMap.ext
  intro y
  show φ ((algEquivToLinearEquiv φ hφ).invFun y * a) = y * φ a
  rw [show (algEquivToLinearEquiv φ hφ).invFun y = φ.symm y from rfl, map_mul,
    AlgEquiv.apply_symm_apply]

/-- **The reduced norm is invariant under `L`-linear isomorphism of crossed products**: `φ`
conjugates the right-multiplication operators, and `LinearMap.det_conj` says conjugation does not
change a determinant. -/
theorem nrd_algEquiv (φ : CrossedProduct w ≃ₐ[K] CrossedProduct z)
    (hφ : ∀ (x : L) (a : CrossedProduct w), φ (x • a) = x • φ a) (a : CrossedProduct w) :
    nrd z (φ a) = nrd w a := by
  rw [nrd, nrd, ← mulRight_conj φ hφ a, LinearMap.det_conj]

/-- **The reduced norm is invariant under cohomologous change of cocycle**
(`CrossedProduct.algEquivOfCoboundary` is `L`-linear, `algEquivOfCoboundary_smul`). -/
theorem nrd_algEquivOfCoboundary (b : (L ≃ₐ[K] L) → Lˣ)
    (h : ∀ σ τ : L ≃ₐ[K] L, σ • b τ / b (σ * τ) * b σ = w.toFun σ τ / z.toFun σ τ)
    (a : CrossedProduct w) :
    nrd z (CrossedProduct.algEquivOfCoboundary b h a) = nrd w a :=
  nrd_algEquiv (CrossedProduct.algEquivOfCoboundary b h)
    (CrossedProduct.algEquivOfCoboundary_smul b h) a

/-- **The reduced-norm image on units depends only on the cohomology class of the cocycle.** -/
theorem nrd_image_eq_of_cohomologous (hzw : z.Cohomologous w) :
    (Set.range fun u : (CrossedProduct w)ˣ => nrd w (u : CrossedProduct w))
      = (Set.range fun u : (CrossedProduct z)ˣ => nrd z (u : CrossedProduct z)) := by
  obtain ⟨b, hb⟩ := hzw
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Units.map (CrossedProduct.algEquivOfCoboundary b hb).toMonoidHom u, ?_⟩
    show nrd z ((CrossedProduct.algEquivOfCoboundary b hb) (u : CrossedProduct w))
      = nrd w (u : CrossedProduct w)
    exact nrd_algEquivOfCoboundary b hb (u : CrossedProduct w)
  · rintro ⟨v, rfl⟩
    refine ⟨Units.map (CrossedProduct.algEquivOfCoboundary b hb).symm.toMonoidHom v, ?_⟩
    show nrd w ((CrossedProduct.algEquivOfCoboundary b hb).symm (v : CrossedProduct z))
      = nrd z (v : CrossedProduct z)
    rw [← nrd_algEquivOfCoboundary b hb
        ((CrossedProduct.algEquivOfCoboundary b hb).symm (v : CrossedProduct z)),
      AlgEquiv.apply_symm_apply]

end CrossedProductNrd
