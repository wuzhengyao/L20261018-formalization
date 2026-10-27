import L20261018.Hyp32
/-!
# `(f)`: the reduced norm of *any* algebra presented by a crossed product, and the paper's `hNrd`

`Hyp32` proves that the reduced norm `nrd` of a crossed product is not moved by any `K`-algebra
isomorphism between crossed-product presentations. The present file draws the two consequences the
paper needs:

1. **`Nrd` is well defined on an abstract `K`-algebra `D` once `D` is *known* to be isomorphic to a
   crossed product.** `nrdOfIso c φ` transports `nrd c` along `φ : D ≃ₐ[K] CrossedProduct c`, and
   `nrdOfIso_independent` shows the result does not depend on `φ` — two transports differ by an
   automorphism of `CrossedProduct c`, which Skolem–Noether makes inner and `nrd` is blind to inner
   automorphisms (`Hyp32.nrd_algEquiv_self`). This is Gille–Szamuely **Prop. 2.6.3**'s "does not
   depend on the choice of splitting field and matrix representation" in the sharpest form available
   here: independence of *every* presentation.

2. **The paper's `hNrd` for such a `D`**: every field norm `N_{L/K}(y)` of a unit `y ∈ L^×` is the
   reduced norm of a unit of `D` (`exists_nrdOfIso_eq_norm`). This is `lemma_3_3_1`'s input
   `N_{E/F}(E^×) ⊆ Nrd(D^×)` (`prop:prelim-splitting` (3)).

## Named hypothesis: the existence of the crossed-product presentation

Item 1 and 2 are conditional on the *data* `c : TwoCocycle K L` and `φ : D ≃ₐ[K] CrossedProduct c`.
That data is not free: producing it for the paper's `D` is exactly the step

> `E` splits `D`  ⟹  `E ↪ D` is a maximal subfield (GS2017 Prop. 4.5.8)  ⟹  `D` is a crossed product
> over `E` (GS2017 §2.5 / §4.7)

whose Lean-side entry point `E` splits `D` needs the **symbol-class formula**
`[(a,b)_F] = (a) ∪ (b)` (GS2017 §2.5/§4.7; the paper's `cor:symbol-cup`, after Merkurjev–Suslin).
That result is **not** in TauCeti at general `p` (only the `p = 2` quaternion case,
`TauCeti.BrauerGroup.brauer2EquivH2_quaternionClass`), and it is registered as the named hypothesis
`wiki/hyp-symbol-cup.md`. Everything else in the chain is machine-checked here.
-/

open TauCeti

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace CrossedProductNrd

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable {z w : TwoCocycle K L}

/-- **The reduced norm of an algebra presented by a crossed product**, transported along a chosen
presentation `φ : D ≃ₐ[K] CrossedProduct c`. `nrdOfIso_independent` below shows this is well
defined. -/
noncomputable def nrdOfIso {D : Type u} [Ring D] [Algebra K D] (c : TwoCocycle K L)
    (φ : D ≃ₐ[K] CrossedProduct c) (x : D) : L :=
  nrd c (φ x)

/-- **The transported reduced norm does not depend on the chosen presentation.** Two presentations
`φ`, `φ'` of the same `D` differ by the automorphism `φ.symm.trans φ'` of `CrossedProduct c`, which
Skolem–Noether exhibits as conjugation by a unit, and conjugation leaves `nrd` unchanged
(`Hyp32.nrd_algEquiv_self`). -/
theorem nrdOfIso_independent {D : Type u} [Ring D] [Algebra K D] (c : TwoCocycle K L)
    (φ φ' : D ≃ₐ[K] CrossedProduct c) (x : D) : nrdOfIso c φ x = nrdOfIso c φ' x := by
  have h : φ' x = (φ.symm.trans φ') (φ x) := by
    show φ' x = φ' (φ.symm (φ x))
    rw [AlgEquiv.symm_apply_apply]
  show nrd c (φ x) = nrd c (φ' x)
  rw [h, nrd_algEquiv_self]

/-- **The paper's `hNrd` for an algebra presented by a crossed product**: every field norm
`N_{L/K}(y)` of a unit `y ∈ L^×` is the reduced norm of a unit of `D`. This is
`prop:prelim-splitting` (3)'s `N_{L/F}(L^×) ⊆ Nrd_Δ(Δ^×)`, transported along the presentation. -/
theorem exists_nrdOfIso_eq_norm {D : Type u} [Ring D] [Algebra K D] (c : TwoCocycle K L)
    (φ : D ≃ₐ[K] CrossedProduct c) (y : Lˣ) :
    ∃ v : Dˣ, nrdOfIso c φ (v : D) = algebraMap K L (Algebra.norm K (y : L)) := by
  obtain ⟨u, hu⟩ := norm_mem_range_nrd_units c y
  refine ⟨Units.map φ.symm.toMonoidHom u, ?_⟩
  show nrd c (φ ((Units.map φ.symm.toMonoidHom u : Dˣ) : D)) = _
  rw [show φ (((Units.map φ.symm.toMonoidHom u : Dˣ) : D)) = (u : CrossedProduct c) from
    φ.apply_symm_apply (u : CrossedProduct c)]
  exact hu

/-- **The reduced-norm group of `D` contains the field-norm group of the maximal subfield** — the
set-level form of `exists_nrdOfIso_eq_norm`. -/
theorem norm_image_le_nrdOfIso_image {D : Type u} [Ring D] [Algebra K D] (c : TwoCocycle K L)
    (φ : D ≃ₐ[K] CrossedProduct c) :
    (Set.range fun y : Lˣ => algebraMap K L (Algebra.norm K (y : L)))
      ⊆ (Set.range fun v : Dˣ => nrdOfIso c φ (v : D)) := by
  rintro _ ⟨y, rfl⟩
  exact exists_nrdOfIso_eq_norm c φ y

end CrossedProductNrd
