import TauCeti.Algebra.CrossedProduct.CentralSimple
import TauCeti.Algebra.CrossedProduct.Basic
import TauCeti.Algebra.CentralSimple.Index
import TauCeti.Algebra.CentralSimple.Degree

/-!
# The index of a crossed-product (symbol) algebra is at most its degree

Campaign item (d) (`hind` in the paper's Theorem 3.2): the index function is bounded by `p` on the
symbol classes. The content is that a symbol algebra — the cyclic algebra `(L/K, σ, b)`, written
here in the general form of a crossed product of a Galois extension `L/K` by a `2`-cocycle `c` —
has **index at most its degree**, and its degree is `[L : K]`.

Nothing in this bound needs `Aut_K(L)` to be cyclic; cyclicity enters only when identifying the
Brauer class with a cup product (`TauCeti.Algebra.CrossedProduct.CupProduct`).

The pieces are all in TauCeti:

* `TauCeti.CrossedProduct.finrank_eq_finrank_sq`: `finrank K (CrossedProduct c) = [L : K]^2`;
* `TauCeti.CrossedProduct.instIsSimpleRing`, `TauCeti.CrossedProduct.instIsCentral`: the crossed
  product of a finite Galois extension is a central simple algebra;
* `TauCeti.Algebra.deg_eq_of_finrank_eq_sq`: `deg = √finrank`;
* `TauCeti.Algebra.index_le_deg`: `index ≤ deg`.
-/

open TauCeti

namespace SymbolAlgebra

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The invariants condition making a crossed product central, for a Galois extension: the fixed
field of `Aut_K(L) = ⊤` is `K` (`IsGalois.fixedField_top`). -/
instance instIsInvariant : Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun x hx => by
    have h : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f _
      exact hx f
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at h
    exact h⟩

/-- **The degree of the crossed product is `[L : K]`.** -/
theorem deg_crossedProduct (c : TwoCocycle K L) :
    Algebra.deg K (CrossedProduct c) = Module.finrank K L :=
  Algebra.deg_eq_of_finrank_eq_sq (CrossedProduct.finrank_eq_finrank_sq (c := c))

/-- **The index of a crossed product is at most `[L : K]`** — for a symbol algebra of degree `p`,
  `index ≤ p`. This is the paper's `hind` at the level of the symbol algebra itself. -/
theorem index_crossedProduct_le (c : TwoCocycle K L) :
    Algebra.index K (CrossedProduct c) ≤ Module.finrank K L := by
  have h := Algebra.index_le_deg K (CrossedProduct c)
  rwa [deg_crossedProduct c] at h

/-- The symbol-algebra form of the bound: if `[L : K] = p`, the index is at most `p`. -/
theorem index_crossedProduct_le_of_finrank (c : TwoCocycle K L) (p : ℕ)
    (hp : Module.finrank K L = p) : Algebra.index K (CrossedProduct c) ≤ p := by
  rw [← hp]
  exact index_crossedProduct_le c

end SymbolAlgebra

#print axioms SymbolAlgebra.deg_crossedProduct
#print axioms SymbolAlgebra.index_crossedProduct_le
#print axioms SymbolAlgebra.index_crossedProduct_le_of_finrank
