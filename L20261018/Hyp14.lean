import L20261018.Galo
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Assoc

/-!
# The degree-`(1,1,1)` triple cup product, without a chain homotopy

The paper's Lemma 3.3(3) needs two facts about the degree-`(1,1,1)` triple cup product
`x ⌣ y ⌣ z`:

* **coherence** (`hcoh`): `x ⌣ (y ⌣ z) = (x ⌣ y) ⌣ z`;
* **cyclic symmetry** (`hcyc`): `(x ⌣ y) ⌣ z = (z ⌣ x) ⌣ y`.

An earlier assessment of this campaign recorded these as missing, on the grounds that the *explicit*
(inhomogeneous) model in `TauCeti.ContCohomology` has only the associativity laws
`explicitCup_assoc000` … `explicitCup_assoc101`, i.e. the shapes with an `H⁰` factor, and that
`assoc111` would have to be built as a `2`-cochain homotopy.

That assessment was a search-by-name artefact (the recurring failure mode of this campaign, cf.
`fiveTerm`/`transgression`): the *canonical* model has full associativity in **all** degrees,
`TauCeti.TopPairing.cup_assoc`, and its documentation states explicitly that no chain homotopy is
involved — the Alexander–Whitney formula is associative on homogeneous cochains, in contrast with
graded commutativity, which genuinely fails there and needs `cup_gradedComm`. So

* `hcoh` at degrees `(1,1,1)` **is** `cup_assoc 1 1 1` (after killing a `degreeCast` along a
  propositionally trivial arithmetic identity), and
* `hcyc` is `cup_assoc` together with `cup_skew` (`Galo.lean`) twice, with the signs cancelling
  because two transpositions of degree-`1` classes contribute `(-1)² = 1`.

The file then states Lemma 3.3(3) itself in the continuous model:

`v ∈ U^⊥ ⟹ v ⌣ (a₁ ⌣ b₁ + a₂ ⌣ b₂) = 0`,

which is the form used by `prop:hs-tate-exact-sequences` (2) and by Lemma 3.3.
-/

open TauCeti

set_option maxHeartbeats 1000000

namespace GaloCup

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

/-- `H¹(G_F, μ_p)` in the continuous model, with `μ_p` coefficients. -/
noncomputable abbrev V : Type := GaloBase.V K p

/-- `H²(G_F, μ_p)`. -/
noncomputable abbrev H2 : Type := GaloBase.H2 K p

/-- `H³(G_F, μ_p)`. -/
noncomputable abbrev H3 : Type := ↑(continuousCohomology 3 (GaloBase.muP K p)).toModuleCat

/-- The product `H¹ × H² → H³`, i.e. the cup product with a degree-`2` factor on the right. -/
noncomputable abbrev cupH : V K p →ₗ[ZMod p] H2 K p →ₗ[ZMod p] H3 K p :=
  (GaloBase.muPairing K p).cup 1 2

/-- The degree-`(1,1,1)` triple product `(x ⌣ y) ⌣ z`. -/
noncomputable abbrev triple (x y z : V K p) : H3 K p :=
  (GaloBase.muPairing K p).cup 2 1 (GaloBase.cup (K := K) (p := p) x y) z

/-- **Coherence of the triple cup** (`hcoh` of Lemma 3.3(3)): `(x ⌣ y) ⌣ z = x ⌣ (y ⌣ z)`.

This is `TauCeti.TopPairing.cup_assoc` at degrees `(1,1,1)`. The only obstruction is bookkeeping:
`cup_assoc` transports the right-hand side along `degreeCast` by `(Nat.add_assoc 1 1 1).symm`, an
equation between two natural numbers that are both definitionally `3`, so the transport is the
identity (`Subsingleton.elim` on the proof, then `degreeCast_rfl`). -/
theorem triple_eq_cupH (x y z : V K p) :
    triple K p x y z = cupH K p x (GaloBase.cup (K := K) (p := p) y z) := by
  have h := TopPairing.cup_assoc (GaloBase.muPairing K p) (GaloBase.muPairing K p)
    (GaloBase.muPairing K p) (GaloBase.muPairing K p) (fun a b c => mul_assoc a b c) 1 1 1 x y z
  rw [show (Nat.add_assoc 1 1 1).symm = rfl from Subsingleton.elim _ _,
    ContinuousCohomology.degreeCast_rfl] at h
  simpa [triple, cupH, GaloBase.cup] using h

/-- Swapping the first two arguments of the triple product changes its sign. -/
theorem triple_swap12 (a b c : V K p) :
    triple K p a b c = - triple K p b a c := by
  have h : GaloBase.cup (K := K) (p := p) a b = - GaloBase.cup (K := K) (p := p) b a :=
    GaloBase.cup_skew (K := K) (p := p) a b
  simp only [triple, h, map_neg, LinearMap.neg_apply]

/-- Swapping the last two arguments of the triple product changes its sign. -/
theorem triple_swap23 (a b c : V K p) :
    triple K p a b c = - triple K p a c b := by
  rw [triple_eq_cupH, GaloBase.cup_skew (K := K) (p := p) b c, map_neg]
  simpa using congrArg Neg.neg (triple_eq_cupH K p a c b).symm

/-- **Cyclic symmetry of the triple cup** (`hcyc` of Lemma 3.3(3)):
`(x ⌣ y) ⌣ z = (z ⌣ x) ⌣ y`. Two sign flips, of degree-`1` classes, cancel. -/
theorem triple_cyclic (x y z : V K p) : triple K p x y z = triple K p z x y := by
  rw [triple_swap23 K p x y z, triple_swap12 K p x z y, neg_neg]

/-- **Lemma 3.3(3)** in the continuous model: an element `v` orthogonal to `a₁` and `a₂`
(`v ∈ U^⊥`, i.e. `v ⌣ a₁ = v ⌣ a₂ = 0`) has vanishing cup product with every class of the form
`a₁ ⌣ b₁ + a₂ ⌣ b₂` — in particular with `[D]`.

The paper's `U` is `⟨(a₁), (a₂)⟩` and `[D] = a₁ ⌣ b₁ + a₂ ⌣ b₂` (`cor:symbol-cup`); the vanishing
of `v ⌣ [D]` is what exhibits `U^⊥ ⊆ R`, `R` being the kernel of cupping with `[D]`. -/
theorem lemma_3_3_3_continuous (a1 a2 b1 b2 v : V K p)
    (h1 : GaloBase.cup (K := K) (p := p) v a1 = 0)
    (h2 : GaloBase.cup (K := K) (p := p) v a2 = 0) :
    cupH K p v (GaloBase.cup (K := K) (p := p) a1 b1
      + GaloBase.cup (K := K) (p := p) a2 b2) = 0 := by
  rw [map_add, ← triple_eq_cupH, ← triple_eq_cupH, triple_cyclic K p v a1 b1,
    triple_cyclic K p v a2 b2, triple_eq_cupH, triple_eq_cupH, h1, h2, map_zero, map_zero,
    add_zero]

end GaloCup

#print axioms GaloCup.triple_eq_cupH
#print axioms GaloCup.triple_cyclic
#print axioms GaloCup.lemma_3_3_3_continuous
