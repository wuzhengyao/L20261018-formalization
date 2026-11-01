import L20261018.Ch3.NormImage.Step002_five_term_mg_k2_data
import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# The five-term Hochschild-Serre sequence over `G_F` with `ZMod p` coefficients

`galo_five_term` is the paper's `thm:hs-tate-exact-sequences` at the concrete carrier `G_F`: for a
closed normal subgroup `N`, exactness holds at both inner terms.

The trivial `ZMod p` instances (`SMul`, `MulAction`, `DistribMulAction`, `ContinuousSMul` for
`AbsoluteGaloisGroup K`, in `namespace GaloFive`) are declared in `Step002`: that is the module the
rest of the tree takes them from, and this file imports it.  Keeping a second, verbatim copy here
is what made the root module `L20261018` fail with

    environment already contains 'GaloFive.instSMulAbsoluteGaloisGroupZMod_l20261018'

(anonymous instances synthesise their name from the class and the head type only, so two identical
copies in different modules collide as soon as one environment contains both).
-/

open TauCeti ContCohomology

namespace GaloFive

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

/-- The five-term sequence over `G_F` with `μ_p` coefficients, for any closed normal subgroup. -/
theorem galo_five_term
    (N : Subgroup (AbsoluteGaloisGroup K)) [N.Normal]
    [ContinuousSMul ((AbsoluteGaloisGroup K) ⧸ N)
      ↥(FixedPoints.addSubgroup (↥N) (ZMod p))]
    (hN : IsClosed (N : Set (AbsoluteGaloisGroup K))) :
    (explicitResConj1 (AbsoluteGaloisGroup K) (ZMod p) N).range =
        (transgression (AbsoluteGaloisGroup K) (ZMod p) N hN).ker
    ∧ (transgression (AbsoluteGaloisGroup K) (ZMod p) N hN).range =
        (explicitInfl2 (AbsoluteGaloisGroup K) (ZMod p) N).ker :=
  ⟨fiveTerm_exact_H1N (G := AbsoluteGaloisGroup K) (M := ZMod p) (N := N) hN,
   fiveTerm_exact_H2Q (G := AbsoluteGaloisGroup K) (M := ZMod p) (N := N) hN⟩

end GaloFive
