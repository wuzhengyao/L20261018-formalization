import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

open TauCeti ContCohomology

namespace GaloFive

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

instance : SMul (AbsoluteGaloisGroup K) (ZMod p) := ⟨fun _ x => x⟩

instance : MulAction (AbsoluteGaloisGroup K) (ZMod p) where
  one_smul := by intro x; rfl
  mul_smul := by intro g h x; rfl

instance : DistribMulAction (AbsoluteGaloisGroup K) (ZMod p) where
  smul_zero := by intro g; rfl
  smul_add := by intro g x y; rfl

instance : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod p) := ⟨continuous_snd⟩

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
