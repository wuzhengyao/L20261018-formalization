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

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- `M^G` in the paper, concretely: conjugation invariants of `H¹(G_E, μ_p)`. -/
noncomputable def MG : AddSubgroup (H1 (↥E.fixingSubgroup) (ZMod p)) :=
  H1ConjInvariants (AbsoluteGaloisGroup K) (ZMod p) E.fixingSubgroup

/-- The restriction map `V → M^G`. -/
noncomputable def resMG : H1 (AbsoluteGaloisGroup K) (ZMod p) →+ MG K p E :=
  explicitResConj1 (AbsoluteGaloisGroup K) (ZMod p) E.fixingSubgroup

/-- The transgression `d₂ : M^G → H²(G, μ_p)`. -/
noncomputable def d2 :
    MG K p E →+ H2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
      ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p)) :=
  transgression (AbsoluteGaloisGroup K) (ZMod p) E.fixingSubgroup
    (IntermediateField.fixingSubgroup_isClosed (K := K) E)

/-- `K₂ = ker(inf)`. -/
noncomputable def K2 : AddSubgroup (H2 ((AbsoluteGaloisGroup K) ⧸ E.fixingSubgroup)
    ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) :=
  (explicitInfl2 (AbsoluteGaloisGroup K) (ZMod p) E.fixingSubgroup).ker

/-- `ker d₂ = range res` (five-term exactness at `M^G`). -/
theorem hkerd2 : (d2 K p E).ker = (resMG K p E).range :=
  (fiveTerm_exact_H1N (G := AbsoluteGaloisGroup K) (M := ZMod p) (N := E.fixingSubgroup)
    (IntermediateField.fixingSubgroup_isClosed (K := K) E)).symm

/-- `range d₂ = K₂ = ker inf` (five-term exactness at `H²(G, μ_p)`). -/
theorem hd2surj : (d2 K p E).range = K2 K p E :=
  fiveTerm_exact_H2Q (G := AbsoluteGaloisGroup K) (M := ZMod p) (N := E.fixingSubgroup)
    (IntermediateField.fixingSubgroup_isClosed (K := K) E)

end GaloFive
