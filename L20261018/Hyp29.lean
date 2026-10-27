import L20261018.Hyp28
import L20261018.Hyp9
import L20261018.Hyp19
/-!
# `(a)` at the level of the canonical cohomology of `G_F` with coefficients `ZMod p`

Chaining

* `Hyp9.res_explicitH1` — restriction commutes with the explicit/canonical comparison,
* `Hyp28` — restriction commutes with a change of coefficients,
* TauCeti's `explicitMap1_eq_zero_iff_explicitRes1_eq_zero` — a coefficient change detects zero,
* `Hyp27` — the kernel of the explicit restriction map,

gives the vanishing criterion for the restriction of the Kummer class in the **canonical** cohomology
of `G_F` with coefficients `ZMod p` (the model of `V = H¹(F, μ_p)` after forgetting scalars).
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace BKummer

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`(a)` in the canonical model**: restriction to `E.fixingSubgroup` kills the Kummer class of
`a` exactly when `a ∈ (Fˣ)^p ⊔ Δ`. -/
theorem res_explicitH1_kummerMap_eq_zero_iff (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (a : Fˣ) :
    ContinuousCohomology.res
        (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) 1
        (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
          ((KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd)) = 0
      ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  set S : Subgroup (AbsoluteGaloisGroup F) :=
    (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup with hS
  set e : KummerCoeff F p →+ ZMod p :=
    (KummerBridge.kummerCoeffLinearEquiv F p hp).toAddEquiv.toAddMonoidHom with he
  set c : H1 (AbsoluteGaloisGroup F) (KummerCoeff F p) := (kummerMap F p hp a).toAdd with hc
  -- the equivariance of the coefficient map (the action is trivial on both sides)
  have heq : ∀ (g : AbsoluteGaloisGroup F) (m : KummerCoeff F p), e (g • m) = g • e m :=
    fun g m => by
      rw [smul_kummerCoeff_eq_self (KummerBridge.primitiveRoot_spec F p) g m]; rfl
  -- (`c` is a `set`-binder, so restate the goal's argument)
  have hnorm : (KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd
      = explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p) (AbsoluteGaloisGroup F) (ZMod p)
          (ContinuousMonoidHom.id (AbsoluteGaloisGroup F)) e continuous_of_discreteTopology heq
          (kummerMap F p hp a).toAdd := rfl
  rw [show ContinuousCohomology.res S (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) 1
        (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
          ((KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd))
      = explicitH1AddEquivContinuousCohomology (G := ↥S) (M := ZMod p)
          (explicitRes1 (AbsoluteGaloisGroup F) (ZMod p) S
            ((KummerBridge.kummerH1Equiv F p hp) (kummerMap F p hp a).toAdd)) from
      res_explicitH1 S _]
  refine (AddEquivClass.map_eq_zero_iff (f := explicitH1AddEquivContinuousCohomology
    (G := ↥S) (M := ZMod p))).trans ?_
  rw [hnorm]
  rw [KummerExplicit.explicitRes1_explicitMap1_id]
  exact (explicitMap1_eq_zero_iff_explicitRes1_eq_zero
    (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p) (H := ↥S) (N := ZMod p)
    (S := S) (e := ContinuousMulEquiv.refl ↥S) (hφ := rfl) (f := e)
    (hf := (KummerBridge.kummerCoeffLinearEquiv F p hp).bijective)
    (hequiv := fun s m => heq (s : AbsoluteGaloisGroup F) m)
    (c := (kummerMap F p hp a).toAdd)).trans
    (explicitRes1_kummerMap_eq_zero_iff hp Δ hroots a)

end BKummer
