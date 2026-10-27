import L20261018.Hyp4
import L20261018.Galo
import TauCeti.FieldTheory.GaloisCohomology.Kummer
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars

/-!
# The coefficient bridge: Kummer classes in the paper's `V`

`Hyp16`–`Hyp18` settle campaign item (e) in the Kummer-theoretic model, whose coefficient module is
`TauCeti.KummerCoeff F p = Additive (rootsOfUnity p (Fˢ))`. The paper's vector space is
`V = H¹(G_F, μ_p)` with `μ_p` identified with the *trivial* `ZMod p`-module (fixing `ζ_p`), which in
this campaign is `GaloBase.V F p = continuousCohomology 1 (GaloBase.muP F p)`, a `ZMod p`-module —
the carrier on which `GaloBase.cup` is `ZMod p`-bilinear.

This file transports Kummer classes along that identification. Three steps, each an existing
TauCeti comparison:

1. **coefficients**: `KummerCoeff F p ≃ₗ[ZMod p] ZMod p`, because both sides are one-dimensional over
   `ZMod p` (`TauCeti.finrank_kummerCoeff`);
2. **`H¹`**: `TauCeti.ContCohomology.explicitCoeff1Equiv` turns an equivariant additive equivalence
   of coefficient modules into one on `H¹`. Equivariance uses `TauCeti.smul_kummerCoeff_eq_self`
   (`μ_p ⊂ F` makes the `G_F`-action on `μ_p` trivial);
3. **model**: `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` compares the explicit
   inhomogeneous `H¹` of a *discrete* representation over **any** coefficient ring to the canonical
   `continuousCohomology`; `GaloBase.muP F p` is, on the nose,
   `TauCeti.ofDiscreteModule (ZMod p) G_F (ZMod p)`.

The result `kummerClass : Fˣ → V` is the paper's `a ↦ (a)`, and `kummerClass a = 0 ↔ a ∈ F^{×p}`.

Note (recon): TauCeti *also* has `TauCeti.ClassFieldTheory.muNRepH1Equiv` /
`kummerClass_eq_zero_iff`, which do the same job for the universe-lifted trivial model
`TauCeti.trivialFp` (carrier `ULift (ZMod p)`). `GaloBase.muP` uses the unlifted `ZMod p`, so this
file builds the bridge at that carrier instead; the two agree through `trivialFpEquiv`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace KummerBridge

variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-! ### Instances on the carrier of `muP`

`muP F p` is definitionally `ofDiscreteModule (ZMod p) G (ZMod p)`, but instance search does not
unfold the definition, so the carrier's instances are declared here (the same device TauCeti uses in
`NumberTheory/ClassFieldTheory/MuNRep.lean`). -/

/-- **The coefficient identification** `μ_p ≃ ZMod p` as `ZMod p`-modules: both are
one-dimensional over `ZMod p`. -/
noncomputable def kummerCoeffLinearEquiv (hp : IsUnit (p : F)) :
    KummerCoeff F p ≃ₗ[ZMod p] ZMod p :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_kummerCoeff hp]; simp)

/-- A primitive `p`-th root of unity in `F`, which exists because `F` contains all of them. -/
noncomputable def primitiveRoot : F :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p).choose

theorem primitiveRoot_spec : IsPrimitiveRoot (primitiveRoot F p) p :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot F p).choose_spec

/-- **The coefficient comparison on `H¹`**, `H¹(G_F, μ_p) ≃ H¹(G_F, ZMod p)`. -/
noncomputable def kummerH1Equiv (hp : IsUnit (p : F)) :
    H1 (AbsoluteGaloisGroup F) (KummerCoeff F p) ≃+ H1 (AbsoluteGaloisGroup F) (ZMod p) :=
  explicitCoeff1Equiv (G := AbsoluteGaloisGroup F) (M := KummerCoeff F p) (N := ZMod p)
    (kummerCoeffLinearEquiv F p hp).toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun g m => by rw [smul_kummerCoeff_eq_self (primitiveRoot_spec F p) g m]; rfl)

/-- **The model comparison, via forgetting the scalars.** `GaloBase.muP F p` is
`ofDiscreteModule (ZMod p) G_F (ZMod p)`, whose scalar restriction to `ℤ` is
`ofDiscreteModule ℤ G_F (ZMod p)` *on the nose*; `TauCeti.ContCohomology.restrictScalarsIntEquiv`
therefore identifies `continuousCohomology 1 (ofDiscreteModule ℤ G (ZMod p))` — the target of the
explicit comparison — with the paper's `V = continuousCohomology 1 (muP)`. -/
noncomputable def h1ToVEquiv :
    H1 (AbsoluteGaloisGroup F) (ZMod p) ≃+ GaloBase.V F p :=
  (explicitH1AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)).trans
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 1)

/-- **The Kummer class in the paper's `V`**: the paper's `a ↦ (a)`, obtained from
`TauCeti.kummerMap` by the coefficient and model comparisons. -/
noncomputable def kummerClass (hp : IsUnit (p : F)) (a : Fˣ) : GaloBase.V F p :=
  h1ToVEquiv F p ((kummerH1Equiv F p hp) ((kummerMap F p hp a).toAdd))

/-- **`(a) = 0` exactly for `p`-th powers**: the kernel of `a ↦ (a)` on `Fˣ` is `F^{×p}`. This is
the `V`-level form of `TauCeti.ker_kummerMap`. -/
theorem kummerClass_eq_zero_iff (hp : IsUnit (p : F)) (a : Fˣ) :
    kummerClass F p hp a = 0 ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  have key : (kummerMap F p hp a).toAdd = 0 ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
    have h1 : (kummerMap F p hp a).toAdd = 0 ↔ kummerMap F p hp a = 1 := by
      constructor
      · intro h
        have h' := congrArg Multiplicative.ofAdd h
        simpa using h'
      · intro h
        rw [h]
        rfl
    rw [h1, ← MonoidHom.mem_ker, ker_kummerMap, powerSubgroup_eq_range_powMonoidHom]
  rw [kummerClass, AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff]
  exact key

end KummerBridge
