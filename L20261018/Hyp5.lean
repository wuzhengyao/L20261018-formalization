import L20261018.Hyp4
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# The norm image `N_G(M) = (res ∘ cor)(M)`

This file continues `Hyp4.lean`, which provides the trivial-action instances on `ZMod p`, the
invariants `MG = H¹(G_E, μ_p)^{G_F}` (as an `AddSubgroup`), the restriction `resMG`, the
transgression `d₂`, `K₂ = ker(inf)` and the two halves of the Hochschild–Serre five-term exactness.
Here we add the corestriction `corN`, the composite norm image `N = cor M ⊆ V` and the group-norm
image `NG = res(N) ≤ MG`, together with the identification `NG = (res ∘ cor).range` (the paper's
`lem:hs-rescor`).

`Hyp5` imports `Hyp4` rather than redeclaring `MG`/`resMG`: the two files used to declare
`GaloFive.MG` twice (once as an `AddSubgroup`, once as its carrier type), which makes them
unimportable together — and the instantiation of Theorem 3.5(1) needs both halves at once.
-/

open TauCeti ContCohomology

namespace GaloFive

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- `M = H¹(G_E, μ_p)`. -/
abbrev M : Type := H1 (↥E.fixingSubgroup) (ZMod p)

/-- The corestriction `M → V`. -/
noncomputable def corN : M K p E →+ H1 (AbsoluteGaloisGroup K) (ZMod p) := by
  haveI : E.fixingSubgroup.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (E' := SeparableClosure K) E]
    exact Module.finrank_pos.ne'
  exact explicitCor1 (AbsoluteGaloisGroup K) (ZMod p) E.fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen (K := K) E)

/-- `N = cor M`, the composite norm image in `V`. -/
noncomputable def Ncor : AddSubgroup (H1 (AbsoluteGaloisGroup K) (ZMod p)) :=
  (corN K p E).range

/-- `N_G(M) = res(N)`, the norm image in `M^G`. -/
noncomputable def NG : AddSubgroup (MG K p E) :=
  AddSubgroup.map (resMG K p E) (Ncor K p E)

/-- `N_G(M) = res(N)` is the image of the composite `res ∘ cor`; the norm interpretation is
`res_comp_corestriction`. -/
theorem hNG : NG K p E = ((resMG K p E).comp (corN K p E)).range :=
  AddMonoidHom.map_range _ _

end GaloFive
