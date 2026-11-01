import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

universe u

open TauCeti ContCohomology

/-- Restriction commutes with the explicit/continuous `H¹` comparison. -/
theorem res_explicitH1
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    (S : Subgroup G) (x : H1 G M) :
    ContinuousCohomology.res S (ofDiscreteModule ℤ G M) 1 (explicitH1AddEquivContinuousCohomology G M x)
      = explicitH1AddEquivContinuousCohomology S M (explicitRes1 G M S x) := by
  rw [ContinuousCohomology.res_def]
  refine (explicitH1AddEquivContinuousCohomology_map
    (φ := ContinuousMonoidHom.subgroupSubtype S) (f := AddMonoidHom.id M)
    (hf := fun h m => rfl) (x := x)).trans ?_
  rw [explicitRes1_eq_explicitMap1]
