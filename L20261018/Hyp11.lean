import L20261018.Hyp9
import L20261018.Hyp10
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Basic

/-!
# The projection formula in *continuous* cohomology

`Hyp10.lean` proves the projection formula at the level of the explicit (inhomogeneous) cochain
model, `TauCeti.ContCohomology.explicitCup_projection_res_right`. This file transports it to the
canonical carrier `continuousCohomology`, which is the form the paper's `hproj` is used in:

`cor_{E/F} (w ⌣ res_{E/F} v) = cor_{E/F}(w) ⌣ v`.

The five steps are exactly the ones listed in the handoff:

1. `res_explicitH1` (Hyp9) — restriction commutes with the explicit/continuous comparison;
2. `explicitAddEquiv_cup11` — the canonical `(1,1)` cup is `explicitCup11` under the comparisons;
3. `explicitH2AddEquivContinuousCohomology_corestriction` — degree-2 corestriction is `explicitCor2`;
4. `explicitCup_projection_res_right` (Hyp10) — the projection formula on the explicit model;
5. the reverse of 2 and 3.

No differential or cocycle computation is needed at this layer: every step is an existing
comparison theorem, so the whole content is transport.
-/

open TauCeti ContCohomology

universe u

namespace L20261018

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type u) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type u) [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction G P] [ContinuousSMul G P]

/-- **The projection formula in continuous cohomology**, right-restriction form:

`cor_U^G (w ⌣ res_U^G v) = cor_U^G(w) ⌣ v`,

for `w : H¹(U, M)`, `v : H¹(G, N)` and a coefficient pairing `μ : M →+ N →+ P`.

Every arrow in this statement is one of the canonical TauCeti constructions
(`TauCeti.TopPairing.cup` and `TauCeti.ContinuousCohomology.corestriction`), so it is the
continuous-carrier statement of `prop:prelim-cup` (2), i.e. the hypothesis `hproj` of the paper's
§3.3. -/
theorem continuousCup_projection_res_right
    [LocallyCompactSpace G]
    (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (μ : M →+ N →+ P)
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    (w : H1 U M) (v : H1 G N) :
    haveI : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
    (ContinuousCohomology.corestriction U P hU 2)
        ((ofDiscreteModulePairing μ (fun (g : U) (m : M) (y : N) => hequiv (g : G) m y)).cup 1 1
          (explicitH1AddEquivContinuousCohomology U M w)
          (ContinuousCohomology.res U (ofDiscreteModule ℤ G N) 1
            (explicitH1AddEquivContinuousCohomology G N v))) =
      (ofDiscreteModulePairing μ hequiv).cup 1 1
        (explicitH1AddEquivContinuousCohomology G M
          (explicitCor1 G M U hU w))
        (explicitH1AddEquivContinuousCohomology G N v) := by
  haveI : LocallyCompactSpace U := (U.isClosed_of_isOpen hU).locallyCompactSpace
  -- Step 1: push the restriction inside the explicit comparison (Hyp9).
  rw [res_explicitH1 (G := G) (M := N) U v]
  -- Step 2: rewrite both `(1,1)` cups as explicit cups.
  rw [ContCohomology.explicitAddEquiv_cup11 (G := U) M N P μ
      (fun g m y => hequiv (g : G) m y) w (explicitRes1 G N U v),
    ContCohomology.explicitAddEquiv_cup11 (G := G) M N P μ hequiv
      (explicitCor1 G M U hU w) v]
  -- Steps 3 and 5: transport corestriction through the degree-2 comparison.
  rw [ContinuousCohomology.explicitH2AddEquivContinuousCohomology_corestriction (G := G) U P hU]
  -- Step 4: the projection formula on the explicit model (Hyp10).
  exact congrArg (explicitH2AddEquivContinuousCohomology G P)
    (explicitCup_projection_res_right G M N P U hU μ continuous_of_discreteTopology hequiv w v)

end L20261018
