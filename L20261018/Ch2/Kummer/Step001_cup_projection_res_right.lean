import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula

universe u

open TauCeti ContCohomology

/-- Projection formula with the restriction on the second factor (the paper's `hproj`):
`cor (w ⌣ res v) = cor w ⌣ v`, derived from TauCeti's res-left form by graded
commutativity (the sign `-1` cancels on both sides). -/
theorem explicitCup_projection_res_right
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type u) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
      [DistribMulAction G M] [ContinuousSMul G M]
    (N : Type u) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [DistribMulAction G N] [ContinuousSMul G N]
    (P : Type u) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
      [DistribMulAction G P] [ContinuousSMul G P]
    (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
    (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
    (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)
    (w : H1 U M) (v : H1 G N) :
    explicitCor2 G P U hU
        (explicitCup11 U M N P μ hμ (fun g m y => hequiv (g : G) m y) w
          (explicitRes1 G N U v)) =
      explicitCup11 G M N P μ hμ hequiv (explicitCor1 G M U hU w) v := by
  have h := explicitCup_projection11 G N M P U hU μ.flip (μ.continuous_flip hμ)
    (μ.flip_map_smul hequiv) v w
  have h1 := explicitCup11_eq_neg_flip (G := U) M N P μ hμ
    (fun g m y => hequiv (g : G) m y) w (explicitRes1 G N U v)
  have h2 := explicitCup11_eq_neg_flip (G := G) M N P μ hμ hequiv
    (explicitCor1 G M U hU w) v
  rw [h1, map_neg, h, ← h2]
