import L20261018.Hyp27
/-!
# `(a)`: restriction commutes with a change of coefficients

`Hyp27` proves the kernel statement for the explicit restriction map with coefficients
`KummerCoeff F p`. To move it to the paper's `V = H¹(F, μ_p)` (coefficients `ZMod p`) one needs that
restriction commutes with a change of coefficients:

`res_S (coeffMap c) = coeffMap' (res_S c)`.

Both sides are computed by `explicitMap1_comp` as a single composite coefficient map, so the proof is
one `explicitMap1_comp` rewrite followed by `explicitMap1_congr_of_eq`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

universe u

namespace KummerExplicit

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type u} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]

/-- **Restriction commutes with a change of coefficients** (identity on the group). -/
theorem explicitRes1_explicitMap1_id (S : Subgroup G) (e : M →+ N) {he : Continuous e}
    {hequiv : ∀ (g : G) (m : M), e (g • m) = g • e m} (c : H1 G M) :
    explicitRes1 G N S (explicitMap1 G M G N (ContinuousMonoidHom.id G) e he hequiv c)
      = explicitMap1 G M S N (ContinuousMonoidHom.subgroupSubtype S) e he
          (fun s m => hequiv (s : G) m) c := by
  have h₁ := explicitMap1_comp (G := G) (M := M) (H := G) (N := N)
    (φ := ContinuousMonoidHom.id G) (f := e) he hequiv
    (K := ↥S) (P := N) (ψ := ContinuousMonoidHom.subgroupSubtype S)
    (q := AddMonoidHom.id N) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul N S)
  rw [explicitRes1_eq_explicitMap1]
  refine (DFunLike.congr_fun h₁.symm c).trans ?_
  have key := explicitMap1_congr_of_eq G M ↥S N
    ((ContinuousMonoidHom.id G).comp (ContinuousMonoidHom.subgroupSubtype S))
    (ContinuousMonoidHom.subgroupSubtype S)
    ((AddMonoidHom.id N).comp e) e
    (hf := he) (hq := he) (hφ := fun s m => hequiv (s : G) m)
    (hψ := fun s m => hequiv (s : G) m) rfl rfl
  exact DFunLike.congr_fun key c

end KummerExplicit
