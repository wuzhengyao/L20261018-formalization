import Mathlib

/-!
# Theorem 3.5(1) as a statement about abelian groups

The paper's `thm:hs-tate-exact-sequences` (1) is the short exact sequence

`0 → V/(U+N) → Ĥ⁰(G,M) → K₂ → 0`

and the paper says explicitly that it *does not require `V` to be finite dimensional*
(「这两个结论均不要求 $V$ 有限维」). Nothing in the argument uses an `𝔽_p`-linear structure: the
construction is `v ↦ res(v) + N_G(M)`, a diagram chase in abelian groups.

This matters for the formalization because the real objects are built from cohomology:
`res` (`TauCeti.ContCohomology.explicitResConj1`) and the transgression `d₂`
(`TauCeti.ContCohomology.transgression`, a connecting homomorphism of a long exact sequence) are
additive maps. Upgrading them to `ZMod p`-linear maps would require a linear snake lemma, which
TauCeti does not provide; it is also not what the paper proves. The additive statement below is the
faithful rendition, and it is what the concrete instantiation (`Hyp13.lean`) discharges.
-/

namespace L20261018

/-- **Theorem 3.5(1)**, abelian-group form.

Given additive subgroups `U, N ≤ V`, an additive subgroup `MG ≤ W` playing the role of `M^G`,
an additive map `resMG : V →+ MG` with `ker resMG = U`, a subgroup `NG = resMG(N) ≤ MG`
(so `NG = N_G(M)` is the group-norm image), and the transgression `d₂ : MG →+ K₂` with
`ker d₂ = range resMG` and `range d₂ = K₂` (the two halves of the Hochschild–Serre five-term
exactness), there is a short exact sequence

`0 → V/(U+N) → MG/NG → K₂ → 0`. -/
theorem three_five_one_add
    {V W K2 : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup K2]
    (U N : AddSubgroup V) (MG : AddSubgroup W)
    (resMG : V →+ MG) (hker : resMG.ker = U)
    (NG : AddSubgroup MG) (hNG : NG = N.map resMG)
    (d2 : MG →+ K2) (hkerd2 : d2.ker = resMG.range) (hd2top : d2.range = ⊤) :
    ∃ (φ : (V ⧸ (U ⊔ N)) →+ (MG ⧸ NG)) (ψ : (MG ⧸ NG) →+ K2),
      Function.Injective φ ∧ Function.Surjective ψ ∧ φ.range = ψ.ker := by
  -- `f` is `res` followed by the quotient map; it kills `U` (by `hker`) and `N` (by `hNG`).
  let f : V →+ (MG ⧸ NG) := (QuotientAddGroup.mk' NG).comp resMG
  have hf : U ⊔ N ≤ f.ker := by
    intro x hx
    obtain ⟨u, hu, n, hn, hun⟩ := AddSubgroup.mem_sup.mp hx
    have hu0 : resMG u = 0 := by
      have : u ∈ resMG.ker := by rw [hker]; exact hu
      exact AddMonoidHom.mem_ker.mp this
    have hn0 : resMG n ∈ NG := by
      rw [hNG]
      exact AddSubgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hfu : f u = 0 := by
      show QuotientAddGroup.mk (resMG u) = 0
      rw [hu0, QuotientAddGroup.eq_zero_iff]
      exact NG.zero_mem
    have hfn : f n = 0 := by
      show QuotientAddGroup.mk (resMG n) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact hn0
    rw [AddMonoidHom.mem_ker, show x = u + n from hun.symm, map_add, hfu, hfn, add_zero]
  let φ : (V ⧸ (U ⊔ N)) →+ (MG ⧸ NG) := QuotientAddGroup.lift (U ⊔ N) f hf
  have hφ : ∀ v : V, φ (QuotientAddGroup.mk v) = QuotientAddGroup.mk (resMG v) := by
    intro v
    simp [φ, f]
  -- `N_G(M) ⊆ ker d₂`, which is what makes `d₂` descend to `MG/NG`.
  have hNGker : NG ≤ d2.ker := by
    intro m hm
    rw [hkerd2]
    rw [hNG] at hm
    obtain ⟨n, _, rfl⟩ := AddSubgroup.mem_map.mp hm
    exact ⟨n, rfl⟩
  let ψ : (MG ⧸ NG) →+ K2 := QuotientAddGroup.lift NG d2 hNGker
  have hψ : ∀ m : MG, ψ (QuotientAddGroup.mk m) = d2 m := by
    intro m
    simp [ψ]
  have hd2surj : Function.Surjective d2 := by
    intro y
    have : y ∈ d2.range := by rw [hd2top]; trivial
    exact this
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [AddSubgroup.mem_bot]
    rw [AddMonoidHom.mem_ker, hφ] at hz
    have hres : resMG v ∈ NG := (QuotientAddGroup.eq_zero_iff _).mp hz
    rw [hNG] at hres
    obtain ⟨n, hn, hnv⟩ := AddSubgroup.mem_map.mp hres
    have hmem : v - n ∈ U := by
      have : v - n ∈ resMG.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hnv, sub_self]
      rwa [hker] at this
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_sup.mpr ⟨v - n, hmem, n, hn, by abel⟩
  · intro y
    obtain ⟨m, rfl⟩ := hd2surj y
    exact ⟨QuotientAddGroup.mk m, by rw [hψ]⟩
  · apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
      rw [AddMonoidHom.mem_ker, hφ, hψ]
      have : resMG v ∈ d2.ker := by
        rw [hkerd2]
        exact ⟨v, rfl⟩
      exact this
    · intro y hy
      obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [AddMonoidHom.mem_ker, hψ] at hy
      rw [← AddMonoidHom.mem_ker, hkerd2] at hy
      obtain ⟨v, hv⟩ := hy
      refine ⟨QuotientAddGroup.mk v, ?_⟩
      rw [hφ, hv]

end L20261018
