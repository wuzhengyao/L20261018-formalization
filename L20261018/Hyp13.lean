import L20261018.Hyp12
import L20261018.Hyp5
/-!
# Theorem 3.5(1) instantiated: the first short exact sequence of `thm:hs-tate-exact-sequences`

This file discharges the hypotheses of `L20261018.three_five_one_add` with the *actual*
cohomological objects of the paper:

* `V = H¹(G_F, μ_p)` — `TauCeti.ContCohomology.H1 (AbsoluteGaloisGroup K) (ZMod p)`;
* `M = H¹(G_E, μ_p)`, `M^G` — `GaloFive.MG`, the conjugation invariants `H1ConjInvariants`;
* `res_{E/F}` — `GaloFive.resMG = explicitResConj1`;
* `d₂` — `GaloFive.d2 = transgression`, with the two halves of the Hochschild–Serre five-term
  exactness `GaloFive.hkerd2` (`ker d₂ = im res`) and `GaloFive.hd2surj` (`im d₂ = K₂`) coming
  from `TauCeti.ContCohomology.fiveTerm_exact_H1N` and `fiveTerm_exact_H2Q`;
* `K₂ = ker(inf)` — `GaloFive.K2 = (explicitInfl2).ker`;
* `N = cor M` — `GaloFive.Ncor`, and `N_G(M) = res(N)` — `GaloFive.NG`.

The one ingredient that is *not* proved here is the identification `U = ker res_{E/F}` with the
two-dimensional span `U = ⟨(a₁), (a₂)⟩` (the paper's `prop:bi-kummer-kernel`, campaign item (e)).
Correspondingly the statement below carries `U = resMG.ker`; the identification of that kernel with
the span is exactly what (e) supplies. Everything else is unconditional.
-/

set_option maxHeartbeats 1000000

open TauCeti ContCohomology

namespace GaloFive

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

variable (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]

/-- The transgression with target restricted to `K₂ = ker(inf)`: the map whose surjectivity is the
second half of the five-term exact sequence. -/
noncomputable def d2' : MG K p E →+ ↥(K2 K p E) :=
  (d2 K p E).codRestrict (K2 K p E) fun m => by
    have h : d2 K p E m ∈ (d2 K p E).range := ⟨m, rfl⟩
    rwa [hd2surj K p E] at h

/-- `K₂` does not change the kernel of the transgression. -/
theorem d2'_ker : (d2' K p E).ker = (resMG K p E).range := by
  rw [d2', AddMonoidHom.ker_codRestrict, hkerd2]

/-- **The five-term exactness at `H²`**, read as surjectivity of `d₂` onto `K₂`. -/
theorem d2'_range : (d2' K p E).range = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : (y : H2 (AbsoluteGaloisGroup K ⧸ E.fixingSubgroup)
      ↥(FixedPoints.addSubgroup (↥E.fixingSubgroup) (ZMod p))) ∈ (d2 K p E).range := by
    rw [hd2surj K p E]
    exact y.2
  obtain ⟨m, hm⟩ := hy
  refine ⟨m, ?_⟩
  rw [d2', AddMonoidHom.codRestrict_apply]
  exact Subtype.ext hm

/-- **Theorem 3.5(1)** (`thm:hs-tate-exact-sequences` (1)) for the concrete cohomological objects:

`0 → V/(ker res + N) → M^G/N_G(M) → K₂ → 0`,

where `V = H¹(G_F, μ_p)`, `M = H¹(G_E, μ_p)`, `N = cor_{E/F} M`, `N_G(M) = res(N)` and
`K₂ = ker(H²(G_E/F, μ_p^{G_E}) → H²(G_F, μ_p))`.

`U` is taken as `ker res_{E/F}`. The paper identifies that kernel with `⟨(a₁), (a₂)⟩` through
`prop:bi-kummer-kernel` (campaign item (e)); that identification is machine-checked at several
layers (`Hyp16`/`Hyp18`, `Hyp24`, `Hyp27`, `Hyp29`), and `Hyp36.ker_res_eq_span` gives it on
`GaloBase.V` as `span{(a₁), (a₂)}`. Wiring the two together here is not yet done. -/
-- @source file=raw/L20261018.tex locator=label:thm:hs-tate-exact-sequences quote="越迁映射诱导满射 $\bar d_2:\widehat H^0(G,M)\to K_2$，并有自然短正合列"
theorem theorem_3_5_1_galo :
    ∃ (φ : (H1 (AbsoluteGaloisGroup K) (ZMod p) ⧸
          ((resMG K p E).ker ⊔ Ncor K p E)) →+ (↥(MG K p E) ⧸ NG K p E))
      (ψ : (↥(MG K p E) ⧸ NG K p E) →+ ↥(K2 K p E)),
      Function.Injective φ ∧ Function.Surjective ψ ∧ φ.range = ψ.ker :=
  L20261018.three_five_one_add (resMG K p E).ker (Ncor K p E) (MG K p E) (resMG K p E) rfl
    (NG K p E) rfl (d2' K p E) (d2'_ker K p E) (d2'_range K p E)

end GaloFive
