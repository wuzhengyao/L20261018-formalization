import TauCeti.FieldTheory.Kummer.IntermediateField
import TauCeti.FieldTheory.GaloisCohomology.Kummer

/-!
# `prop:bi-kummer-kernel`, the field-theoretic core

`Hyp16.lean` shows that restriction of Kummer classes is injective modulo `n`-th powers:
`kummerRes (kummerMap a) = 1 ↔ a` becomes an `n`-th power in the extension. So the paper's
`ker res_{E/F} = U = ⟨(a₁),(a₂)⟩` is *equivalent* to a statement with no cohomology in it: for the
Kummer field `E = F(Δ^{1/p})`, an element of `Fˣ` that becomes a `p`-th power in `E` already lies in
`(Fˣ)^p·Δ`.

This file proves that statement in the form that the degree formula gives directly:

> if two Kummer fields agree, `F(Δ^{1/p}) = F(Δ'^{1/p})`, then `Δ' ≤ (Fˣ)^p·Δ`.

That is the classical argument, and it uses no cohomology at all:

* `TauCeti.finrank_kummerField`: `[F(Δ^{1/p}) : F] = [Δ : Δ ∩ (Fˣ)^p]`, i.e. the order of the image
  of `Δ` in `Fˣ⧸(Fˣ)^p`;
* equal fields give equal degrees, hence `Nat.card`-equal images of `Δ` and `Δ'` in `Fˣ⧸(Fˣ)^p`;
* since the image of `Δ` sits inside that of `Δ'`, the relative index is `1`, so the images are
  equal, and every element of `Δ'` is congruent to an element of `Δ` modulo `p`-th powers.

The hypothesis `μ_p ⊂ F` is `HasEnoughRootsOfUnity F p`; `hroots`/`hroots'` say that the radicals
have `p`-th roots in the separable closure, which is what makes the degree formula applicable.
-/

open TauCeti

set_option maxHeartbeats 1000000

namespace BKummer

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **Equal Kummer fields force containment of power classes**: if `F(Δ^{1/p}) = F(Δ'^{1/p})` and
`Δ ≤ Δ'`, then `Δ' ≤ (Fˣ)^p · Δ`, i.e. every element of `Δ'` is a `p`-th power times an element
of `Δ`. -/
theorem le_mul_pow_of_kummerField_eq {Δ Δ' : Subgroup Fˣ} (h : Δ ≤ Δ')
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ']
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) ↑b)
    (hroots' : ∀ b ∈ Δ', ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) ↑b)
    (hfield : kummerField (SeparableClosure F) p Δ = kummerField (SeparableClosure F) p Δ') :
    Δ' ≤ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  classical
  set P : Subgroup Fˣ := (powMonoidHom p : Fˣ →* Fˣ).range with hP
  set q : Fˣ →* Fˣ ⧸ P := QuotientGroup.mk' P with hq
  have hker : q.ker = P := QuotientGroup.ker_mk' P
  -- The image of a subgroup in `Fˣ ⧸ P` has `Nat.card` equal to the relative index.
  have hcard : ∀ K : Subgroup Fˣ, P.IsFiniteRelIndex K →
      Nat.card ↥(Subgroup.map q K) = P.relIndex K := by
    intro K _
    rw [← Subgroup.relIndex_ker K q, hker]
  -- Equal fields, equal degrees, equal indices.
  have hrel : P.relIndex Δ = P.relIndex Δ' := by
    rw [← finrank_kummerField (K := F) (E := SeparableClosure F) (n := p) (Δ := Δ) hroots,
      ← finrank_kummerField (K := F) (E := SeparableClosure F) (n := p) (Δ := Δ') hroots', hfield]
  have hmaps : Subgroup.map q Δ ≤ Subgroup.map q Δ' := Subgroup.map_mono h
  have hN : Nat.card ↥(Subgroup.map q Δ) = Nat.card ↥(Subgroup.map q Δ') := by
    rw [hcard Δ inferInstance, hcard Δ' inferInstance, hrel]
  have hN0 : Nat.card ↥(Subgroup.map q Δ) ≠ 0 := by
    rw [hcard Δ inferInstance]
    exact Subgroup.IsFiniteRelIndex.relIndex_ne_zero
  -- The relative index of the two images is therefore one.
  have hmul := Subgroup.relIndex_mul_card (H := Subgroup.map q Δ) (K := Subgroup.map q Δ')
  rw [inf_eq_left.2 hmaps, hN] at hmul
  have hpos : 0 < Nat.card ↥(Subgroup.map q Δ') := by
    rw [← hN]
    exact Nat.pos_of_ne_zero hN0
  have hone : (Subgroup.map q Δ).relIndex (Subgroup.map q Δ') = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hmul)
  have hle : Subgroup.map q Δ' ≤ Subgroup.map q Δ := Subgroup.relIndex_eq_one.1 hone
  -- Consequently every element of `Δ'` is congruent to an element of `Δ` modulo `p`-th powers.
  intro a ha
  have hqa : q a ∈ Subgroup.map q Δ := hle (Subgroup.mem_map_of_mem q ha)
  obtain ⟨δ, hδ, hδa⟩ := Subgroup.mem_map.1 hqa
  have hinv : δ⁻¹ * a ∈ P := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hδa, inv_mul_cancel]
  have hmem : (δ⁻¹ * a) * δ ∈ P ⊔ Δ := Subgroup.mul_mem_sup hinv hδ
  rwa [mul_comm (δ⁻¹ * a) δ, mul_inv_cancel_left] at hmem

end BKummer
