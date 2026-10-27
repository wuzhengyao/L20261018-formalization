import L20261018.Hyp16
import L20261018.Hyp18
/-!
# `prop:bi-kummer-kernel`: the kernel of restriction on Kummer classes

Chapter 2's `prop:bi-kummer-kernel` states `ker(res_{E/F}) = U = ⟨(a_1), (a_2)⟩` for the bi-Kummer
extension `E = F(a_1^{1/p}, a_2^{1/p})`. Campaign item (e) proved its two halves separately:

* `Hyp16.lean`: `kummerRes (kummerMap a) = 1 ↔ a` becomes an `n`-th power in the extension;
* `Hyp18.lean`: if `a` becomes a `p`-th power in `F(Δ^{1/p})`, then `a ∈ (Fˣ)^p ⊔ Δ`.

This file composes them into the kernel statement itself, in the Kummer-theoretic model:

`kummerRes (kummerMap a) = 1 ↔ a ∈ (Fˣ)^p ⊔ Δ`,

i.e. the classes killed by restriction to `E = F(Δ^{1/p})` are exactly the power classes spanned by
`Δ`. For `Δ = ⟨a_1, a_2⟩` this is `ker res = U` read through the Kummer isomorphism.
-/

open TauCeti

set_option maxHeartbeats 1000000

namespace BKummer

universe u

variable {F : Type u} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- The Kummer field `F(Δ^{1/p})` as a field. -/
abbrev KF (Δ : Subgroup Fˣ) : Type u := ↥(kummerField (SeparableClosure F) p Δ)

/-- **`(a)` + `(e)` composed**: an element `a : Fˣ` is killed by restriction to the bi-Kummer
extension `F(Δ^{1/p})` exactly when `a ∈ (Fˣ)^p ⊔ Δ` — the kernel statement
`prop:bi-kummer-kernel` in the Kummer-theoretic model. -/
theorem kummerRes_kummerMap_eq_one_iff_mem_sup (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (a : Fˣ) :
    kummerRes F p (KF (p := p) Δ)
        (IntermediateField.val (kummerField (SeparableClosure F) p Δ))
        (kummerMap F p hp a) = 1
      ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · -- restriction kills `a` ⟹ `a` is a `p`-th power in the Kummer field ⟹ `a ∈ P ⊔ Δ`
    intro h
    obtain ⟨b, hb⟩ := (kummerRes_kummerMap_eq_one_iff (K := F) (L := KF (p := p) Δ)
      (n := p) (IntermediateField.val (kummerField (SeparableClosure F) p Δ)) hp a).1 h
    have hb' : ((b : KF (p := p) Δ) : SeparableClosure F) ^ p
        = algebraMap F (SeparableClosure F) (a : F) := by
      have hv := congrArg (fun u : (KF (p := p) Δ)ˣ => ((u : KF (p := p) Δ) : SeparableClosure F)) hb
      simpa using hv.symm
    exact mem_sup_of_isPow_in_kummerField Δ (a := a)
      (α := ((b : KF (p := p) Δ) : SeparableClosure F)) hroots hb'
      (b : KF (p := p) Δ).2
  · -- `a ∈ P ⊔ Δ` ⟹ `a` is a `p`-th power in the Kummer field ⟹ restriction kills it
    intro ha
    obtain ⟨c, hc, δ, hδ, hcδ⟩ := Subgroup.mem_sup.1 ha
    obtain ⟨d, rfl⟩ := hc
    obtain ⟨x, hx⟩ := hroots δ hδ
    have hxL : x ∈ kummerField (SeparableClosure F) p Δ :=
      mem_kummerField_of_pow_eq hδ hx
    have hne : (algebraMap F (SeparableClosure F) (δ : F)) ≠ 0 := by simpa using δ.ne_zero
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne p)] at hx
      exact hne hx.symm
    -- the `p`-th root of `algebraMap δ` inside the Kummer field, as a unit
    set xu : KF (p := p) Δ := ⟨x, hxL⟩ with hxu
    have hxu0 : (xu : KF (p := p) Δ) ≠ 0 := by
      intro h
      have : (xu : KF (p := p) Δ) = 0 := h
      exact hx0 (by simpa [hxu] using congrArg Subtype.val this)
    have hxup : (Units.mk0 (xu : KF (p := p) Δ) hxu0) ^ p
        = Units.map (algebraMap F (KF (p := p) Δ)).toMonoidHom δ := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      apply Subtype.ext
      show ((x : SeparableClosure F)) ^ p = algebraMap F (SeparableClosure F) (δ : F)
      simpa [hxu] using hx
    -- the prescribed root of `a`, as a unit of the Kummer field
    refine (kummerRes_kummerMap_eq_one_iff (K := F) (L := KF (p := p) Δ)
      (n := p) (IntermediateField.val (kummerField (SeparableClosure F) p Δ)) hp a).2 ?_
    refine ⟨Units.map (algebraMap F (KF (p := p) Δ)).toMonoidHom d
      * Units.mk0 (xu : KF (p := p) Δ) hxu0, ?_⟩
    rw [mul_pow, hxup, ← hcδ, map_mul, powMonoidHom_apply, map_pow]

end BKummer
