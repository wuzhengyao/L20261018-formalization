import L20261018.Hyp24
import L20261018.Hyp19
/-!
# `(a)`: the Kummer class as a homomorphism on `Fˣ`, and restriction of the two generators

`Hyp19.kummerClass` sends `a : Fˣ` to the paper's class `(a) ∈ V = H¹(F, μ_p)`. It is built from the
multiplicative Kummer map composed with additive equivalences, hence is a **group homomorphism**
`Fˣ →* Multiplicative V`. This file packages that, derives that two classes coincide exactly when
the quotient of their arguments is a `p`-th power, and records the paper's item `(a)`: the two
generators `a₁, a₂` die under restriction to the bi-Kummer extension `F(Δ^{1/p})`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace KummerBridge

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- The Kummer class map `a ↦ (a)` as a homomorphism of groups `Fˣ →* Multiplicative V`. -/
noncomputable def kummerClassHom (hp : IsUnit (p : F)) :
    Fˣ →* Multiplicative (GaloBase.V F p) :=
  ((h1ToVEquiv (F := F) (p := p)).toAddMonoidHom.toMultiplicative).comp
    (((kummerH1Equiv (F := F) (p := p) hp).toAddMonoidHom.toMultiplicative).comp
      (kummerMap F p hp))

@[simp]
theorem kummerClassHom_apply (hp : IsUnit (p : F)) (a : Fˣ) :
    kummerClassHom (F := F) (p := p) hp a = Multiplicative.ofAdd (kummerClass F p hp a) :=
  rfl

/-- **The classes of `a` and `b` coincide iff `a b⁻¹` is a `p`-th power**: the map `a ↦ (a)` is
injective modulo `p`-th powers. -/
theorem kummerClass_eq_iff (hp : IsUnit (p : F)) (a b : Fˣ) :
    kummerClass F p hp a = kummerClass F p hp b ↔
      a * b⁻¹ ∈ (powMonoidHom p : Fˣ →* Fˣ).range := by
  constructor
  · intro h
    have h1 : kummerClassHom (F := F) (p := p) hp (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, kummerClassHom_apply, kummerClassHom_apply, h]
      simp
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [kummerClassHom_apply, toAdd_ofAdd, toAdd_one] at h2
    exact (kummerClass_eq_zero_iff (F := F) (p := p) hp _).1 h2
  · intro h
    have h1 : kummerClassHom (F := F) (p := p) hp (a * b⁻¹) = 1 := by
      rw [kummerClassHom_apply, (kummerClass_eq_zero_iff (F := F) (p := p) hp _).2 h]
      simp
    rw [map_mul, map_inv] at h1
    have h2 : kummerClassHom (F := F) (p := p) hp a = kummerClassHom (F := F) (p := p) hp b :=
      mul_inv_eq_one.1 h1
    have h3 := congrArg Multiplicative.toAdd h2
    simpa only [kummerClassHom_apply, toAdd_ofAdd] using h3

end KummerBridge

namespace BKummer

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- The easy direction of `prop:bi-kummer-kernel`: everything in `(Fˣ)^p ⊔ Δ` is killed by
restriction to `F(Δ^{1/p})`. -/
theorem kummerRes_kummerMap_eq_one_of_mem_sup (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    {a : Fˣ} (ha : a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ) :
    kummerRes F p ↥(kummerField (SeparableClosure F) p Δ)
      (IntermediateField.val (kummerField (SeparableClosure F) p Δ))
      (kummerMap F p hp a) = 1 :=
  (kummerRes_kummerMap_eq_one_iff_mem_sup hp Δ hroots a).2 ha

/-- **Item `(a)` for the first generator**: `res_{E/F}((a₁)) = 0`. -/
theorem kummerRes_kummerMap_a1 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex (Subgroup.closure ({a1, a2} : Set Fˣ))] :
    kummerRes F p
      ↥(kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ)))
      (IntermediateField.val
        (kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ))))
      (kummerMap F p hp a1) = 1 :=
  kummerRes_kummerMap_eq_one_of_mem_sup hp _ hroots
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

/-- **Item `(a)` for the second generator**: `res_{E/F}((a₂)) = 0`. -/
theorem kummerRes_kummerMap_a2 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex (Subgroup.closure ({a1, a2} : Set Fˣ))] :
    kummerRes F p
      ↥(kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ)))
      (IntermediateField.val
        (kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ))))
      (kummerMap F p hp a2) = 1 :=
  kummerRes_kummerMap_eq_one_of_mem_sup hp _ hroots
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

end BKummer
