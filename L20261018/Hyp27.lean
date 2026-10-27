import L20261018.Hyp24
/-!
# `(a)`: the kernel of the **explicit** restriction map on Kummer classes

`Hyp24.lean` proves `prop:bi-kummer-kernel` in the Kummer model:
`kummerRes (kummerMap a) = 1 ↔ a ∈ (Fˣ)^p ⊔ Δ`.

`kummerRes` is by definition (`TauCeti.toAdd_kummerRes`) the composite

`H¹(G_F, KummerCoeff F p) --res--> H¹(E.fixingSubgroup, KummerCoeff F p) --pullback--> H¹(G_E, KummerCoeff E p)`,

where the second leg is the pullback along the group identification
`absoluteGaloisGroupEquivFixingSubgroup` and the coefficient identification `kummerCoeffMap`.
TauCeti's `explicitMap1_eq_zero_iff_explicitRes1_eq_zero` says this pullback leg (an isomorphism)
detects zero, so it can be stripped off. This file does that, giving the kernel statement for the
**explicit restriction map itself**:

`explicitRes1 E.fixingSubgroup (kummerMap a) = 0 ↔ a ∈ (Fˣ)^p ⊔ Δ`.
-/

open TauCeti ContCohomology

set_option maxHeartbeats 1000000

namespace KummerExplicit

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  {n : ℕ} (σ : L →ₐ[K] SeparableClosure K)

/-- `kummerCoeffMap` is a bijection (explicit inverse `kummerCoeffMapSymm`). -/
theorem kummerCoeffMap_bijective : Function.Bijective (kummerCoeffMap K n L σ) :=
  ⟨fun x y hxy => by
      have h := congrArg (kummerCoeffMapSymm K n L σ) hxy
      simpa [kummerCoeffMapSymm_kummerCoeffMap] using h,
    fun y => ⟨kummerCoeffMapSymm K n L σ y,
      by simp [kummerCoeffMap_kummerCoeffMapSymm]⟩⟩

/-- Equivariance of `kummerCoeffMap` for the composite
`G_L → Gal(Kˢ/σ(L)) ↪ G_K`. -/
theorem kummerCoeffMap_smul_comp (g : AbsoluteGaloisGroup L) (m : KummerCoeff K n) :
    kummerCoeffMap K n L σ
        (((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
          (absoluteGaloisGroupEquivFixingSubgroup K L σ : AbsoluteGaloisGroup L →ₜ*
            ↥σ.fieldRange.fixingSubgroup)) g • m)
      = g • kummerCoeffMap K n L σ m := by
  have hcoe : ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
        (absoluteGaloisGroupEquivFixingSubgroup K L σ : AbsoluteGaloisGroup L →ₜ*
          ↥σ.fieldRange.fixingSubgroup)) g
      = ↑(absoluteGaloisGroupEquivFixingSubgroup K L σ g) := by
    rw [ContinuousMonoidHom.coe_comp]
    rfl
  rw [hcoe]
  exact kummerCoeffMap_smul K n L σ g m

/-- **Bridge**: `kummerRes` rewritten as a single `explicitMap1` from `G_K`, i.e. restriction
followed by the identifications of the subgroup with `G_L`. -/
theorem kummerRes_toAdd_eq (x : Multiplicative (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n))) :
    (kummerRes K n L σ x).toAdd =
      explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L)
        (KummerCoeff L n)
        ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
          (absoluteGaloisGroupEquivFixingSubgroup K L σ : AbsoluteGaloisGroup L →ₜ*
            ↥σ.fieldRange.fixingSubgroup))
        (kummerCoeffMap K n L σ) continuous_of_discreteTopology
        (kummerCoeffMap_smul_comp σ) x.toAdd := by
  have hcomp := explicitMap1_comp (G := AbsoluteGaloisGroup K) (M := KummerCoeff K n)
    (H := ↥σ.fieldRange.fixingSubgroup) (N := KummerCoeff K n)
    (φ := ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup)
    (f := AddMonoidHom.id (KummerCoeff K n)) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul (KummerCoeff K n) σ.fieldRange.fixingSubgroup)
    (K := AbsoluteGaloisGroup L) (P := KummerCoeff L n)
    (ψ := absoluteGaloisGroupEquivFixingSubgroup K L σ) (q := kummerCoeffMap K n L σ)
    continuous_of_discreteTopology (kummerCoeffMap_smul K n L σ)
  rw [toAdd_kummerRes, explicitRes1_eq_explicitMap1]
  exact (DFunLike.congr_fun hcomp x.toAdd).symm

/-- **`kummerRes` vanishes exactly when the explicit restriction vanishes.** -/
theorem kummerRes_eq_one_iff_explicitRes1_eq_zero
    (x : Multiplicative (H1 (AbsoluteGaloisGroup K) (KummerCoeff K n))) :
    kummerRes K n L σ x = 1 ↔
      explicitRes1 (AbsoluteGaloisGroup K) (KummerCoeff K n)
        σ.fieldRange.fixingSubgroup x.toAdd = 0 := by
  have key := explicitMap1_eq_zero_iff_explicitRes1_eq_zero
    (G := AbsoluteGaloisGroup K) (M := KummerCoeff K n)
    (H := AbsoluteGaloisGroup L) (N := KummerCoeff L n)
    (S := σ.fieldRange.fixingSubgroup)
    (e := absoluteGaloisGroupEquivFixingSubgroup K L σ)
    (φ := (ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
      (absoluteGaloisGroupEquivFixingSubgroup K L σ : AbsoluteGaloisGroup L →ₜ*
        ↥(σ.fieldRange.fixingSubgroup)))
    rfl (kummerCoeffMap_bijective σ) (kummerCoeffMap_smul_comp σ) (c := x.toAdd)
  constructor
  · intro h
    have h' : (kummerRes K n L σ x).toAdd = 0 := by rw [h, toAdd_one]
    rw [kummerRes_toAdd_eq σ x] at h'
    exact key.1 h'
  · intro h
    have h0 : (kummerRes K n L σ x).toAdd = 0 := by
      rw [kummerRes_toAdd_eq σ x]
      exact key.2 h
    have := congrArg Multiplicative.ofAdd h0
    simpa using this

end KummerExplicit

namespace BKummer

variable {F : Type u} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`(a)`, explicit model**: restriction to the bi-Kummer extension `E = F(Δ^{1/p})` kills the
Kummer class of `a : Fˣ` exactly when `a ∈ (Fˣ)^p ⊔ Δ`. -/
theorem explicitRes1_kummerMap_eq_zero_iff (hp : IsUnit (p : F)) (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (a : Fˣ) :
    explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
        (IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
        (kummerMap F p hp a).toAdd = 0
      ↔ a ∈ (powMonoidHom p : Fˣ →* Fˣ).range ⊔ Δ := by
  rw [← KummerExplicit.kummerRes_eq_one_iff_explicitRes1_eq_zero
    (L := ↥(kummerField (SeparableClosure F) p Δ))
    (σ := IntermediateField.val (kummerField (SeparableClosure F) p Δ))]
  exact kummerRes_kummerMap_eq_one_iff_mem_sup hp Δ hroots a

/-- **Item `(a)`, explicit model**: `res_{E/F}((a₁)) = 0`. -/
theorem explicitRes1_kummerMap_a1 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex (Subgroup.closure ({a1, a2} : Set Fˣ))] :
    explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
      (IntermediateField.val
        (kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
      (kummerMap F p hp a1).toAdd = 0 :=
  (explicitRes1_kummerMap_eq_zero_iff hp _ hroots a1).2
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

/-- **Item `(a)`, explicit model**: `res_{E/F}((a₂)) = 0`. -/
theorem explicitRes1_kummerMap_a2 (hp : IsUnit (p : F)) (a1 a2 : Fˣ)
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex (Subgroup.closure ({a1, a2} : Set Fˣ))] :
    explicitRes1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
      (IntermediateField.val
        (kummerField (SeparableClosure F) p (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
      (kummerMap F p hp a2).toAdd = 0 :=
  (explicitRes1_kummerMap_eq_zero_iff hp _ hroots a2).2
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

end BKummer
