import L20261018.Hyp106
/-!
# 3.6（`thm:dimension`）真实对象版 —— 最终装配（R934）
-/

open TauCeti ContCohomology

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Assemble36

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]

-- @source file=raw/L20261018.tex locator=label:thm:dimension quote="\dim_{\Fp}(U^\perp/N)=\tau-\kappa-r+2"
theorem theorem_3_6_explicit (hp : IsUnit (p : F)) (hp2 : p ≠ 2) {a1 a2 : Fˣ}
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex
      (Subgroup.closure ({a1, a2} : Set Fˣ))]
    (hroots : ∀ b ∈ Subgroup.closure ({a1, a2} : Set Fˣ),
      ∃ x : SeparableClosure F, x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p
      (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [((IntermediateField.val (kummerField (SeparableClosure F) p
      (Subgroup.closure ({a1, a2} : Set Fˣ)))).fieldRange.fixingSubgroup).FiniteIndex]
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    [IsGalois F (Theo352.Efield (F := F) (p := p)
      (Subgroup.closure ({a1, a2} : Set Fˣ)))]
    [Finite (H1 (AbsoluteGaloisGroup F) (ZMod p))]
    (hne : Theo352.cupLin (F := F) (GaloCup.kummerExplicit (F := F) (p := p) hp a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hp a2) ≠ 0) :
    Module.finrank (ZMod p)
        ((Theo352.Bex (F := F) (p := p) hp hne).Uperp ⧸
          (Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).comap
            (Theo352.Bex (F := F) (p := p) hp hne).Uperp.subtype)
      + (Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range - 2)
      = Module.finrank (ZMod p) (H0ex (K := F) (p := p) (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ))))
        - Module.finrank (ZMod p) (K2ex (K := F) (p := p) (Theo352.Efield (F := F) (p := p)
            (Subgroup.closure ({a1, a2} : Set Fˣ))))
    ∧ Module.finrank (ZMod p) ↥(Theo352.Nsub (F := F) (p := p)
          (Subgroup.closure ({a1, a2} : Set Fˣ)))
        + Module.finrank (ZMod p)
          ((Theo352.Bex (F := F) (p := p) hp hne).Uperp ⧸
            (Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).comap
              (Theo352.Bex (F := F) (p := p) hp hne).Uperp.subtype)
        = Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Uperp
    ∧ Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Uperp
        + Module.finrank (ZMod p) ↥(Theo352.Bex (F := F) (p := p) hp hne).Phi.range
        = Module.finrank (ZMod p) (H1 (AbsoluteGaloisGroup F) (ZMod p)) := by
  haveI h2 : NeZero (2 : ZMod p) := neZero_two_zmod hp2
  set E := Theo352.Efield (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))
  have ha1 : a1 ∈ Subgroup.closure ({a1, a2} : Set Fˣ) := Subgroup.subset_closure (by simp)
  have ha2 : a2 ∈ Subgroup.closure ({a1, a2} : Set Fˣ) := Subgroup.subset_closure (by simp)
  obtain ⟨φ₀, ψ₀, hφ₀, hψ₀, hex₀⟩ := three_five_one_Bex (F := F) (p := p) hp hroots hne
  obtain ⟨j, q, hj, hq, hex2⟩ :=
    Theo352.theorem_3_5_2_explicit (F := F) (p := p) hp hp2
      (Subgroup.closure ({a1, a2} : Set Fˣ)) hroots hU (a1 := a1) (a2 := a2) ha1 ha2 hne
  have hNU : Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))
      ≤ (Theo352.Bex (F := F) (p := p) hp hne).Uperp :=
    Nsub_le_Uperp (F := F) (p := p) hp hp2 (Subgroup.closure ({a1, a2} : Set Fˣ))
      hroots hU (a1 := a1) (a2 := a2) ha1 ha2 hne
  haveI hH0 : Module.Finite (ZMod p) (H0ex (K := F) (p := p) E) :=
    moduleFinite_H0ex (K := F) (p := p) E
  haveI hK2 : Module.Finite (ZMod p) (K2ex (K := F) (p := p) E) :=
    moduleFinite_K2ex (K := F) (p := p) E
  -- 商搬运（`AddEquiv`，是函数）
  let e := quotientAddEquivOfEq (V := H1 (AbsoluteGaloisGroup F) (ZMod p))
    (A := ((Theo352.Bex (F := F) (p := p) hp hne).U ⊔
      Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).toAddSubgroup)
    (B := ((Theo352.Bex (F := F) (p := p) hp hne).U).toAddSubgroup ⊔
      (Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))).toAddSubgroup)
    (by rw [submodule_sup_toAddSubgroup])
  let φ : (H1 (AbsoluteGaloisGroup F) (ZMod p) ⧸
      ((Theo352.Bex (F := F) (p := p) hp hne).U ⊔
        Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))))
      →ₗ[ZMod p] (H0ex (K := F) (p := p) E) :=
    toLinearMapOfAddEquiv (p := p) e φ₀
  let ψ : (H0ex (K := F) (p := p) E) →ₗ[ZMod p] (K2ex (K := F) (p := p) E) :=
    toLinearMapOfAddEquiv (p := p) (AddEquiv.refl (H0ex (K := F) (p := p) E)) ψ₀
  have hφ : Function.Injective φ := toLinearMapOfAddEquiv_injective (p := p) e hφ₀
  have hψ : Function.Surjective ψ :=
    toLinearMapOfAddEquiv_surjective (p := p) (AddEquiv.refl (H0ex (K := F) (p := p) E)) hψ₀
  have hex : LinearMap.range φ = LinearMap.ker ψ := by
    ext y
    show (∃ x, φ₀ (e x) = y) ↔ ψ₀ y = 0
    rw [show (∃ x, φ₀ (e x) = y) ↔ (∃ z, φ₀ z = y) from
      ⟨fun ⟨x, hx⟩ => ⟨e x, hx⟩,
        fun ⟨z, hz⟩ => ⟨e.symm z, by rw [AddEquiv.apply_symm_apply]; exact hz⟩⟩]
    exact SetLike.ext_iff.mp hex₀ y
  exact L20261018.BiKummerData.theorem_3_6 (B := Theo352.Bex (F := F) (p := p) hp hne)
    (N := Theo352.Nsub (F := F) (p := p) (Subgroup.closure ({a1, a2} : Set Fˣ))) hNU
    φ ψ hφ hψ hex j q hj hq hex2

end Assemble36

#print axioms Assemble36.theorem_3_6_explicit
