import L20261018.Hyp339
import L20261018.Hyp323

/-! # R1250：`∃D` 在战役载体上、无 `[Finite (ResidueField)]`（`VKern` 命名载体避免 whnf 爆炸） -/

set_option maxHeartbeats 8000000
open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

variable {F : Type} [Field F]
variable {p : ℕ} [NeZero p] [Fact p.Prime]
variable {v : Fˣ →* Multiplicative ℤ}

/-- 命名载体 `↥(ker (valH1LinearGen v hpF))`（必须显式带 `F`／`p`／`v`，否则隐参被丢）。 -/
noncomputable abbrev VKern (F : Type) [Field F] (p : ℕ) [NeZero p] [Fact p.Prime]
    (v : Fˣ →* Multiplicative ℤ) (hpF : IsUnit (p : F)) : Type :=
  ↥(LinearMap.ker (valH1LinearGen (F := F) (p := p) v hpF))

/-- ★★★★★★ **`∃D`（无 `[Finite (ResidueField)]`／无 Hensel／无 DVR）**。 -/
theorem exists_henselResidueData_noFinite (hpF : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {π : Fˣ} (hπ : v π = Multiplicative.ofAdd (1 : ℤ))
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x))
    (d : ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat →ₗ[ZMod p]
      VKern F p v hpF)
    (hd_infl : ∀ y z : VKern F p v hpF,
      d (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) (y : _) (z : _)) = 0)
    (hd_cup_pi : ∀ y : VKern F p v hpF,
      d (((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) (y : _)
        (ClassFieldTheory.kummerClass F hpF π)) = y) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        (VKern F p v hpF) ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF := by
  have hpi : valH1LinearGen (p := p) (F := F) v hpF
      (ClassFieldTheory.kummerClass F hpF π) = 1 := by
    have hg : valH1Gen (p := p) v hpF (ClassFieldTheory.kummerClass F hpF π) = 1 := by
      rw [valH1Gen_kummerClass, hπ]; simp
    exact hg
  exact exists_henselResidueData_of_residueMap
    ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
    (valH1LinearGen (p := p) v hpF) (ClassFieldTheory.kummerClass F hpF π) hpi hskew
    (LinearMap.ker (valH1LinearGen (p := p) v hpF)).subtype (fun y => y.2)
    (fun x hx => ⟨⟨x, hx⟩, rfl⟩) d hd_infl hd_cup_pi

end L20261018
#print axioms L20261018.exists_henselResidueData_noFinite
