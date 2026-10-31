import Hyp309
import Hyp303

/-!
# R1201（**无条件版装配**：`v` 与 `D` 同时存在）

`PLAN-VALCOMPAT-HBRIDGE.md` §A 的最后一步。

## 本轮
| 声明 | 内容 |
|---|---|
| `moduleFinite_adjoinRoot` | ★★★★ `Module.Finite F (AdjoinRoot (X^p − C a))`（`PowerBasis.finite` ＋ `natDegree_X_pow_C`） |
| **`exists_henselResidueData_uncond`** | ★★★★★★ **`∃ v, ValCompat v ∧ ∃ D, D.val = valH1LinearGen v hpF`**（`hv`/`hπ`/`Fact`/`Module.Finite` 全部消去） |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section ModuleFinite

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime]

/-- ★★★★ **`AdjoinRoot (X^p − C a)` 是有限 `F`-模**（本 pin 无现成实例）。 -/
theorem moduleFinite_adjoinRoot (a : F) : Module.Finite F (AdjoinRoot (X ^ p - C a)) := by
  have hf : X ^ p - C a ≠ 0 := by
    intro h
    have h0 : (X ^ p - C a).natDegree = 0 := by rw [h]; simp
    rw [natDegree_X_pow_sub_C] at h0
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact PowerBasis.finite (AdjoinRoot.powerBasis hf)

end ModuleFinite

section Uncond

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
  [IsDiscreteValuationRing ↥𝒪[F]]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★★ **无条件版**：`hv`／`hπ`／`[Fact (Irreducible …)]`／`[Module.Finite …]` **全部消去**
（`v` 仍出现在结论的类型中，故以 `∃ v` 的形式给出；取 `v := vCompatHom`）。

只多一条假设 `[IsDiscreteValuationRing ↥𝒪[F]]`（「离散」），
这本来就被 `hπ : v π = ofAdd 1` 隐含。 -/
theorem exists_henselResidueData_uncond {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x)) :
    ∃ (v : Fˣ →* Multiplicative ℤ),
      ValCompat (F := F) v ∧
      ∃ D : HenselResidueData (ZMod p)
          ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
          ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
          ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
          ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
        D.val = valH1LinearGen (p := p) v hpF := by
  obtain ⟨π, hzπ, hnotpow⟩ :=
    exists_uniformizer_not_pow (F := F) (p := p) (Fact.out : p.Prime).ne_one
  haveI hIrred : Fact (Irreducible (X ^ p - C (π : F))) :=
    ⟨(capelli_irreducible_iff (F := F) (p := p) hp2).mpr hnotpow⟩
  haveI hFin : Module.Finite F (AdjoinRoot (X ^ p - C (π : F))) :=
    moduleFinite_adjoinRoot (p := p) (π : F)
  have hπ : vCompatHom (F := F) π = Multiplicative.ofAdd (1 : ℤ) := by
    rw [show vCompatHom (F := F) π = Multiplicative.ofAdd (zval (F := F) π) from rfl, hzπ]
  exact ⟨vCompatHom, valCompat_of_dvr,
    exists_henselResidueData (F := F) (p := p) hζ hp hpF hbridge
      valCompat_of_dvr hπ hp2 hskew⟩

end Uncond

end L20261018

#print axioms L20261018.moduleFinite_adjoinRoot
#print axioms L20261018.exists_henselResidueData_uncond
