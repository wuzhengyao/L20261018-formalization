import Hyp302
import Hyp289

/-!
# R1193（**收口完成：`UnitsCupVanish` 无条件 ⟹ `∃ D` 与第 4 章三条无条件**）

`Hyp302.unitsCupVanish` 已在「离散 ＋ Hensel ＋ 有限剩余」下**无条件**给出
单位 × 单位杯积为零。本轮把它代入 `Hyp288`／`Hyp289`，消去 `hUU`：

| 声明 | 消去的输入 |
|---|---|
| **`exists_henselResidueData`** | `Hyp288.exists_henselResidueData_of_units_cup` 的 `hUU` |
| **`orth_eq_bot_of_discrete_valuation''`** | 4.2，`Hyp289` 版本的 `hUU` |
| **`thm_ramified_1_of_discrete_valuation''`** | 4.3(1) |
| **`corollary_4_4_of_discrete_valuation''`** | 4.4 |

⟹ `PROMPT-S33` §① 达成（除 `∅-bridge` `hbridge` 与 `⚠-tex-sourced`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section Closure

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [HenselianRing ↥𝒪[F] (IsLocalRing.maximalIdeal ↥𝒪[F])]
  [Finite (IsLocalRing.ResidueField ↥𝒪[F])]
variable (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★★★ **一般 Hensel 的 `D` 存在 —— 无条件**（除 `∅-bridge`）。

`hUU` 已由 `Hyp302.unitsCupVanish` 无条件给出。 -/
theorem exists_henselResidueData {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hskew : ∀ x y, ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) x y
      = -(((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1) y x)) :
    ∃ D : HenselResidueData (ZMod p)
        ↑(continuousCohomology 1 (ClassFieldTheory.muNRep p F)).toModuleCat
        ↑(continuousCohomology (1 + 1) (ClassFieldTheory.muNRep p F)).toModuleCat
        ↥(LinearMap.ker (valH1LinearGen (p := p) v hpF))
        ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1),
      D.val = valH1LinearGen (p := p) v hpF :=
  exists_henselResidueData_of_units_cup (p := p) hζ hp hpF hbridge hv hπ hp2 hskew
    (unitsCupVanish (p := p) hζ hp hpF hp2 hv)

/-- ★★★★★★ **4.2（`lem:ramified-vanishing`）—— `hUU` 已消**。 -/
theorem orth_eq_bot_of_discrete_valuation'' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (hp2' : NeZero (2 : ZMod p)) {a1 a2 : GaloBase.V F p}
    (hne : GaloBase.cup (K := F) (p := p) a1 a2 ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p) a1 a2,
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    ResidueCupData.orth (GaloBase.cup (K := F) (p := p)) a1 a2 = ⊥ :=
  orth_eq_bot_of_discrete_valuation' (F := F) (p := p) hp hpF hζ hbridge hv hπ hp2
    (unitsCupVanish (p := p) hζ hp hpF hp2 hv) hp2' hne hval

/-- ★★★★★★ **4.3(1) —— `hUU` 已消**。 -/
theorem thm_ramified_1_of_discrete_valuation'' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    (Δ : Subgroup Fˣ)
    [(powMonoidHom p : Fˣ →* Fˣ).range.IsFiniteRelIndex Δ]
    (hroots : ∀ b ∈ Δ, ∃ x : SeparableClosure F,
      x ^ p = algebraMap F (SeparableClosure F) (b : F))
    (hU : IsOpen ((IntermediateField.val (kummerField (SeparableClosure F) p Δ)).fieldRange.fixingSubgroup
      : Set (AbsoluteGaloisGroup F)))
    [FiniteDimensional F (Theo352.Efield (F := F) (p := p) Δ)]
    [IsGalois F (Theo352.Efield (F := F) (p := p) Δ)]
    {a1 a2 : Fˣ} (ha1 : a1 ∈ Δ) (ha2 : a2 ∈ Δ)
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (KummerBridge.kummerClass F p hpF a1) (KummerBridge.kummerClass F p hpF a2),
      valLinOf (F := F) (p := p) v hpF u ≠ 0)
    [FiniteDimensional (ZMod p) (GaloBase.V F p)] :
    (Theo352.Bex (F := F) (p := p) hpF hne).Uperp = ⊥ ∧
      Theo352.Nsub (F := F) (p := p) Δ = ⊥ :=
  thm_ramified_1_of_discrete_valuation' (F := F) (p := p) hp hpF hζ hbridge hv hπ hp2
    (unitsCupVanish (p := p) hζ hp hpF hp2 hv) Δ hroots hU ha1 ha2 hne hval

/-- ★★★★★★ **4.4（`cor:rank-barrier`）—— `hUU` 已消**。 -/
theorem corollary_4_4_of_discrete_valuation'' {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {v : Fˣ →* Multiplicative ℤ} {π : Fˣ}
    [Fact (Irreducible (X ^ p - C (π : F)))]
    [Module.Finite F (AdjoinRoot (X ^ p - C (π : F)))]
    (hp : IsUnit (p : ↥𝒪[F])) (hpF : IsUnit (p : F))
    (hbridge : ∀ a : Fˣ, H2Bridge.redEquiv1 hζ (KummerBridge.kummerClass F p hpF a)
      = ClassFieldTheory.kummerClass F hpF a)
    (hv : ValCompat (F := F) v) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    {a1 a2 : Fˣ}
    (hne : Theo352.cupLin (F := F)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2) ≠ 0)
    (hval : ∃ u ∈ ResidueCupData.plane (k := ZMod p)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
      (GaloCup.kummerExplicit (F := F) (p := p) hpF a2),
      valLinOf (F := F) (p := p) v hpF (KummerBridge.h1ToVEquiv F p u) ≠ 0)
    (hK1 : Module.finrank (ZMod p)
      ↥(LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) = 1)
    [FiniteDimensional (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p))]
    [NeZero (2 : ZMod p)] :
    Module.finrank (ZMod p)
        ↥(ResidueCupData.commonCupMap (Theo352.cupLin (F := F) (p := p))
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a1)
          (GaloCup.kummerExplicit (F := F) (p := p) hpF a2)).range = 2
      ∧ Module.finrank (ZMod p) (ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) = 2 :=
  corollary_4_4_of_discrete_valuation' (F := F) (p := p) hp hpF hζ hbridge hv hπ hp2
    (unitsCupVanish (p := p) hζ hp hpF hp2 hv) hne hval hK1

end Closure

end L20261018

#print axioms L20261018.exists_henselResidueData
#print axioms L20261018.orth_eq_bot_of_discrete_valuation''
#print axioms L20261018.thm_ramified_1_of_discrete_valuation''
#print axioms L20261018.corollary_4_4_of_discrete_valuation''
