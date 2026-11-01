import Hyp749
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison

/-!
# S68 R5：A-1 —— **二级载体的方阵** `infl2Res ∘ eQ₂ = h2ToGaloBase ∘ explicitMap2`

## 为什么需要

`hd_infl`（`PROMPT-S68` §②A2）要证 `d (cup y z) = 0`（`y z ∈ VKG`）。路线：
`cup y z ∈ residueSpan ≤ range infl₂`（`Hyp744` ＋ `Hyp749.unramifiedKummer`）⟹ `cup y z = infl2Res w`
⟹ 需要 `∂² (infl2Res w) = 0`。而库内已机检的 `∂² ∘ Inf₂ = 0`（`Hyp743`）用的是**另一个载体**：
`map φ (ofDiscreteModulePair φ subtype) 2`（`ofDiscreteModule ℤ (Γ⧸I) (M^I)`），
`infl2Res = map φ coeffIdHom 2`（`muPQuot`）。

本件给出与 `Hyp748` 一级方阵**完全平行**的二级方阵，工具全部复用：
`Hyp748.restrictScalarsIntEquiv_map`（对一切 `n` 成立）、
`Hyp748.resRestrictScalarsIntMap_coeffIdHom_eq_pair`（级无关态射等式）、
库内 `explicitH2AddEquivContinuousCohomology_map`。

## 交付

| 声明 | 内容 |
|---|---|
| `eQ2` | `H²(Γ⧸I, μ_p)` 的显式模型 ≃ `ResH2Type` |
| `h2ToGaloBase` | `H²(Γ, μ_p)` 的显式模型 ≃ `GaloBase.H2` |
| **`infl2Res_eQ2`** | ★★★★★ `infl2Res (eQ₂ x) = h2ToGaloBase (explicitMap2 … x)` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology

namespace L20261018

section DegreeTwo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★★ **`H²(Γ⧸I, μ_p)` 的显式模型 ≃ 战役载体 `ResH2Type`**
（`explicitH2AddEquivContinuousCohomology` ＋ `restrictScalarsIntEquiv`；一级版是 `Hyp748.eQ`）。 -/
noncomputable def eQ2 :
    H2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) ≃+ ResH2Type (F := F) p I :=
  (explicitH2AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p)).trans
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I)
      (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 2)

/-- ★★★★ **`H²(Γ, μ_p)` 的显式模型 ≃ `GaloBase.H2`**（一级版是 `KummerBridge.h1ToVEquiv`）。 -/
noncomputable def h2ToGaloBase :
    H2 (AbsoluteGaloisGroup F) (ZMod p) ≃+ GaloBase.H2 F p :=
  (explicitH2AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)).trans
    (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2)

/-- ★★★★★ **二级方阵**：`infl2Res (eQ₂ x) = h2ToGaloBase (explicitMap2 … x)`。

与 `Hyp748.infl1Res_eQ` 同一证明（标量限制交换 ＋ `coeffIdHom` 是恒等系数对 ＋ 显式↔规范方阵）。 -/
theorem infl2Res_eQ2 (x : H2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)) :
    infl2Res (F := F) (p := p) I (eQ2 (F := F) (p := p) I x)
      = h2ToGaloBase (F := F) (p := p)
          (explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (AbsoluteGaloisGroup F) (ZMod p)
            (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
            continuous_of_discreteTopology (fun _ _ => rfl) x) := by
  show (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        (coeffIdHom (F := F) p I) 2)
      ((restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F ⧸ I)
        (muPQuot (AbsoluteGaloisGroup F ⧸ I) p) 2)
        (explicitH2AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I)
          (M := ZMod p) x))
    = (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2)
        (explicitH2AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F) (M := ZMod p)
          (explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (AbsoluteGaloisGroup F) (ZMod p)
            (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
            continuous_of_discreteTopology (fun _ _ => rfl) x))
  rw [← restrictScalarsIntEquiv_map (p := p) (n := 2)
    (G := AbsoluteGaloisGroup F ⧸ I) (H := AbsoluteGaloisGroup F)
    (X := muPQuot (AbsoluteGaloisGroup F ⧸ I) p) (Y := GaloBase.muP F p)
    (φ := (Subgroup.quotientMkContinuousMonoidHom I))
    (f := coeffIdHom (F := F) p I)
    (explicitH2AddEquivContinuousCohomology (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p) x)]
  rw [resRestrictScalarsIntMap_coeffIdHom_eq_pair (F := F) (p := p) I]
  exact congrArg (restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 2)
    (explicitH2AddEquivContinuousCohomology_map (G := AbsoluteGaloisGroup F ⧸ I)
      (M := ZMod p) (H := AbsoluteGaloisGroup F) (N := ZMod p)
      (Subgroup.quotientMkContinuousMonoidHom I) (AddMonoidHom.id (ZMod p))
      (fun _ _ => rfl) x)

end DegreeTwo

end L20261018

#print axioms L20261018.eQ2
#print axioms L20261018.h2ToGaloBase
#print axioms L20261018.infl2Res_eQ2
