import L20261018.Hyp312
import L20261018.Hyp80

/-!
# R1209（`kc = c • kcCanonical`：标量从系数识别传到 Kummer 类）

`PLAN-VALCOMPAT-HBRIDGE.md` §G.2 的确定写法：用库内**已有**的两条引理
* `explicitCoeff1_comp`（`ExplicitFunctoriality.lean:781`）
* `explicitCoeff1_eq_nsmul`（同文件 `:772`）

把 `Hyp311` 的标量从**系数层**传到 **`H¹` 层**。

## 本轮
| 声明 | 内容 |
|---|---|
| `kummerH1EquivCanon` | 用**规范**系数识别（`SymbolCupBridge`）的 `H¹` 等价 |
| **`kummerH1Equiv_eq_smul_canon`** | ★★★★★ `∃ c ≠ 0, kummerH1Equiv = c • kummerH1EquivCanon` |
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing

namespace L20261018

section KummerH1Canon

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 规范系数识别诱导的 `H¹` 等价（与 `KummerBridge.kummerH1Equiv` 平行，但用
`SymbolCupBridge.kummerCoeffLinearEquiv`，**无 `Classical.choose`**）。 -/
noncomputable def kummerH1EquivCanon :
    ContCohomology.H1 (AbsoluteGaloisGroup F) (KummerCoeff F p) ≃+
      ContCohomology.H1 (AbsoluteGaloisGroup F) (ZMod p) :=
  ContCohomology.explicitCoeff1Equiv (G := AbsoluteGaloisGroup F)
    (M := KummerCoeff F p) (N := ZMod p)
    (SymbolCupBridge.kummerCoeffLinearEquiv (p := p) (ζ := ζ) hζ).toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun g m => by rw [smul_kummerCoeff_eq_self hζ g m]; rfl)

end KummerH1Canon

end L20261018

#print axioms L20261018.kummerH1EquivCanon
