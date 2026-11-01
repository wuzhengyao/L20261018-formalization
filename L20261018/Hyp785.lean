import Hyp784

/-!
# S75 R2：**连续模型的 `H⁰`-Leibniz**（`PROMPT-S75` §1.1 的靶子）

## 本件做什么

`Hyp784.explicitLeibniz_cup01` 在**显式模型**里给出

```
S.explicitDelta1 (z₀ ⌣ y) = (S.explicitDelta0 z₀) ⌣ y          z₀ ∈ H⁰(Γ, C),  y ∈ H¹(Γ, μ_p)
```

本件用库内的两条桥把它搬到**连续模型**（Mathlib 的 `continuousCohomology`）：

| 桥 | 名称 | 位置 |
|---|---|---|
| `δ⁰` | `DiscreteShortExact.explicitIso_delta0` | `ConnectingMapComparison.lean:79` |
| `δ¹` | `DiscreteShortExact.explicitIso_delta1` | 同上 `:126` |
| `hom`↔`AddEquiv` | `explicitH1/H2IsoContinuousCohomology_hom_apply` | `CohomologyComparison.lean` |
| cup `(0,1)`／`(1,1)` | `explicitAddEquiv_cup01`／`explicitAddEquiv_cup11` | `Cup/Comparison.lean` |

**⟹ 交付**（`S = contCoindSES p`，`cup` = `TopPairing.cup`）：

```
contLeibniz_cup01 : (S.delta 1).hom (cup01 x y) = cup11 ((S.delta 0).hom x) y
```

这正是 `PROMPT-S75` §1.1 的 `δ₁(Inf z₀ ⌣ Inf a) = δ₀(Inf z₀) ⌣ Inf a` 的**一般形**（取
`x = Inf z₀` 即得；`Inf z₀` 的定义在下一件）。

## 诚实边界

* 本件**不含** `Infl⁻¹`／`contM` 段（`GAP3-PLAN` §11.3 的第 3–5 步）——下一件。
* 技术实例 `[LocallyCompactSpace Γ]` 由 `CompactSpace` 自动合成（慢，见文件头 `synthInstance` 设置）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-! ### 1. 两条桥：`δ⁰`／`δ¹` 的「连续 = 显式」 -/

/-- ★★★ **`δ¹` 的桥（加性等价版）**：`S.delta 1` 在连续模型上等于显式 `explicitDelta1` 的搬运。

由库内 `explicitIso_delta1`（`TopModuleCat` 版）＋ `explicitH1/H2IsoContinuousCohomology_hom_apply`
得到；`discreteH1Equiv`／`discreteH2Equiv` 都是 `AddEquiv.refl`，故只剩
`AddEquiv.apply_symm_apply`。 -/
theorem coindSES_delta_one_eq_explicit (x : DiscreteH1 (AbsoluteGaloisGroup F) (contC (F := F) p)) :
    ((contCoindSES (F := F) p).delta 1).hom
        (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p) x)
      = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((contCoindSES (F := F) p).explicitDelta1 x) := by
  have h := DiscreteShortExact.explicitIso_delta1 (S := contCoindSES (F := F) p) x
  rw [explicitH1IsoContinuousCohomology_hom_apply] at h
  simp only [discreteH1Equiv] at h
  rw [explicitH2IsoContinuousCohomology_hom_apply] at h
  simp only [discreteH2Equiv] at h
  exact h

/-- ★★★ **`δ⁰` 的桥（加性等价版）**：`S.delta 0` 在连续模型上等于显式 `explicitDelta0` 的搬运。 -/
theorem coindSES_delta_zero_eq_explicit (z₀ : ↥(H0 (AbsoluteGaloisGroup F) (contC (F := F) p))) :
    ((contCoindSES (F := F) p).delta 0).hom
        ((CategoryTheory.ConcreteCategory.hom
          (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀)
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((contCoindSES (F := F) p).explicitDelta0 z₀) := by
  have h := DiscreteShortExact.explicitIso_delta0 (S := contCoindSES (F := F) p) z₀
  rw [explicitH1IsoContinuousCohomology_hom_apply] at h
  simp only [discreteH1Equiv] at h
  exact h

/-! ### 2. ★★★★ **连续模型的 `H⁰`-Leibniz** -/

/-- ★★★★★ **连续模型的 `H⁰`-Leibniz**：`δ¹ (x ⌣ y) = δ⁰(x) ⌣ y`。

`x ∈ H⁰(Γ, C)`（`C = Coind Γ ⊥ μ_p ⧸ μ_p`），`y ∈ H¹(Γ, μ_p)`；`⌣` 是 `TopPairing.cup`，
配对分别为 `C ⊗ μ_p → C`（`smulPairingC`）与 `μ_p ⊗ μ_p → μ_p`（`mulPairing`）。

这是 GS `lemma-residue-cup-product`（印版 6.8.4）在 `p = 0` 处的一支；`PROMPT-S75` §1.1 的
`δ₁(Inf z₀ ⌣ Inf a) = δ₀(Inf z₀) ⌣ Inf a` 取 `x = Inf z₀` 即得。 -/
theorem contLeibniz_cup01 (z₀ : ↥(H0 (AbsoluteGaloisGroup F) (contC (F := F) p)))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    ((contCoindSES (F := F) p).delta 1).hom
        (((ofDiscreteModulePairing (smulPairingC (F := F) p)
            (smulPairingC_equivariant (F := F) p)).cup 0 1)
          ((CategoryTheory.ConcreteCategory.hom
            (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀)
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y))
      = ((ofDiscreteModulePairing (mulPairing (p := p))
            (mulPairing_equivariant (F := F) p)).cup 1 1)
          (((contCoindSES (F := F) p).delta 0).hom
            ((CategoryTheory.ConcreteCategory.hom
              (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀))
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y) := by
  -- 两侧都归到 `e₂ (explicitCup11 (S.explicitDelta0 z₀) y)`
  have hcup01 :
      ((ofDiscreteModulePairing (smulPairingC (F := F) p)
          (smulPairingC_equivariant (F := F) p)).cup 0 1)
        ((CategoryTheory.ConcreteCategory.hom
          (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀)
        ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y)
      = explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)
          (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p) (contC (F := F) p)
            (smulPairingC (F := F) p) continuous_of_discreteTopology
            (smulPairingC_equivariant (F := F) p) z₀ y) :=
    explicitAddEquiv_cup01 (G := AbsoluteGaloisGroup F) (M := contC (F := F) p) (N := ZMod p)
      (P := contC (F := F) p) (μ := smulPairingC (F := F) p)
      (hequiv := smulPairingC_equivariant (F := F) p) z₀ y
  have hcup11 :
      ((ofDiscreteModulePairing (mulPairing (p := p))
          (mulPairing_equivariant (F := F) p)).cup 1 1)
        ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p))
          ((contCoindSES (F := F) p).explicitDelta0 z₀))
        ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y)
      = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          (explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p) (mulPairing (p := p))
            continuous_of_discreteTopology (mulPairing_equivariant (F := F) p)
            ((contCoindSES (F := F) p).explicitDelta0 z₀) y) :=
    explicitAddEquiv_cup11 (G := AbsoluteGaloisGroup F) (M := ZMod p) (N := ZMod p) (P := ZMod p)
      (μ := mulPairing (p := p)) (hequiv := mulPairing_equivariant (F := F) p)
      ((contCoindSES (F := F) p).explicitDelta0 z₀) y
  calc ((contCoindSES (F := F) p).delta 1).hom
        (((ofDiscreteModulePairing (smulPairingC (F := F) p)
            (smulPairingC_equivariant (F := F) p)).cup 0 1)
          ((CategoryTheory.ConcreteCategory.hom
            (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀)
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y))
      = ((contCoindSES (F := F) p).delta 1).hom
          (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)
            (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p) (contC (F := F) p)
              (smulPairingC (F := F) p) continuous_of_discreteTopology
              (smulPairingC_equivariant (F := F) p) z₀ y)) := by rw [hcup01]
    _ = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          ((contCoindSES (F := F) p).explicitDelta1
            (explicitCup01 (AbsoluteGaloisGroup F) (contC (F := F) p) (ZMod p) (contC (F := F) p)
              (smulPairingC (F := F) p) continuous_of_discreteTopology
              (smulPairingC_equivariant (F := F) p) z₀ y)) :=
        coindSES_delta_one_eq_explicit (F := F) p _
    _ = explicitH2AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)
          (explicitCup11 (AbsoluteGaloisGroup F) (ZMod p) (ZMod p) (ZMod p) (mulPairing (p := p))
            continuous_of_discreteTopology (mulPairing_equivariant (F := F) p)
            ((contCoindSES (F := F) p).explicitDelta0 z₀) y) := by
        rw [explicitLeibniz_cup01 (F := F) p z₀ y]
    _ = ((ofDiscreteModulePairing (mulPairing (p := p))
            (mulPairing_equivariant (F := F) p)).cup 1 1)
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p))
            ((contCoindSES (F := F) p).explicitDelta0 z₀))
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y) := by
        rw [hcup11]
    _ = ((ofDiscreteModulePairing (mulPairing (p := p))
            (mulPairing_equivariant (F := F) p)).cup 1 1)
          (((contCoindSES (F := F) p).delta 0).hom
            ((CategoryTheory.ConcreteCategory.hom
              (explicitH0IsoContinuousCohomology (AbsoluteGaloisGroup F) (contC (F := F) p)).hom) z₀))
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y) := by
        rw [coindSES_delta_zero_eq_explicit (F := F) p z₀]

end L20261018

#print axioms L20261018.coindSES_delta_one_eq_explicit
#print axioms L20261018.coindSES_delta_zero_eq_explicit
#print axioms L20261018.contLeibniz_cup01
