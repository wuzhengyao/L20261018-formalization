import Hyp785

/-!
# S75 R3：**`(6.15)⁻¹` 的存在性** —— `δ⁰ : H⁰(Γ, C) ↠ H¹(Γ, μ_p)`

## 本件在五步打法的哪一步

`PROMPT-S75` §1.1／`GAP3-PLAN` §11.3 第 1 步：**取 `z₀` 使 `δ₀(Inf z₀) = π`**（即 GS 的
`(6.15^{(1)})⁻¹`）。本件给出它的**存在性半**：

```
longExact_exact₁ 0 : range (S.delta 0) = ker (coeffMap (incl) 1)
H¹(Γ, B) = 0        （B = Coind Γ ⊥ μ_p 余诱导零调）
⟹ range (S.delta 0) = ⊤  ⟹  ∀ π, ∃ z₀, (S.delta 0).hom z₀ = π
```

## 交付

| 声明 | 内容 |
|---|---|
| **`contC_exists_delta_zero_eq`** | ★★★★ `δ⁰` **满射**（`(6.15)⁻¹` 的存在性） |

## 诚实边界（下一件的三件事，已定路线）

1. **`e₀` 的满射性**（`↥(H0 G C) → continuousCohomology 0 (…)`）：路线 = `zeroIso`
   （`ContinuousCohomology.zeroIso : H⁰_cont ≅ invariants`）＋
   `explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass`；
   有了它，`contLeibniz_cup01`（`Hyp785`，**显式** `H⁰` 槽）才能用在**连续** `H⁰` 类上。
2. 特化到 `π = kummerClass π` 与 `y = Inf a`。
3. 第 3 步 `Infl⁻¹(Inf z₀ ⌣ Inf a) = z₀ ⌣ a`：需 `Cᴵ` 上的 `ZMod p`-模结构（同 `contCModule`
   的三段式）＋ 库内 `explicitInfl1_explicitCup01`（`Cup/Inflation.lean:96`）。
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

/-- ★★★★ **`(6.15)⁻¹` 的存在性**：`δ⁰ : H⁰(Γ, C) ↠ H¹(Γ, μ_p)` 满射。

`S = 0 → μ_p → Coind Γ ⊥ μ_p → C → 0`；`H¹(Γ, Coind) = 0`（余诱导零调，作为假设给出），
故 `coeffMap incl 1 = 0`，由 `longExact_exact₁ 0`（`range (S.delta 0) = ker (coeffMap incl 1)`）
得 `range (S.delta 0) = ⊤`。 -/
theorem contC_exists_delta_zero_eq
    [Subsingleton
      ↑(continuousCohomology 1
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contB (F := F) p))).toModuleCat]
    (π : continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p))) :
    ∃ z₀ : continuousCohomology 0
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)),
      ((contCoindSES (F := F) p).delta 0).hom z₀ = π := by
  have hex := DiscreteShortExact.longExact_exact₁ (S := contCoindSES (F := F) p) 0
  exact (hex π).mp (Subsingleton.elim _ 0)

/-- ★★★ **同一件事的 `H¹` 形态**：把 `π` 取成 `e₁ π'`（`π' ∈ H¹(Γ, μ_p)` 显式模型），
方便下游直接喂 `KummerBridge.kummerClass`。 -/
theorem contC_exists_delta_zero_eq_of_H1
    [Subsingleton
      ↑(continuousCohomology 1
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contB (F := F) p))).toModuleCat]
    (π' : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    ∃ z₀ : continuousCohomology 0
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)),
      ((contCoindSES (F := F) p).delta 0).hom z₀
        = (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) π' :=
  contC_exists_delta_zero_eq (F := F) p _

end L20261018

#print axioms L20261018.contC_exists_delta_zero_eq
#print axioms L20261018.contC_exists_delta_zero_eq_of_H1
