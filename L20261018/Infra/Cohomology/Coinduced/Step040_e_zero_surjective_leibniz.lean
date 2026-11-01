import L20261018.Infra.Cohomology.Coinduced.Step039_delta_zero_surjective

/-!
# S75 R4：`e₀` 满射性 ＋ **连续 `H⁰` 类上的 Leibniz** ＋ **`cup11 π y` 的 `δ¹` 原像存在**

## 为什么需要这三件

`Hyp785.contLeibniz_cup01` 的 `H⁰` 槽是**显式模型**（`↥(H0 G C)`），而下游拿到的 `z₀`
（`Hyp786.contC_exists_delta_zero_eq` 的产出）住在**连续模型**
（`continuousCohomology 0 (…)`）。本件把这两头接上：

| 声明 | 内容 |
|---|---|
| **`h0Iso_surjective`** | ★★★ `explicitH0IsoContinuousCohomology` 在底层类型上**满射** |
| **`contLeibniz_cup01_cont`** | ★★★★★ **连续 `H⁰` 类上的 Leibniz**：`δ¹(z₀ ⌣ y) = δ⁰ z₀ ⌣ y`，`z₀ : H⁰_cont` |
| **`contC_exists_cup_preimage`** | ★★★★★ `∀ π, ∀ y, ∃ z, δ¹ z = cup11 π y`（**`Hyp781` 准入件的 `z`**） |

第三件正是 GS 6.8.4 证明里 "`x := π ⌣ Inf a`，取 `z₃` 使 `δ₁ z₃ = x`" 的机检形态：
`z := cup01 z₀ (e₁ y)`，其中 `z₀` 是 `δ⁰` 的任一原像（`Hyp786`）。

## 证明结构

```
h0Iso_surjective          z ↦ e₀.inv z，配 Iso.hom_inv_id_apply
contLeibniz_cup01_cont    把 z₀ 写成 e₀ m（满射），一步 rw 后喂 Hyp785.contLeibniz_cup01
contC_exists_cup_preimage 取 z₀ := Hyp786 的原像，z := cup01 z₀ (e₁ y)，再 rw [δ⁰ z₀ = π]
```
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

/-- ★★★ **`explicitH0IsoContinuousCohomology` 满射**（底层类型上）：连续 `H⁰` 类都来自显式
`H⁰`（即 `G`-不变元素）。这是把显式模型的引理用在连续 `H⁰` 类上的桥。 -/
theorem h0Iso_surjective {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] [DistribMulAction G M]
    (z : continuousCohomology 0 (ofDiscreteModule ℤ G M)) :
    ∃ m : ↥(H0 G M),
      (CategoryTheory.ConcreteCategory.hom (explicitH0IsoContinuousCohomology G M).hom) m = z := by
  obtain ⟨m, hm⟩ := (explicitH0IsoContinuousCohomology G M).toContinuousLinearEquiv.toEquiv.surjective z
  exact ⟨m, hm⟩

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- ★★★★★ **连续模型上的 `H⁰`-Leibniz**（`H⁰` 槽取**连续**类）：
`δ¹ (z₀ ⌣ y) = δ⁰ z₀ ⌣ y`，`z₀ ∈ H⁰_cont(Γ, C)`、`y ∈ H¹(Γ, μ_p)`。

由 `Hyp785.contLeibniz_cup01`（显式槽）＋ `h0Iso_surjective` 得。 -/
theorem contLeibniz_cup01_cont
    (z₀ : continuousCohomology 0
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    ((contCoindSES (F := F) p).delta 1).hom
        (((ofDiscreteModulePairing (smulPairingC (F := F) p)
            (smulPairingC_equivariant (F := F) p)).cup 0 1) z₀
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y))
      = ((ofDiscreteModulePairing (mulPairing (p := p))
            (mulPairing_equivariant (F := F) p)).cup 1 1)
          (((contCoindSES (F := F) p).delta 0).hom z₀)
          ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y) := by
  obtain ⟨m, hm⟩ := h0Iso_surjective (G := AbsoluteGaloisGroup F)
    (M := contC (F := F) p) z₀
  rw [← hm]
  exact contLeibniz_cup01 (F := F) p m y

/-- ★★★★★ **`cup11 π y` 的 `δ¹`-原像存在**：`∀ π y, ∃ z, δ¹ z = cup11 π y`。

`z := cup01 z₀ (e₁ y)`，`z₀` 取 `δ⁰` 的任一原像（**`Hyp786`**）；`δ¹ z = δ⁰ z₀ ⌣ y = π ⌣ y`
用 `contLeibniz_cup01_cont`。**这是 `Hyp781.deltaTwoShift_eq_of_delta_eq` 的准入件**：
`∂²(π ⌣ y)` 由此可以按 `z` 显式展开。 -/
theorem contC_exists_cup_preimage
    [Subsingleton
      ↑(continuousCohomology 1
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contB (F := F) p))).toModuleCat]
    (π : continuousCohomology 1 (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)))
    (y : H1 (AbsoluteGaloisGroup F) (ZMod p)) :
    ∃ z : continuousCohomology 1
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)),
      ((contCoindSES (F := F) p).delta 1).hom z
        = ((ofDiscreteModulePairing (mulPairing (p := p))
            (mulPairing_equivariant (F := F) p)).cup 1 1) π
            ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y) := by
  obtain ⟨z₀, hz₀⟩ := contC_exists_delta_zero_eq (F := F) p π
  refine ⟨((ofDiscreteModulePairing (smulPairingC (F := F) p)
      (smulPairingC_equivariant (F := F) p)).cup 0 1) z₀
      ((explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p)) y), ?_⟩
  rw [contLeibniz_cup01_cont (F := F) p z₀ y, hz₀]

end L20261018

#print axioms L20261018.h0Iso_surjective
#print axioms L20261018.contLeibniz_cup01_cont
#print axioms L20261018.contC_exists_cup_preimage
