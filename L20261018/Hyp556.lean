import Hyp555

/-!
# S46 R5：★★★★ **`δ_T` 同构（把剩余义务压成一个 `Subsingleton`）** ＋ `T ≅ CoindQuotient` 的落点说明

## 数学内容

`(d)` 的两条路线都要 `δ_T` iso（`S46-DIGEST` §5）。库内 `isIso_delta`
（`ContCohomology/HomologySequence.lean:200`）给出的判据是：

```
Subsingleton (Hⁿ(Γ⧸I, Bᴵ))  ∧  Subsingleton (Hⁿ⁺¹(Γ⧸I, Bᴵ))   ⟹   IsIso (δ_T n)
```

本件把它**在战役短正合列 `contInvSES` 上开火**，于是「`δ_T` iso」不再是散文，而是一条
**带显式 `Subsingleton` 假设的机检定理**。

## 关键结构观察（下一轮的落点）

`Bᴵ = (DiscreteCoind Γ ⊥ μ_p)ᴵ` ＝ `I`-不变局部常值函数 on `Γ` ＝ 函数 on `Γ⧸I`（`I ◁ Γ`）
＝ `DiscreteCoind (Γ⧸I) ⊥ μ_p`；于是 `T = Bᴵ⧸Aᴵ ≅ CoindQuotient (Γ⧸I) ⊥ μ_p`，
**`contInvSES` 与库内 `coindShortExact (Γ⧸I) ⊥ μ_p` 同构**。

⟹ 若能证该同构，`δ_T` iso 由 `isIso_coindShortExact_bot_delta`
（`DimensionShifting/Basic.lean:180`，**无条件**）**免费**得到，
且 `H^{1,2}(Γ⧸I, Bᴵ) = 0` 也一并到手。这是下一轮的目标。

## 诚实边界

* 本件**不证** `Subsingleton (H^{1,2}(Γ⧸I, Bᴵ))`：它是 `Bᴵ ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p`
  的直接推论，而该同构**尚未证**（函数空间上的 `I`-不变性 × `I◁Γ` ⟹ `I∖Γ = Γ⧸I`）。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★★ **`δ_T` 是同构**（判据形态）：只需 `H^{n}` 与 `H^{n+1}` 上 `Bᴵ` 的零调性。 -/
theorem isIso_contInvSES_delta (n : ℕ)
    [Subsingleton (continuousCohomology n
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I)))]
    [Subsingleton (continuousCohomology (n + 1)
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I)))] :
    IsIso ((contInvSES (F := F) p I).delta n) :=
  DiscreteShortExact.isIso_delta (contInvSES (F := F) p I) n

/-- `δ_T` 的 `Epi` 形态（`(d)` 收口：`δ ≫ X = 0 ⟹ X = 0` 需要 `Epi`）。 -/
theorem epi_contInvSES_delta (n : ℕ)
    [Subsingleton (continuousCohomology n
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I)))]
    [Subsingleton (continuousCohomology (n + 1)
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I)))] :
    Epi ((contInvSES (F := F) p I).delta n) := by
  haveI := isIso_contInvSES_delta (F := F) p I n
  infer_instance

/-- 靶的载体锁定：`contInvSES` 的中项底层就是 `FixedPoints.addSubgroup I B`（改即编译失败）。 -/
theorem contInvSES_X₂ :
    (contInvSES (F := F) p I).incl
      = contInvIncl (F := F) p I := (rfl)

end L20261018

#print axioms L20261018.isIso_contInvSES_delta
#print axioms L20261018.epi_contInvSES_delta
#print axioms L20261018.contInvSES_X₂
