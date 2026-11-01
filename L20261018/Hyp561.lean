import Hyp560

/-!
# S46 R9：★★★ **同构的两条互逆律之一**：`descend ∘ pull = id` ⟹ `pull` 单射

`Hyp559` 给正向（`contInvBDescend : Bᴵ →+ (Γ⧸I → μ_p)`），`Hyp560` 给反向
（`coindBotToContInvB : DiscreteCoind (Γ⧸I) ⊥ μ_p →+ Bᴵ`）。本件把它们对起来一条：

```
contInvBDescend (coindBotToContInvB h) = h        -- 函数层
```

由此 `coindBotToContInvB` **单射**（有左逆）。

## 诚实边界

* 反向的那条 `coindBotToContInvB (descend g) = g` 需要 `descend g` **落进** `DiscreteCoind`
  （即 `IsLocallyConstant (contInvBDescend g)`），**未做**。它同时是 `pull` 满射性的唯一来源。
* `≃+`／`TopRep` 同构因而仍未装配。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- `↥(⊥ : Subgroup (Γ⧸I))` 的平凡作用（每个新文件都要重声明，见 digest §4c-i）。 -/
local instance trivialActionBotQuotR9 :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotQuotR9 :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **`descend ∘ pull = id`**（函数层）：拉回后下降回到原函数。 -/
theorem contInvBDescend_comp_coindBotToContInvB
    (h : DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :
    contInvBDescendFun (F := F) p I (coindBotToContInvB (F := F) p I h)
      = (h : ((AbsoluteGaloisGroup F) ⧸ I) → ZMod p) := by
  funext q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [contInvBDescendFun_comp_mk]
  rfl

/-- ★★★★ **反向映射单射**（`descend` 是它的左逆）。 -/
theorem coindBotToContInvB_injective :
    Function.Injective (coindBotToContInvB (F := F) p I) := by
  intro h₁ h₂ heq
  have h := congrArg (contInvBDescendFun (F := F) p I) heq
  rw [contInvBDescend_comp_coindBotToContInvB (F := F) p I h₁,
    contInvBDescend_comp_coindBotToContInvB (F := F) p I h₂] at h
  exact DiscreteCoind.ext (fun x => congrArg (fun f => f x) h)

end L20261018

#print axioms L20261018.contInvBDescend_comp_coindBotToContInvB
#print axioms L20261018.coindBotToContInvB_injective
