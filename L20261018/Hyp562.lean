import Hyp561

/-!
# S46 R10：★★★★ **同构的装配（条件于一句 `IsLocallyConstant`）**

`Hyp559`–`Hyp561` 已备：正向 `contInvBDescend`（含 `∘ mk = id`、单射）、反向 `coindBotToContInvB`、
以及互逆律 `descend ∘ pull = id`（⟹ `pull` 单射）。**唯一还缺**的是

```
IsLocallyConstant (contInvBDescend g)            -- 使 `descend g` 落进 `DiscreteCoind`
```

本件把它作为**具名假设**（`hlc`），断言：

```
hlc  ⟹  contInvB ≃+ DiscreteCoind (Γ⧸I) ⊥ μ_p
```

于是剩余义务从「一段散文」压成**一句带类型的 `Prop`**，且下游（`δ_T` iso）可立即消费。

## 为什么绕不过这句（已试过）

`pull` 的**满射性**唯一来源是 `pull (descend g) = g`，它要求 `descend g` 已是 `DiscreteCoind` 的元素
——正是 `IsLocallyConstant`。故不能用「单射 ＋ 另一条逆」代替。

## 证法与依据

`hlc` ＋ `descend ∘ pull = id` ⟹ `pull` 与 `descendD` 互为逆 ⟹ `AddEquiv`。
`IsLocallyConstant` 本身的证法（下一件）：`descend g ∘ mk = g` ＋ 商拓扑 `isOpen_coinduced`
（`s` 在 `Γ⧸I` 中开 ⟺ `mk ⁻¹' s` 在 `Γ` 中开）⟹ `descend g` 连续 ⟹ 局部常值
（`IsLocallyConstant.iff_continuous`）。
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

/-- `↥(⊥ : Subgroup (Γ⧸I))` 的平凡作用（每件须用新鲜名字，见 digest §4c-i）。 -/
local instance trivialActionBotQuotR10 :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotQuotR10 :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **`descend` 的结构版**（条件于 `IsLocallyConstant`）：`Bᴵ →+ DiscreteCoind (Γ⧸I) ⊥ μ_p`。 -/
noncomputable def contInvBDescendCoind
    (hlc : ∀ g : contInvB (F := F) p I,
      IsLocallyConstant (contInvBDescendFun (F := F) p I g)) :
    contInvB (F := F) p I →+ DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) where
  toFun g :=
    ⟨contInvBDescendFun (F := F) p I g, ⟨hlc g, by
      intro u g'
      rw [show u = 1 from Subsingleton.elim u 1]
      simp⟩⟩
  map_zero' := by
    apply DiscreteCoind.ext
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    show contInvBDescendFun (F := F) p I 0 (x : (AbsoluteGaloisGroup F) ⧸ I) = 0
    rw [contInvBDescendFun_comp_mk]
    simp
  map_add' g₁ g₂ := by
    apply DiscreteCoind.ext
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    show contInvBDescendFun (F := F) p I (g₁ + g₂) (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (contInvBDescendFun (F := F) p I g₁ + contInvBDescendFun (F := F) p I g₂)
          (x : (AbsoluteGaloisGroup F) ⧸ I)
    rw [contInvBDescendFun_comp_mk]
    simp

/-- ★★★★★ **同构装配**：`hlc ⟹ contInvB ≃+ DiscreteCoind (Γ⧸I) ⊥ μ_p`。 -/
noncomputable def contInvBEquivCoind
    (hlc : ∀ g : contInvB (F := F) p I,
      IsLocallyConstant (contInvBDescendFun (F := F) p I g)) :
    contInvB (F := F) p I ≃+ DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) where
  toFun := contInvBDescendCoind (F := F) p I hlc
  invFun := coindBotToContInvB (F := F) p I
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show (coindBotPull (F := F) p I
        ((contInvBDescendCoind (F := F) p I hlc) g)) x = (g : contB (F := F) p) x
    rw [coindBotPull_apply]
    show contInvBDescendFun (F := F) p I g (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (g : contB (F := F) p) x
    rw [contInvBDescendFun_comp_mk]
  right_inv h := by
    apply DiscreteCoind.ext
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    show contInvBDescendFun (F := F) p I ((coindBotToContInvB (F := F) p I) h)
        (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (h : ((AbsoluteGaloisGroup F) ⧸ I) → ZMod p) (x : (AbsoluteGaloisGroup F) ⧸ I)
    rw [contInvBDescendFun_comp_mk]
    rfl
  map_add' g₁ g₂ := map_add (contInvBDescendCoind (F := F) p I hlc) g₁ g₂

end L20261018

#print axioms L20261018.contInvBDescendCoind
#print axioms L20261018.contInvBEquivCoind
