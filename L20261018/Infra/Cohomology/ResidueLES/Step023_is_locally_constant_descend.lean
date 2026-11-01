import L20261018.Infra.Cohomology.ResidueLES.Step022_bi_iso_assembly

/-!
# S46 R11：★★★★★ **`hlc` 已证** —— `IsLocallyConstant (contInvBDescend g)`

`Hyp562` 把同构 `contInvB ≃+ DiscreteCoind (Γ⧸I) ⊥ μ_p` 装到了条件 `hlc` 上。本件**证 `hlc`**：

```
descend g ∘ mk = g   (Hyp559)  ＋  g 局部常值  ＋  Γ⧸I 是商拓扑
⟹ descend g 的每个纤维前像在 Γ 中开  ⟺  （商拓扑）在 Γ⧸I 中开
⟹ descend g 连续  ⟹  局部常值      (IsLocallyConstant.iff_continuous)
```

商拓扑那一步是 mathlib 的 `isOpen_coinduced`：`Γ⧸I` 上的开集恰是使 `mk ⁻¹' s` 开者。
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

/-- ★★★★★ **`contInvBDescend g` 是局部常值的**：下降不破坏局部常值性。 -/
theorem contInvBDescendFun_locallyConstant (g : contInvB (F := F) p I) :
    IsLocallyConstant (contInvBDescendFun (F := F) p I g) := by
  rw [IsLocallyConstant.iff_continuous]
  have hgcont : Continuous (fun x : AbsoluteGaloisGroup F => (g : contB (F := F) p) x) := by
    rw [← IsLocallyConstant.iff_continuous]
    exact (g : contB (F := F) p).2.1
  rw [continuous_def]
  intro s hs
  rw [isOpen_coinduced]
  convert hgcont.isOpen_preimage s hs using 1
  ext x
  show contInvBDescendFun (F := F) p I g (x : (AbsoluteGaloisGroup F) ⧸ I) ∈ s
    ↔ (g : contB (F := F) p) x ∈ s
  rw [contInvBDescendFun_comp_mk]

/-- `↥(⊥ : Subgroup (Γ⧸I))` 的平凡作用（每件须换新名字）。 -/
local instance trivialActionBotQuotR11 :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotQuotR11 :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★★ **无条件同构**：`Bᴵ ≃+ DiscreteCoind (Γ⧸I) ⊥ μ_p`（`hlc` 已由上一件消去）。 -/
noncomputable def contInvBEquivCoindBot :
    contInvB (F := F) p I ≃+ DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p) :=
  contInvBEquivCoind (F := F) p I
    (fun g => contInvBDescendFun_locallyConstant (F := F) p I g)

end L20261018

#print axioms L20261018.contInvBDescendFun_locallyConstant
#print axioms L20261018.contInvBEquivCoindBot
