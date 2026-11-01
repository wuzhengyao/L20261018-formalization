import L20261018.Infra.Cohomology.ResidueLES.Step023_is_locally_constant_descend

/-!
# S46 R12：★★★★★ **`TopRep` 同构** —— `Bᴵ ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p`（作为 `Γ⧸I`-模）

`Hyp563` 给了加法同构 `contInvBEquivCoindBot`。本件补上**等变性**（`map_smul'`），
并据此造出库内可直接消费的 `TopRep` 同构：

```
ofDiscreteModule ℤ (Γ⧸I) (Bᴵ)  ≅  ofDiscreteModule ℤ (Γ⧸I) (DiscreteCoind (Γ⧸I) ⊥ μ_p)
```

等变性的实质：`(mk h • g) : contB` 在 `x` 处取 `g (x * h)`（`fixedPoints_subtype_quotientMk_smul`
＋ `DiscreteCoind.coe_smul`），而右边 `mk h • e g` 在 `mk x` 处取 `(e g) ((mk x) * (mk h))`，
`(mk x)*(mk h) = mk (x*h)`，两处同值。
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
  (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal] [IsClosed (I : Set (AbsoluteGaloisGroup F))]

/-- `↥(⊥ : Subgroup (Γ⧸I))` 的平凡作用（每件须换新名字）。 -/
local instance trivialActionBotQuotR12 :
    DistribMulAction (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulBotQuotR12 :
    ContinuousSMul (↥(⊥ : Subgroup ((AbsoluteGaloisGroup F) ⧸ I))) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **等变性**：`e` 是 `Γ⧸I`-线性的。 -/
theorem contInvBEquivCoindBot_smul (q : (AbsoluteGaloisGroup F) ⧸ I)
    (g : contInvB (F := F) p I) :
    contInvBEquivCoindBot (F := F) p I (q • g)
      = q • contInvBEquivCoindBot (F := F) p I g := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I q
  apply DiscreteCoind.ext
  intro y
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  have hL : (contInvBEquivCoindBot (F := F) p I
        ((I.quotientMkContinuousMonoidHom h) • g)) (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (g : contB (F := F) p) (x * (h : AbsoluteGaloisGroup F)) := by
    show contInvBDescendFun (F := F) p I ((I.quotientMkContinuousMonoidHom h) • g)
      (x : (AbsoluteGaloisGroup F) ⧸ I) = _
    rw [contInvBDescendFun_comp_mk]
    show ((FixedPoints.addSubgroup (↥I) (contB (F := F) p)).subtype
      ((I.quotientMkContinuousMonoidHom h) • g)) x = _
    rw [I.fixedPoints_subtype_quotientMk_smul (M := contB (F := F) p),
      DiscreteCoind.coe_smul]
    rfl
  have hR : ((I.quotientMkContinuousMonoidHom h) •
        contInvBEquivCoindBot (F := F) p I g) (x : (AbsoluteGaloisGroup F) ⧸ I)
      = (g : contB (F := F) p) (x * (h : AbsoluteGaloisGroup F)) := by
    rw [DiscreteCoind.coe_smul]
    show contInvBDescendFun (F := F) p I g
      (((x : (AbsoluteGaloisGroup F) ⧸ I)) *
        ((I.quotientMkContinuousMonoidHom h) : (AbsoluteGaloisGroup F) ⧸ I)) = _
    show contInvBDescendFun (F := F) p I g
      ((x * (h : AbsoluteGaloisGroup F) : AbsoluteGaloisGroup F) :
        (AbsoluteGaloisGroup F) ⧸ I) = _
    rw [contInvBDescendFun_comp_mk]
  exact hL.trans hR.symm


/-- `e.symm` 的等变性（由 `e` 的等变性 ＋ 单射性）。 -/
theorem contInvBEquivCoindBot_symm_smul (q : (AbsoluteGaloisGroup F) ⧸ I)
    (h : DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :
    (contInvBEquivCoindBot (F := F) p I).symm (q • h)
      = q • (contInvBEquivCoindBot (F := F) p I).symm h := by
  apply (contInvBEquivCoindBot (F := F) p I).injective
  rw [AddEquiv.apply_symm_apply, contInvBEquivCoindBot_smul, AddEquiv.apply_symm_apply]

/-- ★★★★★ **`TopRep` 同构**：`Bᴵ ≅ DiscreteCoind (Γ⧸I) ⊥ μ_p` 作为 `Γ⧸I`-模。 -/
noncomputable def contInvBTopRepIso :
    ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I) ≅
      ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I)
        (DiscreteCoind ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) where
  hom := ofDiscreteModuleMap
    (contInvBEquivCoindBot (F := F) p I).toAddMonoidHom.toIntLinearMap
    (fun q x => contInvBEquivCoindBot_smul (F := F) p I q x)
  inv := ofDiscreteModuleMap
    (contInvBEquivCoindBot (F := F) p I).symm.toAddMonoidHom.toIntLinearMap
    (fun q x => contInvBEquivCoindBot_symm_smul (F := F) p I q x)
  hom_inv_id := by
    ext x
    exact (contInvBEquivCoindBot (F := F) p I).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (contInvBEquivCoindBot (F := F) p I).apply_symm_apply x

/-- ★★★★★ **`Bᴵ` 在 `Γ⧸I` 上零调**（`n ≥ 1`）。 -/
theorem subsingleton_contInvB (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (continuousCohomology n
      (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvB (F := F) p I))) := by
  haveI := subsingleton_continuousCoindBot (F := F) p I n hn
  exact subsingleton_of_topRep_iso (contInvBTopRepIso (F := F) p I) n

/-- ★★★★★ **`δ_T` 是同构**（无条件！）。 -/
theorem isIso_contInvSES_delta_uncond (n : ℕ) (hn : 1 ≤ n) :
    IsIso ((contInvSES (F := F) p I).delta n) := by
  haveI := subsingleton_contInvB (F := F) p I n hn
  haveI := subsingleton_contInvB (F := F) p I (n + 1) (by omega)
  exact isIso_contInvSES_delta (F := F) p I n

end L20261018

#print axioms L20261018.contInvBEquivCoindBot_smul
#print axioms L20261018.contInvBEquivCoindBot_symm_smul
#print axioms L20261018.contInvBTopRepIso
#print axioms L20261018.subsingleton_contInvB
#print axioms L20261018.isIso_contInvSES_delta_uncond
