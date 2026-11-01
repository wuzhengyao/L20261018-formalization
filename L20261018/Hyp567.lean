import L20261018.Hyp566

/-!
# S46 R15：★★★ **`Aᴵ ≅ A` 的 `TopRep` 层完成**

`Hyp566` 给了 `contInvAEquiv : Aᴵ ≃+ A` 与其等变性，但 `TopRep` 同构的 `inv` 一侧当时没证完
（`toAddMonoidHom.toIntLinearMap` 包装挡住 `AddEquiv.apply_symm_apply` 的重写）。
本件先证**作用在 `Aᴵ` 上是平凡的**（`contInvA_smul_eq_self`），再据此把 `TopRep` 同构补完。

用途：把 `contInvSES : 0 → Aᴵ → Bᴵ → T → 0` 与库内 `coindShortExact (Γ⧸I) ⊥ μ_p` 对齐。
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

/-- `Γ⧸I` 在 `ZMod p` 上的平凡作用。 -/
local instance trivialActionZModQuotR15 :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModQuotR15 :
    ContinuousSMul ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★ **`Γ⧸I` 在 `Aᴵ` 上的作用是平凡的**（`Aᴵ` 的成员都是 `I`-不动点，且 `μ_p` 上作用平凡）。 -/
theorem contInvA_smul_eq_self (q : (AbsoluteGaloisGroup F) ⧸ I) (x : contInvA (F := F) p I) :
    q • x = x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective I q
  apply Subtype.ext
  show ((I.quotientMkContinuousMonoidHom h) • x : ZMod p) = (x : ZMod p)
  rfl

/-- ★★★★ **`Aᴵ ≅ A` 作为 `Γ⧸I`-模**（`TopRep` 层）。 -/
noncomputable def contInvATopRepIso :
    ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvA (F := F) p I) ≅
      ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  hom := ofDiscreteModuleMap (contInvAEquiv (F := F) p I).toAddMonoidHom.toIntLinearMap
    (fun q x => contInvAEquiv_smul (F := F) p I q x)
  inv := ofDiscreteModuleMap (contInvAEquiv (F := F) p I).symm.toAddMonoidHom.toIntLinearMap
    (fun q x => by
      show (contInvAEquiv (F := F) p I).symm (q • x)
        = q • (contInvAEquiv (F := F) p I).symm x
      rw [contInvA_smul_eq_self (F := F) p I q ((contInvAEquiv (F := F) p I).symm x)]
      rfl)
  hom_inv_id := by
    ext x
    exact (contInvAEquiv (F := F) p I).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (contInvAEquiv (F := F) p I).apply_symm_apply x

end L20261018

#print axioms L20261018.contInvA_smul_eq_self
#print axioms L20261018.contInvATopRepIso
