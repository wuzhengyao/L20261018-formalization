import Hyp569

/-!
# S46 R18：★★★★ **右格收口** —— `hK` 已证 ⟹ `T ≅ CoindQuotient (Γ⧸I) ⊥ μ_p` 无条件

`Hyp569` 证了主等式 `e ∘ contInvIncl = unit ∘ subtype`；本件补三行 `range` 搬运：

```
contKI.map e = (contInvIncl.range).map e
             = (e ∘ contInvIncl).range          -- range_comp
             = (unit ∘ subtype).range            -- Hyp569
             = subtype.range.map unit = ⊤.map unit = unit.range   -- subtype 满射
```
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

/-- `Γ⧸I` 在 `ZMod p` 上的平凡作用（每件换新名字）。 -/
local instance trivialActionZModQuotR18 :
    DistribMulAction ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的连续性。 -/
local instance trivialContinuousSMulZModQuotR18 :
    ContinuousSMul ((AbsoluteGaloisGroup F) ⧸ I) (ZMod p) where
  continuous_smul := continuous_snd

/-- ★★★★ **`hK` 已证**：`contKI` 在 `e` 下的像就是常值子群。 -/
theorem contKI_map_eq :
    (contKI (F := F) p I).map (contInvBEquivCoindBot (F := F) p I).toAddMonoidHom
      = (DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)).toAddMonoidHom.range := by
  have hcomp : (contInvBEquivCoindBot (F := F) p I).toAddMonoidHom.comp
        (contInvIncl (F := F) p I)
      = (DiscreteCoind.unit ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)).toAddMonoidHom.comp
          (contInvAEquiv (F := F) p I).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro a
    exact contInvIncl_equiv_unit (F := F) p I a
  show (contInvIncl (F := F) p I).range.map
      (contInvBEquivCoindBot (F := F) p I).toAddMonoidHom = _
  rw [← AddMonoidHom.range_comp, hcomp, AddMonoidHom.range_comp]
  have hsurj : (contInvAEquiv (F := F) p I).toAddMonoidHom.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (contInvAEquiv (F := F) p I).surjective
  rw [hsurj, AddSubgroup.map_top]

/-- ★★★★★ **右格无条件**：`T ≅ CoindQuotient (Γ⧸I) ⊥ μ_p`。 -/
theorem contT_equiv_coindQuotient' :
    Nonempty (contT (F := F) p I
      ≃+ CoindQuotient ((AbsoluteGaloisGroup F) ⧸ I) ⊥ (ZMod p)) :=
  contT_equiv_coindQuotient (F := F) p I (contKI_map_eq (F := F) p I)

end L20261018

#print axioms L20261018.contKI_map_eq
#print axioms L20261018.contT_equiv_coindQuotient'
