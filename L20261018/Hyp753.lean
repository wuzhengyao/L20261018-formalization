import L20261018.Hyp752
import L20261018.Hyp743

/-!
# S68 R11：A-1 最后一步（`S68-HYP744-PLAN.md` §9quater）

## 恒等式 ②

`em_{Γ,φ,subtype} = em_{Γ,φ,id} ∘ em_{Γ⧸I,id,subtype}`（一次 `explicitMap2_comp` ＋ `explicitMap2_congr_of_eq`）。

⚠ `ContinuousMonoidHom.comp` **反序**：`φ.comp ψ` 意为「先 `ψ` 后 `φ`」，故
`id_{Γ⧸I}.comp φ = φ`（**不是** `φ.comp id`）。见 `LESSONS.md` **D71**。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology
attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- 恒等式 ②：`em_{Γ,φ,subtype} = em_{Γ,φ,id} ∘ em_{Γ⧸I,id,subtype}`。 -/
theorem explicitMap2_quot_subtype_eq_comp
    (y : H2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))) :
    explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (AbsoluteGaloisGroup F) (ZMod p)
        (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
        (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n) y
      = explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
          (AbsoluteGaloisGroup F) (ZMod p)
          (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
          (AddMonoidHom.id (ZMod p)) continuous_of_discreteTopology (fun _ _ => rfl)
          (explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
            (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
            (ContinuousMonoidHom.id _)
            (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
            continuous_of_discreteTopology
            (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
            y) := by
  have h := explicitMap2_comp (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (M := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (H := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (N := ZMod p)
    (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F))
    (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
    continuous_of_discreteTopology
    (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
    (AbsoluteGaloisGroup F) (ZMod p)
    (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
    (AddMonoidHom.id (ZMod p)) continuous_of_discreteTopology (fun _ _ => rfl)
  have h' : explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (AbsoluteGaloisGroup F) (ZMod p)
        (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
        (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
      = explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (AbsoluteGaloisGroup F) (ZMod p)
          ((ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F)).comp
            (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F)))
          ((AddMonoidHom.id (ZMod p)).comp
            (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype)
          continuous_of_discreteTopology
          (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n) :=
    explicitMap2_congr_of_eq _ _ _ _ _ _ _ _
      (ContinuousMonoidHom.ext fun _ => rfl) (AddMonoidHom.ext fun _ => rfl)
  rw [h', h]
  rfl

end L20261018

#print axioms L20261018.explicitMap2_quot_subtype_eq_comp
