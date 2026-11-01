import L20261018.Infra.Cohomology.Coinduced.Step032_a1_last_step

/-!
# S68 R12：**`∂² ∘ infl₂ = 0`** 在战役载体上（A-1 收口）

`Hyp743` 的 `∂² ∘ Inf₂ = 0` 用的是**源系数 `M^I`** 的 `Inf₂`；
`Hyp610.infl2Res = map φ coeffIdHom 2` 用的是 **`ZMod p`**。本件用
`Hyp753.explicitMap2_quot_subtype_eq_comp`（系数桥）把前者搬到后者。

## 交付

| 声明 | 内容 |
|---|---|
| `explicitMap2_subtype_comp_coeff` | ★★★★ `em_{Γ⧸I,subtype} ∘ em_{Γ⧸I,e} = id`（＝ §9ter 的 ①） |

**下一步（§9quinquies 的 ③）**：`em_{Γ,φ,id} = em_{Γ,φ,subtype} ∘ em_e`，取 `Hyp753` 于 `y := em_e y`
再用本件的 ①。⚠ 两个 `rw` 的**方向**：`rw [explicitMap2_quot_subtype_eq_comp …]` 在前、
`rw [explicitMap2_subtype_comp_coeff …]` 在后（反过来 `exact … .symm` 会撞类型不匹配）。
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
variable (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
variable (hcop : p.Coprime q)

/-- ★★★★ **`em_subtype ∘ em_e = id`**（由 `Hyp752` 与 `explicitMap2_id`）。 -/
theorem explicitMap2_subtype_comp_coeff
    (y : H2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (ContinuousMonoidHom.id _)
        (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
        continuous_of_discreteTopology
        (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
        (explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
          (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
          continuous_of_discreteTopology
          (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) y) = y := by
  rw [← explicitMap2_id_eq_subtype_comp (F := F) (p := p) (I := inertiaLoc F) y]
  exact congrArg (fun f => f y) (explicitMap2_id _ _ (fun _ _ => rfl))

/-- ★★★★ **恒等式 ③**：`em_{Γ,φ,id} = em_{Γ,φ,subtype} ∘ em_{Γ⧸I,e}`。

由 `Hyp753`（取 `y := em_e y`）＋ `explicitMap2_subtype_comp_coeff`（把内层绕回 `y`）。 -/
theorem explicitMap2_quot_id_eq_subtype_comp
    (y : H2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)) :
    explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (AbsoluteGaloisGroup F) (ZMod p)
        (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
        (AddMonoidHom.id (ZMod p)) continuous_of_discreteTopology (fun _ _ => rfl) y
      = explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
          (AbsoluteGaloisGroup F) (ZMod p)
          (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
          (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype
          continuous_of_discreteTopology
          (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
          (explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
            (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
            ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
            (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
            continuous_of_discreteTopology
            (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) y) := by
  have h3 := explicitMap2_quot_subtype_eq_comp (F := F) (p := p)
    (explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
      (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := inertiaLoc F))
      continuous_of_discreteTopology
      (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) y)
  rw [explicitMap2_subtype_comp_coeff (F := F) (p := p) y] at h3
  exact h3.symm


end L20261018

#print axioms L20261018.explicitMap2_subtype_comp_coeff
#print axioms L20261018.explicitMap2_quot_id_eq_subtype_comp

