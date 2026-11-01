import L20261018.Hyp750
import L20261018.Hyp743

/-!
# S68 R8：A-1 第二半 —— 系数桥 `ZMod p → M^I`

`Hyp743` 的 `Inf₂` 用源系数 `M^I = FixedPoints.addSubgroup (↥I) (ZMod p)`，
`Hyp610.infl2Res` 用 `muPQuot` 的载体 `ZMod p`。本件给出两者之间的 `TopRep` 态射。

⚠ 造法坑：`LESSONS.md` **D68**（`isIntertwining'` 在 `ρ` 层）、**D69**（`Module ℤ` 的类型注解会展开
`ZMod` 的 `match`）⟹ 走 `ofDiscreteModulePair`（`hf` 在 `•` 层）＋ `AddMonoidHom.toIntLinearMap`。
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology
open TauCeti.ContCohomology
attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- 平凡作用下 `ZMod p` 的元素都落在 `M^I` 里。 -/
theorem mem_fixedPoints_zmod (z : ZMod p) :
    z ∈ FixedPoints.addSubgroup (↥I) (ZMod p) :=
  (FixedPoints.mem_addSubgroup (↥I) (ZMod p) z).mpr (fun _ => rfl)

/-- 加性同态 `ZMod p →+ M^I`（底层 `z ↦ ⟨z, ·⟩`）。
⚠ 只证到**加性同态**层：包装成 `TopRep` 态射（`ofDiscreteModulePair` / `TopRep.ofHom`）
两条路都撞墙，见 `LESSONS.md` D68／D69 与 `S68-HYP744-PLAN.md` §7／§8。 -/
noncomputable def coeffSubAddHom :
    ZMod p →+ ↥(FixedPoints.addSubgroup (↥I) (ZMod p)) where
  toFun z := ⟨z, mem_fixedPoints_zmod (F := F) (p := p) I z⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- `coeffSubAddHom` 的底层元素。 -/
@[simp]
theorem coeffSubAddHom_apply (z : ZMod p) :
    ((coeffSubAddHom (F := F) (p := p) I z : ↥(FixedPoints.addSubgroup (↥I) (ZMod p))) : ZMod p) = z :=
  rfl

end L20261018

#print axioms L20261018.mem_fixedPoints_zmod
#print axioms L20261018.coeffSubAddHom_apply
#print axioms L20261018.coeffSubAddHom_apply
