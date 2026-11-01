import L20261018.Infra.Cohomology.Coinduced.Step030_coefficient_bridge_m_inv
import L20261018.Infra.Cohomology.Coinduced.Step028_delta_two_carrier_inertia

/-!
# S68 R9：A-1 第二半 —— **显式模型里的系数桥**（绕开 `TopRep` 系数，见 `S68-HYP744-PLAN.md` §8）

`Hyp743` 的 `Inf₂` 用源系数 `M^I`，`Hyp610.infl2Res` 用 `ZMod p`。本件在**显式模型**里
（那里系数只是 `AddMonoidHom`，不需要 `LinearMap ℤ`，也没有 `ρ` 层）把两者接起来：

```
explicitMap2 (Γ⧸I) (ZMod p) Γ (ZMod p) φ id
  = explicitMap2 (Γ⧸I) (M^I)  Γ (ZMod p) φ subtype  ∘  explicitMap2 (Γ⧸I) (ZMod p) (Γ⧸I) (M^I) id e
```
（`e := coeffSubAddHom`，`subtype ∘ e = id`；`explicitMap2_comp`）

## 交付

| 声明 | 内容 |
|---|---|
| `subtype_comp_coeffSubAddHom` | `subtype ∘ e = id` |
| `coeffSubAddHom_smul` | `e (h • m) = h • e m`（`•` 层，`QuotientGroup.induction_on`） |

**下一步（`explicitMap2_comp` 的装配）**：需先用 `explicitMap2_congr_of_eq` 把
`explicitMap2 … (φ.comp ψ) (q.comp f)` 改写成 `explicitMap2 … id id`（`subtype ∘ e = id`），
再用 `← explicitMap2_comp`。`rw [← h]` 直接失败，因为两边的组合项不逐字相同。
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
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-- ★★★ **`subtype ∘ coeffSubAddHom = id`**（加性同态层）。 -/
theorem subtype_comp_coeffSubAddHom :
    (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype.comp
        (coeffSubAddHom (p := p) (I := I)) = AddMonoidHom.id (ZMod p) := by
  ext z
  exact coeffSubAddHom_apply (p := p) (I := I) z

/-- ★★★★ **`coeffSubAddHom` 与 `Γ⧸I`-作用相容**（`•` 层）。 -/
theorem coeffSubAddHom_smul (h : AbsoluteGaloisGroup F ⧸ I) (m : ZMod p) :
    coeffSubAddHom (p := p) (I := I) (h • m)
      = h • coeffSubAddHom (p := p) (I := I) m := by
  refine Subtype.ext ?_
  rw [coeffSubAddHom_apply]
  induction h using QuotientGroup.induction_on with
  | H g =>
    rw [TauCeti.coe_quotient_smul_fixedPoints_addSubgroup,
      TauCeti.coe_smul_fixedPoints_addSubgroup]
    rfl

/-! ## 主恒等式：显式模型里的系数替换（`S68-HYP744-PLAN.md` §9 的装配） -/

/-- ★★★★ **`explicitMap2` 的系数替换**：
`ZMod p` 系数上的 `id` 对 ＝ `M^I` 系数上的 `subtype` 对 复合 `coeffSubAddHom`。

装配（`rw [← explicitMap2_comp]` 不能直接用，两边组合项不逐字相同）：
先 `explicitMap2_congr_of_eq` 把 `id` 对换成 `(id.comp id) (subtype.comp e)`，再 `explicitMap2_comp`。 -/
theorem explicitMap2_id_eq_subtype_comp (y : H2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)) :
    explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (ContinuousMonoidHom.id _) (AddMonoidHom.id (ZMod p)) continuous_id
        (fun _ _ => rfl) y
      = explicitMap2 (AbsoluteGaloisGroup F ⧸ I)
          ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
          (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
          (ContinuousMonoidHom.id _) (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype
          continuous_of_discreteTopology
          (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I k n)
          (explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
            (AbsoluteGaloisGroup F ⧸ I) ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
            (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := I))
            continuous_of_discreteTopology (coeffSubAddHom_smul (F := F) (p := p) I) y) := by
  -- ① `explicitMap2_comp`
  have h := explicitMap2_comp (G := AbsoluteGaloisGroup F ⧸ I) (M := ZMod p)
    (H := AbsoluteGaloisGroup F ⧸ I) ↥(FixedPoints.addSubgroup (↥I) (ZMod p))
    (ContinuousMonoidHom.id _) (coeffSubAddHom (p := p) (I := I))
    continuous_of_discreteTopology (coeffSubAddHom_smul (F := F) (p := p) I)
    (AbsoluteGaloisGroup F ⧸ I) (ZMod p) (ContinuousMonoidHom.id _)
    (FixedPoints.addSubgroup (↥I) (ZMod p)).subtype continuous_of_discreteTopology
    (fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) I k n)
  -- ② 把 `id` 对换成 `(id.comp id) (subtype.comp e)`
  have h' : explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
        (ContinuousMonoidHom.id _) (AddMonoidHom.id (ZMod p)) continuous_id
        (fun _ _ => rfl)
      = explicitMap2 (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
          (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
          ((ContinuousMonoidHom.id _).comp (ContinuousMonoidHom.id _))
          ((FixedPoints.addSubgroup (↥I) (ZMod p)).subtype.comp
            (coeffSubAddHom (p := p) (I := I))) continuous_of_discreteTopology
          (fun _ _ => rfl) := by
    refine explicitMap2_congr_of_eq (AbsoluteGaloisGroup F ⧸ I) (ZMod p)
      (AbsoluteGaloisGroup F ⧸ I) (ZMod p) _ _ _ _ ?_ ?_
    · exact ContinuousMonoidHom.ext fun _ => rfl
    · rw [subtype_comp_coeffSubAddHom (F := F) (p := p) I]
  rw [h']
  exact DFunLike.congr_fun h y

end L20261018

#print axioms L20261018.subtype_comp_coeffSubAddHom
#print axioms L20261018.coeffSubAddHom_smul
#print axioms L20261018.explicitMap2_id_eq_subtype_comp

