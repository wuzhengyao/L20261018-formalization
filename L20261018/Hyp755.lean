import L20261018.Hyp754
import L20261018.Hyp743

/-!
# S69 R1：`Delta` —— **`∂² (map φ (pair φ id) 2 z) = 0`**（A-1 的最后一次装配）

五步装配（`PROMPT-S69` §①-3、`S68-HYP744-PLAN.md` §9sexies）：

```
1. y := e₂_{Γ⧸I}.symm z                      （e₂ := explicitH2AddEquivContinuousCohomology，ZMod p 系数）
2. _map（f := id）:  map φ (pair φ id) 2 (e₂ y) = e₂_Γ (em_{Γ,φ,id} y)
3. Hyp754.explicitMap2_quot_id_eq_subtype_comp: em_{Γ,φ,id} = em_{Γ,φ,sub} ∘ em_{Γ⧸I,e}
4. _map（f := sub）【反向】: e₂_Γ (em_{Γ,φ,sub} u) = map φ (pair φ sub) 2 (e₂' u)
5. Hyp743.deltaTwoCarrierInertia_comp_infl_eq_zero ⟹ 0
```

`hf` 槽的差异（自动生成项 vs 手写项）由**证明无关性**吸收（`hf` 命题值），
必要时可回退到 `map_congr_of_hom_apply`（`D64` 的绕法）。
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

/-- ★★★★★ **`Delta`**：`∂² (infl₂ z) = 0`，`z` 是 `H²(Γ⧸I, ZMod p)` 的**任意**元素
（`ZMod p` 系数的 `pair φ id` 载体）。

这才是 `hd_infl` 需要的形态：`Hyp743` 给的是源系数 `M^I` 的 `pair φ subtype`，
本件经三条系数恒等式把它搬到 `ZMod p`。 -/
theorem deltaTwoCarrierInertia_map_pair_id_eq_zero
    (q : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (hcop : p.Coprime q)
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (H1 ↥(inertiaLoc F) (ZMod p))]
    [ContinuousSMul (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (TBI (contCoindSES (F := F) p) (inertiaLoc F))]
    [DiscreteTopology (H1 ↥(inertiaLoc F) (ZMod p))]
    (z : ↥(continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)))) :
    deltaTwoCarrierInertia (F := F) p q hcop
      ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
        (TauCeti.ofDiscreteModulePair
          (Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F) :
            AbsoluteGaloisGroup F →* AbsoluteGaloisGroup F ⧸ inertiaLoc F)
          (AddMonoidHom.id (ZMod p)).toIntLinearMap
          (fun _ _ => rfl)) 2) z) = 0 := by
  haveI hcl : IsClosed (inertiaLoc F : Set (AbsoluteGaloisGroup F)) := isClosed_inertiaLoc F
  -- 1. 换到显式模型
  set y : H2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p) :=
    (explicitH2AddEquivContinuousCohomology
      (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p)).symm z with hy
  have hz : ((explicitH2AddEquivContinuousCohomology
      (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p)) y
      : ↥(continuousCohomology 2
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)))) = z := by
    rw [hy]
    exact AddEquiv.apply_symm_apply _ _
  rw [← hz]
  -- 2. 显式↔规范方阵（f := id）
  rw [explicitH2AddEquivContinuousCohomology_map
    (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F) (M := ZMod p)
    (H := AbsoluteGaloisGroup F) (N := ZMod p)
    (φ := Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
    (f := AddMonoidHom.id (ZMod p)) (hf := fun _ _ => rfl) y]
  -- 3. 系数桥（恒等式 ③）
  rw [explicitMap2_quot_id_eq_subtype_comp (F := F) (p := p) y]
  -- 4. 显式↔规范方阵（f := subtype，反向）
  rw [← explicitH2AddEquivContinuousCohomology_map
    (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
    (M := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
    (H := AbsoluteGaloisGroup F) (N := ZMod p)
    (φ := Subgroup.quotientMkContinuousMonoidHom (inertiaLoc F))
    (f := (FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)).subtype)
    (hf := fun k n => coe_quotient_smul_subtype_fixedPoints (F := F) (p := p) (inertiaLoc F) k n)
    (x := explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
      (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
      (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F))
      (coeffSubAddHom (p := p) (I := inertiaLoc F))
      continuous_of_discreteTopology
      (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) y)]
  -- 5. `∂² ∘ Inf₂ = 0`（源系数 `M^I`）
  exact deltaTwoCarrierInertia_comp_infl_eq_zero (F := F) (p := p) (q := q) (hcop := hcop)
    (explicitH2AddEquivContinuousCohomology
      (G := AbsoluteGaloisGroup F ⧸ inertiaLoc F)
      (M := ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p)))
      (explicitMap2 (AbsoluteGaloisGroup F ⧸ inertiaLoc F) (ZMod p)
        (AbsoluteGaloisGroup F ⧸ inertiaLoc F)
        ↥(FixedPoints.addSubgroup (↥(inertiaLoc F)) (ZMod p))
        (ContinuousMonoidHom.id (AbsoluteGaloisGroup F ⧸ inertiaLoc F))
        (coeffSubAddHom (p := p) (I := inertiaLoc F))
        continuous_of_discreteTopology
        (coeffSubAddHom_smul (F := F) (p := p) (inertiaLoc F)) y))

end L20261018

#print axioms L20261018.deltaTwoCarrierInertia_map_pair_id_eq_zero
