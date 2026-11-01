import L20261018.Hyp735

/-!
# S66 R5：分片 **4c-v（第三格，收官）** —— `h1BridgeQ` 与**膨胀**交换

4c-v 的最后一条自然性：

```
h1BridgeQ_C ∘ map φ (Cᴵ ↪ C) = explicitInfl1_C ∘ h1BridgeQ_{Cᴵ}
```

**关键侦察结论（本轮第 0 步，省下一跳）**：`CohomologyComparison.lean:338` 的
**`explicitH1IsoContinuousCohomology_hom_apply`** 是 **`rfl` 级**：

```
(explicitH1IsoContinuousCohomology G M).hom x
  = explicitH1AddEquivContinuousCohomology G M (discreteH1Equiv G M x)
```

⟹ `explicitH1IsoContinuousCohomology`（`DiscreteH1` 载体）与
`explicitH1AddEquivContinuousCohomology`（`H1` 载体）之间**不需要额外的等式桥**
（上一轮担心的"两跳"其实是一跳，另一个是 `rfl`）。

**证明骨架**：`coeffMap_ofDiscreteModuleQuotient_comp_infl`（`Inflation/Comparison.lean:95`）
把 `map φ (Cᴵ↪C)` 认成 `coeffMap(quotient) ≫ infl`；再用
`explicitIso_infl`（同文件 `:149`，取 `x := h1BridgeIso⁻¹ y`）＋ `rfl` 桥即可。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]

/-- ★★★★★ **`h1BridgeQ` 与膨胀交换**（4c-v 的最后一格）。

`map φ (Cᴵ ↪ C)` 是**连续**模型里的膨胀，`explicitInfl1 G C I` 是**显式**模型里的同一映射；
本件说 `h1BridgeQ`（`H¹` 比较同构）把前者译成后者。 -/
theorem h1BridgeQ_infl (I : Subgroup G) [I.Normal]
    [ContinuousSMul (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) C)]
    (y : ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) C))).toModuleCat) :
    (explicitH1AddEquivContinuousCohomology G C).symm
        ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
            I.fixedPoints_subtype_quotientMk_smul) 1) y)
      = explicitInfl1 G C I
          ((explicitH1AddEquivContinuousCohomology (G ⧸ I)
            ↥(FixedPoints.addSubgroup (↥I) C)).symm y) := by
  -- 1) `map φ (Cᴵ↪C) = coeffMap(quotient) ≫ infl`（库内）
  have hmap : (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
      (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
        (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
        I.fixedPoints_subtype_quotientMk_smul) 1)
      = (TauCeti.ContinuousCohomology.coeffMap.{0, u, u}
          (TauCeti.ofDiscreteModuleQuotient G C I) 1) ≫
        (TauCeti.ContinuousCohomology.infl.{0, u, u} I (ofDiscreteModule ℤ G C) 1) :=
    (TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl (G := G) (M := C) I 1).symm
  -- 2) 用 `explicitIso_infl` 在精心选取的 `x` 上开火：取 `x` 使 `discreteH1Equiv x` 与
  --    `h1BridgeIso x` **同时**退化到目标值（两个 `AddEquiv.apply_symm_apply` ＋ `rfl` 桥）
  set A := ↥(FixedPoints.addSubgroup (↥I) C) with hA
  set eM := explicitH1AddEquivContinuousCohomology (G ⧸ I) A with heM
  set x := (discreteH1Equiv (G ⧸ I) A).symm (eM.symm y) with hx
  have hx1 : eM (eM.symm y) = y := AddEquiv.apply_symm_apply eM y
  have hx2 : (discreteH1Equiv (G ⧸ I) A) x = eM.symm y := AddEquiv.apply_symm_apply _ _
  have hx3 : (explicitH1IsoContinuousCohomology (G ⧸ I) A).hom x = y := by
    rw [explicitH1IsoContinuousCohomology_hom_apply, hx2, hx1]
  have hkey : (explicitH1AddEquivContinuousCohomology G C)
      (explicitInfl1 G C I
        ((explicitH1AddEquivContinuousCohomology (G ⧸ I)
          ↥(FixedPoints.addSubgroup (↥I) C)).symm y))
      = (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
            I.fixedPoints_subtype_quotientMk_smul) 1) y := by
    rw [hmap, ConcreteCategory.comp_apply]
    have h := explicitIso_infl (G := G) (M := C) I x
    rw [hx3, hx2] at h
    rw [h]
    rw [explicitH1IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply]
  rw [← hkey, AddEquiv.symm_apply_apply]

end L20261018

#print axioms L20261018.h1BridgeQ_infl
