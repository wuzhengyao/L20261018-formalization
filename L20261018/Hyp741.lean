import Hyp737
import Hyp740

/-!
# S67 R1：分片 **4d 组装收官** —— `∂² ∘ Inf₂ = 0`（C4 的核心）

`S66-4CV-PLAN.md` **§7** 的 6 步链条，本件把它**串成一条机检定案**。
6 步与 6 条 `have` 一一对应（全部机检件此前已在库，本件只补**第 4 步**）：

| 步 | 改写 | 件 | 本件处置 |
|---|---|---|---|
| 1 | `(δ¹_Γ)⁻¹(Inf₂ x) → map φ fC 1 z`（`z := (δ¹_{SES1})⁻¹ x`） | `Hyp740.delta_inv_comp_infl_eq` | `h1`（＋`deltaShift1_eq_deltaAddEquivOfSub`） |
| 2 | `map φ fC 1 → map φ sub 1 ∘ coeffMap ι 1` | `Hyp734.coeffMap_comp_map_quotientMk` | **`map_fCG_apply`（本件新证）** |
| 3 | `h1BridgeQ_C ∘ map φ sub 1 → explicitInfl1 ∘ h1BridgeQ_{Cᴵ}` | `Hyp736.h1BridgeQ_infl` | `h3` |
| **4** | **`inflStep ∘ explicitInfl1 → id`** | **`Hyp719.inflStep_explicitInfl1`（本件新增）** | `h4` |
| 5 | `h1BridgeQ_{Cᴵ} ∘ coeffMap ι → explicitCoeff1 ι ∘ h1BridgeQ_T` | `Hyp735.h1BridgeQ_coeffMap` | `h5` |
| 6 | `contM_coeffMap ∘ explicitCoeff1 ι → 0` | `Hyp739.coeffMap_comp_coeffMap_eq_zero` ＋ `hzero` | `h6` |

**本件补的两件**（`PROMPT-S67` §①-1 的正解）：

1. **第 4 步**写进 `Hyp719` **自己的文件**（`inflStep` 的定义处），一次即通：
   `inflStep_explicitInfl1`（`AddEquiv.symm_apply_apply`）。写在新文件会撞 `whnf` 超 8M（`M18`）。
2. **第 2 步**：`map φ fC` 与 `map φ sub ≫ coeffMap ι` 的桥 —— `map_congr_of_hom_apply`
   （逐点相等是 `rfl`）＋ `Hyp734`。

## 两处**代价**（如实登记）

* 陈述里写 `deltaTwoShift` 的**展开式** `deltaShift1.trans (h1BridgeQ.trans (inflStep hC))`
  而非 `deltaTwoShift` 本身：后者在**抽象语境**（`G`、`C` 为变量）下会撞 `whnf` 超 8M
  （实测：`deltaTwoShift` 直接写出即 8M 超时；写成展开式秒过）。两者是**定义级**相等
  （`Hyp719:82` 的定义就是三项 `.trans`）⟹ 战役级（`Hyp723`，`G = AbsoluteGaloisGroup F`）用
  `deltaTwoShift` 形态**照常可写**（`Hyp723` 已编译即是证据）。
* 本件三条实例 `[SeparatelyContinuousMul G] [TotallyDisconnectedSpace G] [IsClosed ↑I]` 是
  `Hyp719.inflStep_explicitInfl1` 的**伴随形参**（由 `explicitInfl1` 的实例合成路径带上，
  与该引理陈述本身无关）。战役里 `G = AbsoluteGaloisGroup F`、`I = inertiaLoc F` **全部满足**。
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


variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]
variable (I : Subgroup G) [I.Normal] [IsClosed (I : Set G)]
variable {T : Type} [AddCommGroup T] [TopologicalSpace T] [DiscreteTopology T]
  [DistribMulAction (G ⧸ I) T] [ContinuousSMul (G ⧸ I) T]

/-- `fC := sub ∘ ι : T →+ C`（`G`-兼容对的系数映射；`T` 抽象，避免 `TBI` 的 `abbrev` 展开）。 -/
noncomputable def fCG (ι : T →+[G ⧸ I] ↥(FixedPoints.addSubgroup (↥I) C)) : T →+ C :=
  (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap.toAddMonoidHom.comp ι.toAddMonoidHom

/-- `fCG` 的兼容性：`fC (φ g • x) = g • fC x`（`φ = G → G⧸I`）。 -/
theorem fCG_compat (ι : T →+[G ⧸ I] ↥(FixedPoints.addSubgroup (↥I) C)) (g : G) (x : T) :
    fCG (C := C) I ι ((g : G ⧸ I) • x) = g • fCG (C := C) I ι x := by
  show ((ι ((g : G ⧸ I) • x) : FixedPoints.addSubgroup (↥I) C) : C)
      = g • ((ι x : FixedPoints.addSubgroup (↥I) C) : C)
  rw [map_smul]
  exact I.fixedPoints_subtype_quotientMk_smul g (ι x)

/-- ★★★★★ **4d 第 2 步**：`map φ fC = map φ sub ≫ coeffMap ι`（逐点形态）。

`map_congr_of_hom_apply`（`fC = sub ∘ ι` 逐点相等，故 `rfl`）把 `fC` 的兼容对换成
`(res φ).map ι ≫ sub`，再用 `Hyp734.coeffMap_comp_map_quotientMk` 拆开。 -/
theorem map_fCG_apply (ι : T →+[G ⧸ I] ↥(FixedPoints.addSubgroup (↥I) C))
    (z : ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I) T)).toModuleCat) :
    (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
      (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
        (fCG (C := C) I ι).toIntLinearMap (fCG_compat (C := C) I ι)) 1) z
    = (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
          (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
          I.fixedPoints_subtype_quotientMk_smul) 1)
      ((ContinuousCohomology.coeffMap
        (TauCeti.ofDiscreteModuleMap ι.toAddMonoidHom.toIntLinearMap
          (fun g m => map_smul ι g m)) 1) z) := by
  have h734 := coeffMap_comp_map_quotientMk (R := ℤ) (I := I)
    (X := ofDiscreteModule ℤ (G ⧸ I) T)
    (Y := ofDiscreteModule ℤ (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) C))
    (Z := ofDiscreteModule ℤ G C)
    (TauCeti.ofDiscreteModuleMap ι.toAddMonoidHom.toIntLinearMap (fun g m => map_smul ι g m))
    (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
      (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
      I.fixedPoints_subtype_quotientMk_smul) 1
  have hmap : (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
      (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
        (fCG (C := C) I ι).toIntLinearMap (fCG_compat (C := C) I ι)) 1)
      = ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        ((TopRep.resFunctor
            (↑(Subgroup.quotientMkContinuousMonoidHom I) : G →* (G ⧸ I))).map
          (TauCeti.ofDiscreteModuleMap ι.toAddMonoidHom.toIntLinearMap (fun g m => map_smul ι g m))
          ≫ TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
              (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
              I.fixedPoints_subtype_quotientMk_smul) 1 :=
    ContinuousCohomology.map_congr_of_hom_apply rfl _ _ (fun x => rfl) 1
  rw [hmap, ← h734]
  rfl

/-! ## 4d 组装（6 步链） -/

variable [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable (S : DiscreteShortExact G A B C)

/-- `deltaShift1` 与 `deltaAddEquivOfSub` 的定义级一致（同一 `AddEquiv.ofBijective`）。 -/
theorem deltaShift1_eq_deltaAddEquivOfSub
    (h1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ G B)).toModuleCat)
    (h2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ G B)).toModuleCat) :
    deltaShift1 (C := C) S h1 h2 = (deltaAddEquivOfSub S 1 h1 h2).symm := rfl

/-- ★★★★★ **4d 组装 ＝ C4 的核心**：`∂² ∘ Inf₂ = 0`。

**链条**（`S66-4CV-PLAN.md` §7 的 6 步，逐一对应下面 6 条 `have`）：

```
∂² ∘ Inf₂ (x) = contM_coeffMap ( inflStep ( h1BridgeQ ( (δ¹_Γ)⁻¹ (Inf₂ x) ) ) )
   = contM_coeffMap ( inflStep ( h1BridgeQ ( map φ fC 1 z ) ) )                  -- h1 : Hyp740
   = contM_coeffMap ( inflStep ( h1BridgeQ ( map φ sub 1 (coeffMap ι 1 z) ) ) ) -- h2 : map_fCG_apply
   = contM_coeffMap ( inflStep ( explicitInfl1 ( h1BridgeQ_Cᴵ (coeffMap ι 1 z) ) ) ) -- h3 : Hyp736
   = contM_coeffMap ( h1BridgeQ_Cᴵ (coeffMap ι 1 z) )                          -- h4 : Hyp719 新引理
   = contM_coeffMap ( explicitCoeff1 ι ( h1BridgeQ_T z ) )                     -- h5 : Hyp735
   = 0                                                                         -- h6 : Hyp739 + hzero
```

其中 `z := (δ¹_{SES1})⁻¹ x`。

⚠ **陈述里写的是 `deltaTwoShift` 的展开式**（`deltaShift1.trans (h1BridgeQ.trans (inflStep hC))`）
而不是 `deltaTwoShift` 本身：后者在抽象语境下会撞 `whnf` 超预算（8M）。它与 `deltaTwoShift` 是
**定义级**相等（`Hyp719:82` 的定义就是这三项 `.trans`），战役级（`Hyp723`）用 `deltaTwoShift` 形态。 -/
theorem deltaTwoShift_comp_infl_eq_zero
    [ContinuousSMul (G ⧸ I) (TBI S I)]
    [ContinuousSMul (G ⧸ I) ↥(FixedPoints.addSubgroup (↥I) C)]
    (hB1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hB2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) B))).toModuleCat)
    (hA1 : Subsingleton ↑(continuousCohomology 1 (ofDiscreteModule ℤ G B)).toModuleCat)
    (hA2 : Subsingleton ↑(continuousCohomology 2 (ofDiscreteModule ℤ G B)).toModuleCat)
    (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥I C)))
    {P : Type} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DiscreteTopology P] [DistribMulAction (G ⧸ I) P] [ContinuousSMul (G ⧸ I) P]
    (N' : ↥(FixedPoints.addSubgroup (↥I) C) →+[G ⧸ I] P) (hN' : Continuous ⇑N')
    (hzero : ∀ x : TBI S I, N' (iotaHom S I x) = 0)
    (x : ↑(continuousCohomology 2 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) A))).toModuleCat) :
    explicitCoeff1 (G := G ⧸ I) (M := ↥(FixedPoints.addSubgroup (↥I) C)) (N := P) N' hN'
      (((deltaShift1 (C := C) S hA1 hA2).trans
        ((h1BridgeQ (C := C)).trans (inflStep (H := I) (C := C) hC)))
        ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (FixedPoints.addSubgroup (↥I) A).subtype.toIntLinearMap
            I.fixedPoints_subtype_quotientMk_smul) 2) x)) = 0 := by
  set z : ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I) (TBI S I))).toModuleCat :=
    (deltaAddEquiv_sesCoind1 S I hB1 hB2).symm x with hz
  set w : ↑(continuousCohomology 1 (ofDiscreteModule ℤ (G ⧸ I)
      ↥(FixedPoints.addSubgroup (↥I) C))).toModuleCat :=
    (ContinuousCohomology.coeffMap
      (TauCeti.ofDiscreteModuleMap (iotaHom S I).toAddMonoidHom.toIntLinearMap
        (fun g m => map_smul (iotaHom S I) g m)) 1) z with hw
  have h1 : deltaShift1 (C := C) S hA1 hA2
      ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
          (FixedPoints.addSubgroup (↥I) A).subtype.toIntLinearMap
          I.fixedPoints_subtype_quotientMk_smul) 2) x)
      = (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (fCG (C := C) I (iotaHom S I)).toIntLinearMap (fCG_compat (C := C) I (iotaHom S I)))
          1) z := by
    rw [deltaShift1_eq_deltaAddEquivOfSub]
    exact delta_inv_comp_infl_eq S I (fCG (C := C) I (iotaHom S I))
      (fCG_compat (C := C) I (iotaHom S I)) (fun a => rfl)
      (fun b => by
        show ((iota S I (QuotientAddGroup.mk' (inclI S I).range b) :
          FixedPoints.addSubgroup (↥I) C) : C) = S.proj ↑b
        rw [iota_mk]; rfl)
      hB1 hB2 hA1 hA2 x
  have h2 : (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
      (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
        (fCG (C := C) I (iotaHom S I)).toIntLinearMap
        (fCG_compat (C := C) I (iotaHom S I))) 1) z
      = (ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
          (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
            (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
            I.fixedPoints_subtype_quotientMk_smul) 1) w := by
    rw [hw]
    exact map_fCG_apply (C := C) I (iotaHom S I) z
  have h3 : h1BridgeQ (C := C)
      ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
          (FixedPoints.addSubgroup (↥I) C).subtype.toIntLinearMap
          I.fixedPoints_subtype_quotientMk_smul) 1) w)
      = explicitInfl1 G C I
          (h1BridgeQ (G := G ⧸ I) (C := ↥(FixedPoints.addSubgroup (↥I) C)) w) :=
    h1BridgeQ_infl (G := G) (C := C) I w
  have h4 : inflStep (H := I) (C := C) hC
      (explicitInfl1 G C I
        (h1BridgeQ (G := G ⧸ I) (C := ↥(FixedPoints.addSubgroup (↥I) C)) w))
      = h1BridgeQ (G := G ⧸ I) (C := ↥(FixedPoints.addSubgroup (↥I) C)) w :=
    inflStep_explicitInfl1 (H := I) (C := C) hC _
  have h5 : h1BridgeQ (G := G ⧸ I) (C := ↥(FixedPoints.addSubgroup (↥I) C)) w
      = explicitCoeff1 (G := G ⧸ I) (M := TBI S I)
          (N := ↥(FixedPoints.addSubgroup (↥I) C)) (iotaHom S I)
          continuous_of_discreteTopology (h1BridgeQ (G := G ⧸ I) (C := TBI S I) z) := by
    rw [hw]
    exact h1BridgeQ_coeffMap (G := G ⧸ I) (M := TBI S I) (↥(FixedPoints.addSubgroup (↥I) C))
      (iotaHom S I) z
  have h6 := coeffMap_comp_coeffMap_eq_zero (G := G ⧸ I) (M := TBI S I)
    (N := ↥(FixedPoints.addSubgroup (↥I) C)) (P := P) (iotaHom S I)
    continuous_of_discreteTopology N' hN' hzero
  show explicitCoeff1 (G := G ⧸ I) (M := ↥(FixedPoints.addSubgroup (↥I) C)) (N := P) N' hN'
    (inflStep (H := I) (C := C) hC (h1BridgeQ (C := C) (deltaShift1 (C := C) S hA1 hA2
      ((ContinuousCohomology.map (Subgroup.quotientMkContinuousMonoidHom I)
        (TauCeti.ofDiscreteModulePair (Subgroup.quotientMkContinuousMonoidHom I : G →* G ⧸ I)
          (FixedPoints.addSubgroup (↥I) A).subtype.toIntLinearMap
          I.fixedPoints_subtype_quotientMk_smul) 2) x)))) = 0
  rw [h1, h2, h3, h4, h5]
  simpa using DFunLike.congr_fun h6 (h1BridgeQ (G := G ⧸ I) (C := TBI S I) z)

end L20261018

#print axioms L20261018.fCG
#print axioms L20261018.fCG_compat
#print axioms L20261018.map_fCG_apply
#print axioms L20261018.deltaShift1_eq_deltaAddEquivOfSub
#print axioms L20261018.deltaTwoShift_comp_infl_eq_zero
