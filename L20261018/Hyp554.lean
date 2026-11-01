import L20261018.Hyp553

/-!
# S46 R3：★★★★ **(d) 的两块** —— (I) 右端拆分 `map φ fC = i_* ≫ Inf_C`；(III) `δ_Γ` 是同构

## 数学内容

`(d)` = `Inf_A ≫ ∂₂ = 0`（GS 6.8.2 在 `H²(G,A)` 处的正合）。展开（`∂₂ = δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M`）：

```
δ_Γ ≫ (Inf_A ≫ ∂₂)
  = (δ_Γ ≫ Inf_A) ≫ δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M
  = (map φ fC ≫ δ_Γ) ≫ δ_Γ⁻¹ ≫ Inf_C⁻¹ ≫ M     -- (F1)，Hyp553
  = map φ fC ≫ Inf_C⁻¹ ≫ M
  = i_* ≫ Inf_C ≫ Inf_C⁻¹ ≫ M                    -- (I) 本件：右端拆分
  = i_* ≫ M                                       -- Inf_C 是同构
  = 0                                             -- (II) 下一件（连续 (F2) 抬到 T 层）
⟹ Inf_A ≫ ∂₂ = 0                                 -- (III) 本件：Epi δ_Γ
```

## 机检内容

| 声明 | 内容 |
|---|---|
| **`isIso_contCoindSES_delta`** | ★★★★ **(III)**：`δ_Γ : H¹(Γ,C) → H²(Γ,A)` **是同构**（`isIso_coindShortExact_bot_delta`，无条件） |
| `epi_contCoindSES_delta` | 其 `Epi` 推论（`(d)` 收口用） |
| **`contMapFC_split`** | ★★★★★ **(I)**：`map φ fC = i_* ≫ Inf_C`（`map_comp` ＋ `pair` 的分解式） |
| **`contF1_split`** | ★★★ `(F1)` 的可用形态：左端拆 `Inf_A`、右端拆 `i_* ≫ Inf_C` |

## 诚实边界

* 本件**不含 (II)**：`i_* ≫ M = 0`（连续 `iTame ≫ deltaZeroBar = 0`）仍缺；`M` 需要
  `Cᴵ → H¹(I,μ_p)` 的 `(Γ⧸I)`-等变形态，库内 `contDeltaZeroBar` 只有 `TopModuleCat` 层。
* 本件**不**证 `IsIso δ_T`（`(d)` 的 `Epi` 用的是 `δ_Γ` 而非 `δ_T`）。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open CategoryTheory Limits TauCeti ContCohomology

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
variable (I : Subgroup (AbsoluteGaloisGroup F)) [I.Normal]

/-! ### (III) `δ_Γ` 是同构 -/

/-- ★★★★ **(III)**：`δ_Γ : H¹(Γ, C) ⟶ H²(Γ, μ_p)` 是**同构**。

这是 GS (6.15) 的 `i = 2` 情形：`Coind_1^Γ(μ_p)` 在次数 1 与 2 上零调，
库内 `isIso_coindShortExact_bot_delta`（`DimensionShifting/Basic.lean:180`）**无条件**给出。 -/
theorem isIso_contCoindSES_delta :
    IsIso ((contCoindSES (F := F) p).delta 1) :=
  ContCohomology.isIso_coindShortExact_bot_delta (G := AbsoluteGaloisGroup F) (M := ZMod p) 1
    (by norm_num)

/-- `δ_Γ` 是满的（`(d)` 收口：`δ ≫ X = 0 ⟹ X = 0` 需要 `Epi`，不是 `Mono`）。 -/
theorem epi_contCoindSES_delta : Epi ((contCoindSES (F := F) p).delta 1) := by
  haveI := isIso_contCoindSES_delta (F := F) p
  infer_instance

/-! ### (I) 右端拆分 `map φ fC = i_* ≫ Inf_C` -/

/-- `i : T → Cᴵ` 视为 `(Γ⧸I)`-模层映射（`coeffMap` 的输入，即 GS 的 `i_*` 的来源）。 -/
noncomputable abbrev contPairITame :
    ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contT (F := F) p I) ⟶
      ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvC (F := F) p I) :=
  ofDiscreteModulePair (MonoidHom.id ((AbsoluteGaloisGroup F) ⧸ I))
    (contITame (F := F) p I).toIntLinearMap (contITame_smul (F := F) p I)

/-- `(Cᴵ ↪ C)` 视为沿 `φ` 的相容对（即 GS 的 `Inf_C` 的来源）。 -/
noncomputable abbrev contPairSubtypeC :
    TopRep.res (I.quotientMkContinuousMonoidHom : AbsoluteGaloisGroup F →* _)
        (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvC (F := F) p I)) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p) :=
  ofDiscreteModulePair (I.quotientMkContinuousMonoidHom :
      AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)
    (FixedPoints.addSubgroup (↥I) (contC (F := F) p)).subtype.toIntLinearMap
    I.fixedPoints_subtype_quotientMk_smul

/-- `fC` 视为沿 `φ` 的相容对。 -/
noncomputable abbrev contPairFC :
    TopRep.res (I.quotientMkContinuousMonoidHom : AbsoluteGaloisGroup F →* _)
        (ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contT (F := F) p I)) ⟶
      ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p) :=
  ofDiscreteModulePair (I.quotientMkContinuousMonoidHom :
      AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)
    (contFC (F := F) p I).toIntLinearMap (contFC_smul (F := F) p I)

/-- 相容对的分解式（集合并结）：`fC` 的相容对 = `i` 的相容对（沿 `Γ⧸I`）≫ `Cᴵ ↪ C` 的相容对。 -/
theorem contPairFC_eq :
    contPairFC (F := F) p I
      = (TopRep.resFunctor (I.quotientMkContinuousMonoidHom :
            AbsoluteGaloisGroup F →* (AbsoluteGaloisGroup F) ⧸ I)).map
          (contPairITame (F := F) p I) ≫ contPairSubtypeC (F := F) p I := by
  apply ofDiscreteModulePair_eq_of_hom_apply
  intro c
  rfl

/-- ★★★★★ **(I)**：`map φ fC = i_* ≫ Inf_C`。

`i_* = coeffMap (contPairITame)`、`Inf_C = coeffMap (ofDiscreteModuleQuotient Γ C I) ≫ infl I C`。
证明 = `ContinuousCohomology.map_comp`（`Functoriality.lean:163`，取 `φ = id`、`ψ = φ`）
＋ `coeffMap_ofDiscreteModuleQuotient_comp_infl`（`Inflation/Comparison.lean:95`）。 -/
theorem contMapFC_split (n : ℕ) :
    _root_.ContinuousCohomology.map (I.quotientMkContinuousMonoidHom)
        (contPairFC (F := F) p I) n
      = TauCeti.ContinuousCohomology.coeffMap (contPairITame (F := F) p I) n
        ≫ TauCeti.ContinuousCohomology.coeffMap
            (ofDiscreteModuleQuotient (AbsoluteGaloisGroup F) (contC (F := F) p) I) n
        ≫ TauCeti.ContinuousCohomology.infl I
            (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) n := by
  conv_lhs => rw [contPairFC_eq (F := F) p I]
  -- `map φ` 与 `map ((id).comp φ)` 只是同态命题相等：用 `map_congr`
  rw [TauCeti.ContinuousCohomology.map_congr_of_hom_apply
    (ContinuousMonoidHom.ext (fun x => rfl) :
      (ContinuousMonoidHom.id ((AbsoluteGaloisGroup F) ⧸ I)).comp
        (I.quotientMkContinuousMonoidHom) = I.quotientMkContinuousMonoidHom).symm _ _
    (fun _ => rfl) n]
  -- `map_comp`：把 `(res φ).map i ≫ (Cᴵ ↪ C)` 拆成两个因子
  rw [_root_.ContinuousCohomology.map_comp
    (φ := ContinuousMonoidHom.id ((AbsoluteGaloisGroup F) ⧸ I))
    (ψ := I.quotientMkContinuousMonoidHom)
    (X := ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contT (F := F) p I))
    (Y := ofDiscreteModule ℤ ((AbsoluteGaloisGroup F) ⧸ I) (contInvC (F := F) p I))
    (Z := ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p))
    (contPairITame (F := F) p I) (contPairSubtypeC (F := F) p I) n]
  -- `Inf_C` 的 `coeffMap ≫ infl` 分解
  rw [← TauCeti.ContCohomology.coeffMap_ofDiscreteModuleQuotient_comp_infl
    (G := AbsoluteGaloisGroup F) (M := contC (F := F) p) (N := I) n]
  rfl

/-- ★★★ **(F1) 的可用形态**：左端 `Inf_A` 已拆、右端已拆成 `i_* ≫ Inf_C`。

`(d)` 的收口直接消费此式：再乘 `Inf_C⁻¹ ≫ M` 即得 `δ_Γ ≫ (Inf_A ≫ ∂₂) = i_* ≫ M`。 -/
theorem contF1_split (n : ℕ) :
    (contInvSES (F := F) p I).delta n
        ≫ TauCeti.ContinuousCohomology.coeffMap
            (ofDiscreteModuleQuotient (AbsoluteGaloisGroup F) (ZMod p) I) (n + 1)
        ≫ TauCeti.ContinuousCohomology.infl I
            (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (ZMod p)) (n + 1)
      = TauCeti.ContinuousCohomology.coeffMap (contPairITame (F := F) p I) n
        ≫ TauCeti.ContinuousCohomology.coeffMap
            (ofDiscreteModuleQuotient (AbsoluteGaloisGroup F) (contC (F := F) p) I) n
        ≫ TauCeti.ContinuousCohomology.infl I
            (ofDiscreteModule ℤ (AbsoluteGaloisGroup F) (contC (F := F) p)) n
        ≫ (contCoindSES (F := F) p).delta n := by
  rw [contF1_infl (F := F) p I n, contMapFC_split (F := F) p I n]
  simp only [Category.assoc]

end L20261018

#print axioms L20261018.isIso_contCoindSES_delta
#print axioms L20261018.contPairFC_eq
#print axioms L20261018.contMapFC_split
#print axioms L20261018.contF1_split
