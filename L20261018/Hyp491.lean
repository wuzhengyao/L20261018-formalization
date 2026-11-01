import L20261018.Hyp490

/-!
# S41 R2（动作 Z0）：**零系数映射的 `coeffMap` 为零** ⟹ **S40 的 `∂₂`-候选恒为零（`✗-refuted`）**

## 本轮

`Hyp489` 已机检 `v ∘ kummerCoeffToKnrUnits = 0`（`μ_p` 全是单位），`Hyp487` 已机检
`kummerResidueMap = dimShift ∘ v_* ∘ (μ_p ↪ K_nr^×)_*`（`rfl`）。缺的最后一环是**库函子性**：

```
coeffMap (0 : X ⟶ Y) n = 0        -- 即 ContinuousCohomology.map _ 0 n = 0
```

本轮把它落件（**通用引理，与战役无关**）：

| 声明 | 内容 |
|---|---|
| `resolutionMap_zero_eq` | `resolutionMap φ 0 j = 0`（对 `j` 归纳；`rfl` 收尾） |
| `cochainsMap_zero_eq` | `cochainsMap φ 0 = 0`（逐分量，用 `cochainsMap_f`） |
| `map_zero_eq` | ★ `ContinuousCohomology.map φ 0 n = 0`（`homologyMap_zero`） |
| **`coeffMap_zero_eq`** | ★★★ **`coeffMap (0 : X ⟶ Y) n = 0`**（`coeffMap_def` 化到 `map`） |

## 结论链（本件的机检链）

```
① v ∘ kummerCoeffToKnrUnits = 0                          -- Hyp489
② coeffMap 是函子（coeffMap_comp）＋ 零元映射 → 零         -- 本轮 coeffMap_zero_eq
⟹ knrProjCoeffAdd.comp kummerCoeffToKnrAdd = 0
⟹ kummerResidueAdd = 0                                    -- ① 的上游整块归零
⟹ kummerResidueInt = 0 ⟹ kummerResidueH1ZMod = 0 ⟹ knrD = 0
⟹ dPartial = 0 ⟹ dPartialLin = 0                          -- S40 路线造出的 d 是零映射
⟹ KnrResidueReduced ⟹ Subsingleton (VKG)                  -- ③c 把它压成「VKG 只有一个点」
```

⟹ **`kummerResidueMap` 作为 `∂₂` ＝ `✗-refuted`**（恒零，不是「证不出来」）；
`KnrResidueReduced`（对 `dPartialLin`）＝ `✗-refuted`，其**精确存活条件**是 `VKG = ⊥`。

## 诚实边界

* 本件**不**声称 `Ch4TameSymbolHyp` 为假 —— 它是 `∃d`，换一条 `d` 仍可能成立；
  其正确路线见 `S41-STATUS.md` §4 / `S41-RECON-IV-GS68.md`（GS §6.8 的 `∂_v`）。
* `Hyp490.knrResidueObligation_iff_exists_three` 把剩余工作表述为「造一条 `d` 使 (A)(B)(C) 成立」；
  本件证明 S40 造的那条 `d` **不满足** (C)，除非 `VKG` 退化。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

/-! ## 1. 通用引理：零映射的 `coeffMap` 为零 -/

section General

variable {k : Type} [Ring k] [TopologicalSpace k]
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- `resolutionMap φ 0 = 0`（对层数归纳；末步是 `rfl`：`coind₁ResMap φ 0` 与 `Hom.hom 0` 定义相等）。 -/
theorem resolutionMap_zero_eq (φ : H →ₜ* G) (X : TopRep k G) (Y : TopRep k H) (j : ℕ) :
    ContinuousCohomology.resolutionMap φ (0 : TopRep.res (φ : H →* G) X ⟶ Y) j = 0 := by
  induction j with
  | zero => exact ContinuousCohomology.resolutionMap_zero φ _
  | succ i ih =>
    rw [ContinuousCohomology.resolutionMap_succ, ih]
    apply TopRep.hom_ext
    simp only [TopRep.hom_ofHom]
    ext F x
    rfl

/-- `cochainsMap φ 0 = 0`（逐分量，`cochainsMap_f` ＋ 上一件）。 -/
theorem cochainsMap_zero_eq (φ : H →ₜ* G) (X : TopRep k G) (Y : TopRep k H) :
    ContinuousCohomology.cochainsMap φ (0 : TopRep.res (φ : H →* G) X ⟶ Y) = 0 := by
  ext i : 1
  rw [ContinuousCohomology.cochainsMap_f, resolutionMap_zero_eq]
  rfl

/-- ★ **零态射的上同调映射为零**：`ContinuousCohomology.map φ 0 n = 0`。 -/
theorem map_zero_eq (φ : H →ₜ* G) (X : TopRep k G) (Y : TopRep k H) (n : ℕ) :
    ContinuousCohomology.map φ (0 : TopRep.res (φ : H →* G) X ⟶ Y) n = 0 := by
  rw [ContinuousCohomology.map, cochainsMap_zero_eq]
  exact HomologicalComplex.homologyMap_zero _ _ n

/-- ★★★ **`coeffMap` 把零态射送到零**（`coeffMap_def` 化到 `map`，再用上一件）。 -/
theorem coeffMap_zero_eq {X Y : TopRep k G} (n : ℕ) :
    ContinuousCohomology.coeffMap (0 : X ⟶ Y) n = 0 := by
  rw [ContinuousCohomology.coeffMap_def]
  exact map_zero_eq (ContinuousMonoidHom.id G) X Y n

end General

/-! ## 2. 战役侧：`v` 杀掉 `μ_p` 的像 ⟹ 第一段归零 -/

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- ★★★★ **`kummerCoeffToKnr ≫ v` 是零态射**（系数层 `v ∘ kummer = 0` 的 `TopRep` 形式）。 -/
theorem kummerCoeffToKnr_comp_proj_eq_zero :
    kummerCoeffToKnr (K := F) p ≫
      TauCeti.ofDiscreteModuleMap (knrShortExact' F).proj.toIntLinearMap
        (knrShortExact' F).proj_equivariant = 0 := by
  rw [kummerCoeffToKnr]
  refine TopRep.hom_ext (DFunLike.ext _ _ fun m => ?_)
  show (knrShortExact' F).proj (kummerCoeffToKnrUnits (K := F) p m) = 0
  exact knrProjOn_kummerCoeffToKnrUnits (F := F) p m

/-! ## 3. 归零链：`kummerResidueAdd = 0` → … → `dPartialLin = 0` -/

/-- ★★★★ **`v_* ∘ (μ_p ↪ K_nr^×)_* = 0`**（`coeffMap` 函子性 ＋ 上一件 ＋ 零元）。 -/
theorem knrProjCoeffAdd_comp_kummerCoeffToKnrAdd_eq_zero :
    (knrProjCoeffAdd (F := F)).comp (kummerCoeffToKnrAdd (F := F) p) = 0 := by
  refine AddMonoidHom.ext (fun x => ?_)
  show (ContinuousCohomology.coeffMap
      (TauCeti.ofDiscreteModuleMap (knrShortExact' F).proj.toIntLinearMap
        (knrShortExact' F).proj_equivariant) (0 + 2)).hom
    ((ContinuousCohomology.coeffMap (kummerCoeffToKnr (K := F) p) (0 + 2)).hom x) = 0
  show (ContinuousCohomology.coeffMap (kummerCoeffToKnr (K := F) p) (0 + 2) ≫
      ContinuousCohomology.coeffMap
        (TauCeti.ofDiscreteModuleMap (knrShortExact' F).proj.toIntLinearMap
          (knrShortExact' F).proj_equivariant) (0 + 2)).hom x = 0
  rw [← ContinuousCohomology.coeffMap_comp, kummerCoeffToKnr_comp_proj_eq_zero,
    coeffMap_zero_eq]
  rfl

/-- ★★★★★ **S40 的 `∂₂`-候选恒为零（第一段）**：`kummerResidueAdd = 0`。

`kummerResidueAdd = dimShift ∘ (v_* ∘ kummer_*)`，而内层已归零。 -/
theorem kummerResidueAdd_eq_zero : kummerResidueAdd (F := F) p = 0 := by
  refine AddMonoidHom.ext (fun x => ?_)
  show (dimShiftEquiv (F := F) 0).toAddEquiv
    ((knrProjCoeffAdd (F := F)).comp (kummerCoeffToKnrAdd (F := F) p) x) = 0
  rw [knrProjCoeffAdd_comp_kummerCoeffToKnrAdd_eq_zero]
  exact map_zero _

/-- ★★★★★ **`∂₂` 的 `ℤ`-系数形态恒为零**。 -/
theorem kummerResidueInt_eq_zero : kummerResidueInt (F := F) p = 0 := by
  refine AddMonoidHom.ext (fun x => ?_)
  show (intH2AddEquivH1RatOverZ (F := F)).symm (kummerResidueAdd (F := F) p x) = 0
  rw [kummerResidueAdd_eq_zero]
  exact map_zero _

/-- ★★★★★ **`∂₂` 的最终形态恒为零**：`H²(ℤ,μ_p) →+ H¹(ℤ, ℤ/p)` 是零映射。 -/
theorem kummerResidueH1ZMod_eq_zero : kummerResidueH1ZMod (F := F) p = 0 := by
  have hcod : (kummerResidueInt (F := F) p).codRestrict (nsmulAddMonoidHom p).ker
      (fun x => by
        rw [AddMonoidHom.mem_ker]
        show nsmulAddMonoidHom p (kummerResidueInt (F := F) p x) = 0
        simpa using kummerResidueInt_torsion (F := F) p x) = 0 := by
    refine AddMonoidHom.ext (fun x => Subtype.ext ?_)
    show kummerResidueInt (F := F) p x = 0
    rw [kummerResidueInt_eq_zero]
    rfl
  rw [kummerResidueH1ZMod, hcod, AddMonoidHom.comp_zero]

/-- ★★★★★ **S40 的 `d`（加性形态）恒为零**：`knrD = 0`。 -/
theorem knrD_eq_zero (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    knrD (F := F) p hpF hζ = 0 := by
  rw [knrD, kummerResidueH1ZMod_eq_zero, AddMonoidHom.zero_comp]

/-- ★★★★★ **S40 的 `d`（`GaloBase.V` 形态）恒为零**：`dPartial = 0`。 -/
theorem dPartial_eq_zero (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    dPartial (F := F) p hpF hζ = 0 := by
  rw [dPartial, knrD_eq_zero, AddMonoidHom.comp_zero]

/-- ★★★★★★ **S40 路线的 `d` 是零映射**：`dPartialLin = 0`。

⟹ `Hyp488.KnrResidueReduced` 的第 3 条（③c：`d (y ⌣ π) = y`）**对该 `d` 不可能成立**，
除非 `VKG = ⊥`（见下一件）。 -/
theorem dPartialLin_eq_zero (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    dPartialLin (F := F) p hpF hζ = 0 := by
  rw [dPartialLin]
  rw [dPartial_eq_zero]
  rfl

variable (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)

/-- ★★★★★★ **`KnrResidueReduced` 的精确存活条件**：它迫使 `VKG` 只有一个点。

由 ③c（`d (y ⌣ π) = y`）＋ `d = 0` 得 `∀ y : VKG, y = 0`。
⟹ S40 的 `d` 只在**退化**情形（`ker v̄ = ⊥`）满足义务；这正是 `S40-REMAINING-PLAN` §3
路线作废的机检形式。 -/
theorem subsingleton_of_knrResidueReduced (hpF : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : KnrResidueReduced (F := F) p v π hpF hζ) :
    Subsingleton (VKG F p v hpF) := by
  have hd := dPartialLin_eq_zero (F := F) p hpF hζ
  have hone : ∀ y : VKG F p v hpF, y = 0 := by
    intro y
    have hy := h.2.2 y
    rw [hd] at hy
    rw [LinearMap.zero_apply] at hy
    exact Subtype.ext hy.symm
  refine ⟨fun a b => ?_⟩
  rw [hone a, hone b]

end L20261018

#print axioms L20261018.resolutionMap_zero_eq
#print axioms L20261018.cochainsMap_zero_eq
#print axioms L20261018.map_zero_eq
#print axioms L20261018.coeffMap_zero_eq
#print axioms L20261018.kummerCoeffToKnr_comp_proj_eq_zero
#print axioms L20261018.knrProjCoeffAdd_comp_kummerCoeffToKnrAdd_eq_zero
#print axioms L20261018.kummerResidueAdd_eq_zero
#print axioms L20261018.kummerResidueInt_eq_zero
#print axioms L20261018.kummerResidueH1ZMod_eq_zero
#print axioms L20261018.knrD_eq_zero
#print axioms L20261018.dPartial_eq_zero
#print axioms L20261018.dPartialLin_eq_zero
#print axioms L20261018.subsingleton_of_knrResidueReduced
