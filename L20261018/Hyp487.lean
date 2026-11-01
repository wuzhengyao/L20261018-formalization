import Hyp486

/-!
# S41 R1：动作 A4b-2 第一段 —— **把 `∂₂` 变成加性映射，落到 `H¹(G, ℤ/p)`**

`S40-REMAINING-PLAN.md` §3 动作 A 的最后一步是组装

```
d : GaloBase.H2 F p →ₗ[ZMod p] VKG F p v hpF
```

本轮把「`∂₂` 作为一个**加性映射**」这件事机检到位，路线（全部库内件）：

```
GaloBase.H2 F p
  --kummerH2Bridge-->            H²(ℤ, KummerCoeff F p)        (Hyp486)
  --kummerResidueInt-->          H²(ℤ, ULift ℤ)               (本轮；= intH2AddEquivH1RatOverZ ∘ ∂₂)
  --codRestrict 到 p-挠-->       ker (nsmulAddMonoidHom p)     (Hyp485 的 p-挠性)
  --integralBocksteinH1Equiv⁻¹--> H¹(ℤ, ULift (ZMod p))       (TauCeti.Bockstein.Integral，库内件)
```

## 本轮的两个侦察命中（规则 24 ④：缺口清单不得继承）

1. **`integralBocksteinH1Equiv` 早在库里**（`TauCeti/…/Bockstein/Integral.lean`）：

   ```lean
   integralBocksteinH1Equiv (n : ℕ) [NeZero n] :
     continuousCohomology 1 (ofDiscreteModule ℤ G (ULift (ZMod n))) ≃+
       (nsmulAddMonoidHom n : continuousCohomology 2 (ofDiscreteModule ℤ G (ULift ℤ)) →+ _).ker
   ```

   这正是 `RECON-R3` §107.2「三件要补」里的 ①②③ **全部**（`Submodule` ＋
   `LinearEquiv.ofBijective` ＋ 单射／像引理），⟹ 这三件**不需要自建**。
2. **`kummerResidueMap` 的加性形态可 `rfl` 得到**：它虽是裸函数，但定义体是
   「`dimShiftEquiv`（连续线性等价）∘ `coeffMap`（连续线性）∘ `coeffMap`（连续线性）」，
   故取同样三件的加性形态复合即得，且与 `kummerResidueMap` **定义相等**。

## 口径（工艺决定）

全部中间件用 **`AddMonoidHom`**，最后一步才升级到 `ZMod p`-线性：库内
`AddMonoidHom.toZModLinearMap`（`Mathlib/Algebra/Module/ZMod.lean:81`）对**任何**
两个 `ZMod n`-模之间的加性映射给出 `ZMod n`-线性映射（`ZMod.map_smul` 只用
`AddMonoidHom` 与 `zsmul` 的交换性）。⟹ 组装期不必追 `ℤ`-线性，`map_smul'` 的
`Int.induction_on` 坑（规则 27）整体绕过。

## 本文件**不**声称

* `∂₂` 落在 `ker v̄` 内（动作 A5）；
* 两条杯积公式（③b／③c）—— 那需要 GS `prop-units-cohomology` 的实算，
  见 `S41-STATUS.md` 的诚实分诊。

## 机检件

| 声明 | 内容 |
|---|---|
| `dimShiftAdd` | `H²(G,ℤ) →+ H¹(G,ℚ/ℤ)`（维数平移的加性形态） |
| `kummerResidueAdd` | ★★★★ `∂₂` 在 `H¹(ℚ/ℤ)` 层的加性形态 |
| `kummerResidueMap_eq_add` | 它与 `Hyp473.kummerResidueMap` **定义相等**（`rfl`） |
| **`kummerResidueInt`** | ★★★★★ `H²(ℤ,μ_p) →+ H²(ℤ,ℤ)`（`∂₂` 的 `ℤ`-系数形态） |
| **`kummerResidueInt_torsion`** | ★★★★★ 其像落在 `p`-挠内（`p • ∂₂ x = 0`） |
| **`kummerResidueH1ZMod`** | ★★★★★ **`H²(ℤ,μ_p) →+ H¹(ℤ, ℤ/p)`**（`∂₂` 的最终加性形态） |
| `kummerResidueH1ZMod_spec` | 它与 `integralBockstein` 的相容性（`δ (∂₂ x) = ∂₂ x` 于 `H²(ℤ)`） |
| **`knrD`** | ★★★★★ **`GaloBase.H2 F p →+ H¹(ℤ, ℤ/p)`**（接上 `kummerH2Bridge`） |
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

variable {F : Type} [Field F] (p : ℕ) [NeZero p] [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- `G` 在 `ULift (ZMod p)` 上的平凡作用（`integralBockstein` 的系数结构）。 -/
local instance cyclicTrivialAction' : DistribMulAction (TauCeti.AbsoluteGaloisGroup F)
    (ULift.{0} (ZMod p)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用连续（离散）。 -/
local instance cyclicContinuousSMul' : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F)
    (ULift.{0} (ZMod p)) := ⟨continuous_snd⟩

/-! ## 1. `∂₂` 的加性形态（`ℚ/ℤ` 层） -/

/-- **维数平移的加性形态**：`H²(G,ℤ) →+ H¹(G,ℚ/ℤ)`。 -/
noncomputable def dimShiftAdd :
    ↑(continuousCohomology (0 + 1 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ))).toModuleCat →+
      ↑(continuousCohomology (0 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) QoverZdisc)).toModuleCat :=
  (dimShiftEquiv (F := F) 0).toAddEquiv.toAddMonoidHom

/-- `K_nr^× → ℤ` 在 `H²` 上诱导的加性映射。 -/
noncomputable def knrProjCoeffAdd :
    ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KnrUnits' F))).toModuleCat →+
      ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ))).toModuleCat :=
  ((ContinuousCohomology.coeffMap
    (TauCeti.ofDiscreteModuleMap (knrShortExact' F).proj.toIntLinearMap
      (knrShortExact' F).proj_equivariant) (0 + 2)).hom).toAddMonoidHom

/-- `μ_p → K_nr^×` 在 `H²` 上诱导的加性映射。 -/
noncomputable def kummerCoeffToKnrAdd :
    ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat →+
      ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KnrUnits' F))).toModuleCat :=
  ((ContinuousCohomology.coeffMap (kummerCoeffToKnr (K := F) p) (0 + 2)).hom).toAddMonoidHom

/-- ★★★★ **`∂₂` 的加性形态**：`H²(G,μ_p) →+ H¹(G,ℚ/ℤ)`。

定义上等于 `Hyp473.kummerResidueMap p 0`（见 `kummerResidueMap_eq_add`）。 -/
noncomputable def kummerResidueAdd :
    ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat →+
      ↑(continuousCohomology (0 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) QoverZdisc)).toModuleCat :=
  (dimShiftAdd (F := F)).comp
    ((knrProjCoeffAdd (F := F)).comp (kummerCoeffToKnrAdd (F := F) p))

/-- **定义相等**：`kummerResidueAdd` 逐点等于 `Hyp473.kummerResidueMap`（`rfl`）。 -/
theorem kummerResidueMap_eq_add
    (x : ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat) :
    kummerResidueMap (K := F) p 0 x = kummerResidueAdd (F := F) p x := rfl

/-! ## 2. 接上维数平移：`∂₂` 的 `ℤ`-系数形态 -/

/-- ★★★★★ **`∂₂` 的 `ℤ`-系数形态**：`H²(G,μ_p) →+ H²(G,ℤ)`。

即 `Hyp481.knrResidueMapInt` 的加性版（`intH2AddEquivH1RatOverZ.symm ∘ ∂₂`）。 -/
noncomputable def kummerResidueInt :
    ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat →+
      ↑(continuousCohomology (0 + 1 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} ℤ))).toModuleCat :=
  ((intH2AddEquivH1RatOverZ (F := F)).symm.toAddMonoidHom).comp
    (kummerResidueAdd (F := F) p)

/-- `kummerResidueInt` 逐点等于 `knrResidueMapInt`。 -/
theorem kummerResidueInt_apply
    (x : ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat) :
    kummerResidueInt (F := F) p x = knrResidueMapInt F p x := rfl

/-- ★★★★★ **`∂₂` 的像落在 `p`-挠内**：`p • ∂₂ x = 0`。

机制：`kummerResidueInt` 加性，而 `H²(ℤ,μ_p)` 是 `p`-挠
（`Hyp485.kummerCoeffH2_nsmul_eq_zero`）。**不需要**任何关于 `∂₂` 的数学内容。 -/
theorem kummerResidueInt_torsion
    (x : ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat) :
    p • kummerResidueInt (F := F) p x = 0 := by
  rw [← AddMonoidHom.map_nsmul]
  rw [kummerCoeffH2_nsmul_eq_zero (F := F) p, AddMonoidHom.map_zero]

/-! ## 3. `∂₂` 的最终加性形态：`H²(ℤ,μ_p) → H¹(ℤ, ℤ/p)` -/

/-- ★★★★★ **`∂₂` 的最终加性形态**：`H²(G,μ_p) →+ H¹(G, ℤ/p)`。

`p`-挠性（上一件）给出 `codRestrict` 到 `ker (nsmulAddMonoidHom p)`，
再用库内件 `TauCeti.integralBocksteinH1Equiv.symm` 把 `p`-挠子群送回 `H¹(G,ℤ/p)`。 -/
noncomputable def kummerResidueH1ZMod :
    ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat →+
      ↑(continuousCohomology (0 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} (ZMod p)))).toModuleCat :=
  (integralBocksteinH1Equiv (G := TauCeti.AbsoluteGaloisGroup F) p).symm.toAddMonoidHom.comp
    ((kummerResidueInt (F := F) p).codRestrict _
      (fun x => by
        show nsmulAddMonoidHom p (kummerResidueInt (F := F) p x) = 0
        simpa using kummerResidueInt_torsion (F := F) p x))

/-- ★★★★ **相容性**：`∂₂` 经 `integralBockstein` 回读即得它在 `H²(ℤ)` 层的样子。 -/
theorem kummerResidueH1ZMod_spec
    (x : ↑(continuousCohomology (0 + 2) (ofDiscreteModule ℤ
      (TauCeti.AbsoluteGaloisGroup F) (KummerCoeff F p))).toModuleCat) :
    integralBockstein (TauCeti.AbsoluteGaloisGroup F) p 1 (kummerResidueH1ZMod (F := F) p x)
      = kummerResidueInt (F := F) p x :=
  TauCeti.integralBocksteinH1Equiv_symm_apply (G := TauCeti.AbsoluteGaloisGroup F) p _

/-! ## 4. 接上 `GaloBase.H2` -/

/-- ★★★★★ **`∂₂` 于 `H²(G_F, μ_p)` 上**：`GaloBase.H2 F p →+ H¹(ℤ, ℤ/p)`。 -/
noncomputable def knrD (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 F p →+
      ↑(continuousCohomology (0 + 1) (ofDiscreteModule ℤ
        (TauCeti.AbsoluteGaloisGroup F) (ULift.{0} (ZMod p)))).toModuleCat :=
  (kummerResidueH1ZMod (F := F) p).comp (kummerH2Bridge F p hpF hζ).toAddMonoidHom

/-- `knrD` 的展开式（供下游核对：`knrD = integralBocksteinH1Equiv⁻¹ ∘ codRestrict ∘ knrResidueMapInt ∘ bridge`）。 -/
theorem knrD_apply (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (x : GaloBase.H2 F p) :
    knrD (F := F) p hpF hζ x
      = kummerResidueH1ZMod (F := F) p ((kummerH2Bridge F p hpF hζ) x) := rfl

end L20261018

#print axioms L20261018.dimShiftAdd
#print axioms L20261018.kummerResidueMap_eq_add
#print axioms L20261018.kummerResidueInt
#print axioms L20261018.kummerResidueInt_apply
#print axioms L20261018.kummerResidueInt_torsion
#print axioms L20261018.kummerResidueH1ZMod
#print axioms L20261018.kummerResidueH1ZMod_spec
#print axioms L20261018.knrD
#print axioms L20261018.knrD_apply
