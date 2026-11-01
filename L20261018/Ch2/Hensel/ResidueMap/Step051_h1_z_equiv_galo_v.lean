import L20261018.Ch2.Hensel.ResidueMap.Step050_delta_two_additive

/-!
# S41 R1（续）：动作 A4b-2 第二段 —— **系数桥 `H¹(ℤ, ℤ/p) ≃+ GaloBase.V`** 与**约化**

`Hyp487.knrD : GaloBase.H2 F p →+ H¹(ℤ, ULift (ZMod p))`。本轮把值域接到 `GaloBase.V`：

```
H¹(ℤ, ULift (ZMod p))
  --ofDiscreteModuleIso (AddEquiv.ulift)-->  H¹(ℤ, ZMod p)
  --ofDiscreteModuleRestrictScalarsIntEquiv--> H¹(ZMod p, ZMod p)   （"cohomology does not see the scalars"）
  --ofDiscreteModuleIso (muLinearEquiv)-->     H¹(ZMod p, μ_p(F)) = H¹(muPReal)
  --muCohomologyIso-->                          H¹(G_F, muP) = GaloBase.V
```

## 侦察命中（规则 24 ④）

**`ofDiscreteModuleRestrictScalarsIntEquiv`**（TauCeti `ContCohomology/RestrictScalars.lean`）是
**全次数**的「上同调不看见纯量」件：

```lean
ofDiscreteModuleRestrictScalarsIntEquiv (X : TopRep k G) [DiscreteTopology ↑X] (n : ℕ) :
  H^n(ofDiscreteModule ℤ G ↥X) ≃+ H^n(X)
```

⟹ 不需要自建任何 `ULift`／纯量比较件；四段全是库内 `ofDiscreteModuleIso` ＋ `mapIso`。

## 本轮的核心交付（说清楚本轮的**性质变化**）

`Hyp479.KnrResidueObligation` 是 **`∃ d`**（存在性命题）。本文件给出一个**显式构造**的

```lean
dPartialLin : GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p
```

（就是 `∂₂` 经四段系数桥的运输），并证明

```lean
KnrResidueReduced ⟹ KnrResidueObligation
```

其中 `KnrResidueReduced` 是**关于这条显式 `d` 的三条具体陈述**：

1. `∀ x, v̄ (d x) = 0`（落在 `ker v̄ = VKG` 内 —— 动作 A5）；
2. `∀ y z : VKG, d (y ⌣ z) = 0`（③b）；
3. `∀ y : VKG, d (y ⌣ (π)) = y`（③c）。

⟹ **义务从「存在一个 `d`」变成「这三条对这条具体的 `d` 成立」**。这是 S41 的动作 A4b-2 的终点；
1–3 是 GS `prop-units-cohomology` 的实算，见 `S41-STATUS.md` 的诚实分诊。

## 机检件

| 声明 | 内容 |
|---|---|
| `uliftZModCoeffIso` | `H¹(ℤ, ULift (ZMod p)) ≅ H¹(ℤ, ZMod p)` |
| `restrictScalarsH1` | `H¹(ℤ, ZMod p) ≃+ H¹(ZMod p, ZMod p)`（库内件直用） |
| `muPCoeffIso` | `H¹(ZMod p, ZMod p) ≅ H¹(ZMod p, μ_p(F))` |
| **`h1ZModBridge`** | ★★★★★ **`H¹(ℤ, ULift (ZMod p)) ≃+ GaloBase.V F p`**（四段打包） |
| **`dPartial`／`dPartialLin`** | ★★★★★ **显式的 `∂₂ : H²(F,μ_p) → V`** |
| **`KnrResidueReduced`** | ★★★★★ 义务的**显式化**形式（三条关于 `dPartialLin` 的陈述） |
| **`knrResidueObligation_of_reduced`** | ★★★★★ **`KnrResidueReduced ⟹ KnrResidueObligation`** |
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

/-- `G` 在 `ZMod p` 上的平凡作用。 -/
local instance zmodTrivialAction' : DistribMulAction (TauCeti.AbsoluteGaloisGroup F) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- `G` 在 `ULift (ZMod p)` 上的平凡作用。 -/
local instance uliftZModTrivialAction' : DistribMulAction (TauCeti.AbsoluteGaloisGroup F)
    (ULift.{0} (ZMod p)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用连续（离散）。 -/
local instance uliftZModContinuousSMul' : ContinuousSMul (TauCeti.AbsoluteGaloisGroup F)
    (ULift.{0} (ZMod p)) := ⟨continuous_snd⟩

/-! ## 1. 四段系数桥 -/

/-- 第一段：`ULift (ZMod p)` 与 `ZMod p` 的系数比较（两侧作用均平凡）。 -/
noncomputable def uliftZModCoeffIso :
    continuousCohomology 1 (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (ULift.{0} (ZMod p))) ≅
      continuousCohomology 1 (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :=
  (TauCeti.ContinuousCohomology.continuousCohomologyFunctor ℤ
      (TauCeti.AbsoluteGaloisGroup F) 1).mapIso
    (TauCeti.ofDiscreteModuleIso (AddEquiv.toIntLinearEquiv AddEquiv.ulift)
      (fun _ _ => rfl))

/-- 第二段：**上同调不看见纯量**（TauCeti 库内件，全次数）。

`H¹(ℤ, ofDiscreteModule ℤ G (ZMod p)) ≃+ H¹(ZMod p, ofDiscreteModule (ZMod p) G (ZMod p))`。 -/
noncomputable def restrictScalarsH1 :
    ↑(continuousCohomology 1 (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (ZMod p))).toModuleCat ≃+
      ↑(continuousCohomology 1 (ofDiscreteModule (ZMod p) (TauCeti.AbsoluteGaloisGroup F)
        (ZMod p))).toModuleCat :=
  TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
    (ofDiscreteModule (ZMod p) (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) 1

/-- 第三段：`ZMod p ≅ μ_p(F)`（`Hyp382.muLinearEquiv`；两侧作用均平凡）。 -/
noncomputable def muPCoeffIso {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    continuousCohomology 1 (ofDiscreteModule (ZMod p) (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) ≅
      continuousCohomology 1 (muPReal p F) :=
  (TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod p)
      (TauCeti.AbsoluteGaloisGroup F) 1).mapIso
    (TauCeti.ofDiscreteModuleIso (muLinearEquiv p F hζ) (fun _ _ => rfl))

/-- ★★★★★ **四段打包**：`H¹(ℤ, ℤ/p) ≃+ GaloBase.V F p`。

```
H¹(ℤ, ULift (ZMod p)) ≅ H¹(ℤ, ZMod p) ≃+ H¹(ZMod p, ZMod p)
  ≅ H¹(ZMod p, μ_p(F)) ≅ H¹(G_F, muP) = GaloBase.V
``` -/
noncomputable def h1ZModBridge {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    ↑(continuousCohomology 1 (ofDiscreteModule ℤ (TauCeti.AbsoluteGaloisGroup F)
        (ULift.{0} (ZMod p)))).toModuleCat ≃+ GaloBase.V F p :=
  (uliftZModCoeffIso (F := F) p).toContinuousLinearEquiv.toAddEquiv.trans
    ((restrictScalarsH1 (F := F) p).trans
      ((muPCoeffIso (F := F) p hζ).toContinuousLinearEquiv.toAddEquiv.trans
        (muCohomologyIso p F hζ 1).toContinuousLinearEquiv.toAddEquiv))

/-! ## 2. 显式的 `∂₂ : H²(F,μ_p) → V` -/

/-- ★★★★★ **显式的 `∂₂`**：`GaloBase.H2 F p →+ GaloBase.V F p`。

= `h1ZModBridge ∘ knrD` = `（四段系数桥）∘ integralBocksteinH1Equiv⁻¹ ∘ codRestrict ∘ ∂₂ ∘ kummerH2Bridge`。 -/
noncomputable def dPartial (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 F p →+ GaloBase.V F p :=
  (h1ZModBridge (F := F) p hζ).toAddMonoidHom.comp (knrD (F := F) p hpF hζ)

/-- ★★★★★ **显式的 `∂₂`（`ZMod p`-线性）**：`GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p`。

升级用库内 `AddMonoidHom.toZModLinearMap`（任何两个 `ZMod n`-模之间的加性映射都是
`ZMod n`-线性的，`Mathlib/Algebra/Module/ZMod.lean:81`）。 -/
noncomputable def dPartialLin (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    GaloBase.H2 F p →ₗ[ZMod p] GaloBase.V F p :=
  (dPartial (F := F) p hpF hζ).toZModLinearMap p

/-- `dPartialLin` 与 `dPartial` 的取值一致（`toZModLinearMap` 的 `coe`）。 -/
theorem dPartialLin_apply (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (x : GaloBase.H2 F p) :
    dPartialLin (F := F) p hpF hζ x = dPartial (F := F) p hpF hζ x := rfl

/-! ## 3. 义务的显式化 -/

variable (v : Fˣ →* Multiplicative ℤ) (π : Fˣ)

/-- ★★★★★ **义务的显式化**：**关于构造出的 `dPartialLin` 的三条具体陈述**。

1. 像落在 `ker v̄ = VKG` 内（动作 A5）；
2. ③b：`d (y ⌣ z) = 0`；
3. ③c：`d (y ⌣ (π)) = y`。 -/
def KnrResidueReduced (hpF : IsUnit (p : F)) {ζ : F} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  (∀ x : GaloBase.H2 F p,
      valLinOf (F := F) (p := p) v hpF (dPartialLin (F := F) p hpF hζ x) = 0) ∧
    (∀ y z : VKG F p v hpF,
      dPartialLin (F := F) p hpF hζ
        (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p) (z : GaloBase.V F p)) = 0) ∧
    (∀ y : VKG F p v hpF,
      dPartialLin (F := F) p hpF hζ
        (GaloBase.cup (K := F) (p := p) (y : GaloBase.V F p)
          (KummerBridge.kummerClass F p hpF π)) = (y : GaloBase.V F p))

/-- ★★★★★ **`KnrResidueReduced ⟹ KnrResidueObligation`**（动作 A4b-2 的终点）。

`d` 取 `dPartialLin` 沿 `LinearMap.ker (valLinOf …) = VKG` 的 `codRestrict`；
两条杯积公式由 `KnrResidueReduced` 的 2、3 逐字给出（`Subtype.ext`）。

⟹ **`Hyp479` 的存在性义务被消掉**，只剩三条关于**这条显式 `d`** 的陈述。 -/
-- @source file=raw/L20261018.tex locator=line:1050 quote="\partial_2((u)\cup(\pi))=(\bar u)"
theorem knrResidueObligation_of_reduced (hpF : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : KnrResidueReduced (F := F) p v π hpF hζ) :
    KnrResidueObligation F p v π hpF := by
  obtain ⟨himg, hb, hc⟩ := h
  refine ⟨(dPartialLin (F := F) p hpF hζ).codRestrict
    (LinearMap.ker (valLinOf (F := F) (p := p) v hpF)) himg, ?_, ?_⟩
  · intro y z
    apply Subtype.ext
    exact hb y z
  · intro y
    apply Subtype.ext
    exact hc y

/-- 反向的**忠实性**读数：`KnrResidueReduced` 是关于 `dPartialLin` 的陈述，故它**严格强于**
`KnrResidueObligation`（后者只要求某个 `d` 存在）。本件把这一点记成一句可核对的注：
若 `KnrResidueReduced` 成立，则 `KnrResidueObligation` 成立（上一件），反之不然。 -/
theorem knrResidueObligation_of_reduced_apply (hpF : IsUnit (p : F)) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (h : KnrResidueReduced (F := F) p v π hpF hζ) :
    Ch4TameSymbolHyp (F := F) p (v := v) (π := π) hpF :=
  ch4TameSymbolHyp_of_obligation (F := F) p (v := v) (π := π) hpF
    (knrResidueObligation_of_reduced (F := F) p (v := v) (π := π) hpF hζ h)

end L20261018

#print axioms L20261018.uliftZModCoeffIso
#print axioms L20261018.restrictScalarsH1
#print axioms L20261018.muPCoeffIso
#print axioms L20261018.h1ZModBridge
#print axioms L20261018.dPartial
#print axioms L20261018.dPartialLin
#print axioms L20261018.dPartialLin_apply
#print axioms L20261018.knrResidueObligation_of_reduced
#print axioms L20261018.knrResidueObligation_of_reduced_apply
