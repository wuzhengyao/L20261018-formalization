import L20261018.Hyp220

/-!
# R1090（**T1 第五归约：模型比对 —— 两侧都写成 `muP.OfDiscrete ∘ explicitMap1`**）

## 库内侦察（内容式，`L46`／`L47`）

| 关键词 | 命中 | 结论 |
|---|---|---|
| `explicitH1AddEquivContinuousCohomologyOfDiscrete` × `coeffMap` | `Coefficients/FilteredColimits.lean:116–130` | ★ **库内已有该自然性的「用法」**（`NatIso` 的一个分量证明），但**未抽成具名引理** |
| `coeffMap_def` | `Functoriality.lean:218` | `coeffMap f n = map (id G) f n`（`rfl`）—— 把 `coeffMap` 接到 `_map` 自然性引理的入口 |
| `ofDiscreteModuleRestrictScalarsIntEquiv_apply` | `RestrictScalars.lean:665` | `OfDiscrete = ofDiscreteModuleRestrictScalarsIntEquiv ∘ explicitH1AddEquivContinuousCohomology` |

## 本轮结论

战役侧原本是 `h1ToVEquiv = (explicit 比较) ≻ (RS)`，绕开 `OfDiscrete`；但库内
`OfDiscrete = ofDiscreteModuleRestrictScalarsIntEquiv ∘ explicitH1AddEquivContinuousCohomology`，
而 `ofDiscreteModuleRestrictScalarsIntEquiv` 正是「`RS` ＋ 一次 `eqToHom` 搬运」⟹

```
h1ToVEquiv = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
```

于是**两侧同为「`X.OfDiscrete ∘ explicitMap1 id (系数映射)`」**：

| 侧 | `X` | 系数映射 |
|---|---|---|
| 战役侧 | `muP` | `e_c`（`kummerCoeffLinearEquiv`，任意选基） |
| `bridgeKc` 侧 | `muP`（经 `coeffMap (GaloTrivialFp.iso).hom` 从 `trivialFp` 换模型） | `iso∘μ`（ζ-典范） |

⟹ **T1 只剩一维标量**（`Hyp206` ＋ `Hyp218.explicitMap1_eq_nsmul` ＋ `OfDiscrete` 的加法性）。

| 声明 | 内容 |
|---|---|
| **`coeffMap_ofDiscrete`** | ★ 库内缺的具名引理：`coeffMap F 1 (X.OfDiscrete x) = Y.OfDiscrete (explicitCoeff1 f x)` |
| **`h1ToVEquiv_eq_muP`** | 战役侧的比较就是 `muP.OfDiscrete` |
| **`kummerClass_eq_muP`** | 战役侧最终形态：`kummerClass a = muP.OfDiscrete (explicitMap1 id e_c (kummerMap a))` |
| **`kummerClass_eq_muP`** | 战役侧最终形态：`kummerClass a = muP.OfDiscrete (explicitMap1 id e_c (kummerMap a))` |

**下一轮（`Hyp222`）**：`bridgeKc` 侧同形 ——
`bridgeKc a = muP.OfDiscrete (explicitMap1 id (iso∘μ) (kummerMap a))`（用 `coeffMap_ofDiscrete` 于
`F := (GaloTrivialFp.iso F p).hom`、`X := trivialFp p G_a`、`Y := muP`，＋ `explicitMap1_comp` 合并 `iso∘μ`）。
⟹ 两侧同为 `muP.OfDiscrete ∘ explicitMap1 id (系数映射)`，⟹ T1 只剩一维标量。
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

/-! ### 1. 库内缺的具名引理：`coeffMap` 对 `OfDiscrete` 的自然性 -/

section CoeffNat

variable {R : Type} [Ring R] [TopologicalSpace R]
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] TopRep.distribMulAction

/-- ★ **`coeffMap` 对 `OfDiscrete` 的自然性**（库内只有用法、无具名引理）：
`coeffMap F 1 (X.OfDiscrete x) = Y.OfDiscrete (explicitCoeff1 f x)`，其中 `f` 是 `F.hom` 的底层加法映射。 -/
theorem coeffMap_ofDiscrete {X : TopRep R G} [DiscreteTopology X.V] [ContinuousSMul G X.V]
    {Y : TopRep R G} [DiscreteTopology Y.V] [ContinuousSMul G Y.V]
    (F : X ⟶ Y) (f : X.V →+[G] Y.V)
    (hF : ∀ m, F.hom m = f m) (x : H1 G X.V) :
    ContinuousCohomology.coeffMap F 1 (X.explicitH1AddEquivContinuousCohomologyOfDiscrete x)
      = Y.explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitCoeff1 G X.V f continuous_of_discreteTopology x) := by
  rw [explicitCoeff1_eq_explicitMap1, ContinuousCohomology.coeffMap_def]
  exact X.explicitH1AddEquivContinuousCohomologyOfDiscrete_map Y
    (ContinuousMonoidHom.id G) F f.toAddMonoidHom hF (map_smul f) x

end CoeffNat

/-! ### 2. 战役侧的比较就是 `muP.OfDiscrete` -/

section Campaign

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity F p]
variable {ζ : F}

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- **战役侧的 `h1ToVEquiv` 就是 `muP.OfDiscrete`**（`OfDiscrete` 的定义展开 ＋ `eqToHom` 不改取值）。 -/
theorem h1ToVEquiv_eq_muP :
    KummerBridge.h1ToVEquiv F p
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete := by
  refine AddEquiv.ext fun x => ?_
  show restrictScalarsIntEquiv (G := AbsoluteGaloisGroup F) (GaloBase.muP F p) 1
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (ZMod p) x)
    = ofDiscreteModuleRestrictScalarsIntEquiv (GaloBase.muP F p) 1
      (explicitH1AddEquivContinuousCohomology (AbsoluteGaloisGroup F) (GaloBase.muP F p).V x)
  rw [ofDiscreteModuleRestrictScalarsIntEquiv_apply]
  rfl

/-- **战役侧最终形态**：`kummerClass a = muP.OfDiscrete (explicitMap1 id e_c (kummerMap a))`。 -/
theorem kummerClass_eq_muP (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
          (explicitMap1 (AbsoluteGaloisGroup F) (KummerCoeff F p)
            (AbsoluteGaloisGroup F) (ZMod p)
            (ContinuousMonoidHom.id (AbsoluteGaloisGroup F))
            (eCoeffHom (F := F) p hp) continuous_of_discreteTopology
            (fun g m => (eCoeffHom (F := F) p hp).map_smul g m)
            (TauCeti.kummerMap F p hp a).toAdd) := by
  rw [kummerClass_eq_thetaOne (F := F) (p := p) hp a, h1ToVEquiv_eq_muP]
  rfl

end Campaign

end L20261018

#print axioms L20261018.coeffMap_ofDiscrete
#print axioms L20261018.h1ToVEquiv_eq_muP
#print axioms L20261018.kummerClass_eq_muP
