import Hyp127

/-!
# 路线 A 的正规形：`KummerBridge.kummerClass` 落成 `muP` 自己的显式 `H¹` 比较

比例性证明的第一步（R971）：把路线 A

    KummerBridge.kummerClass = restrictScalarsIntEquiv muP 1 ∘ explicitH1AddEquivContinuousCohomology G (ZMod p) ∘ explicitCoeff1(e_A)

改写为 **`muP` 载体上的单一比较**

    KummerBridge.kummerClass = (muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete ∘ kummerH1Equiv ∘ kummerMap

这样两侧（路线 A 与路线 B）就**都以 `·.explicitH1AddEquivContinuousCohomologyOfDiscrete` 收尾**，
群／系数的搬运全部下沉到显式 `H¹` 层，可用 `explicitCoeff1`／`explicitMap1` 的函子性逐段对齐。

关键事实：`TopRep.ofDiscreteModule ℤ G X.V` 与 `TopRep.restrictScalarsInt.obj X` **定义相等**
（故 `ofDiscreteModuleRestrictScalarsIntEquiv` 里的 `eqToHom` 在元素上是恒等，最后一步是 `rfl`）——
这是 `ContCohomology/RestrictScalars.lean:662` 的直接推论。
-/

set_option maxHeartbeats 2000000

open TauCeti ContCohomology ValuativeRel IsLocalRing IsNonarchimedeanLocalField

-- `muP` 的作用来自 `TopRep.ρ`；`TopRep.distribMulAction` 是 TauCeti 惯用的局部实例
-- （`MuNRep.lean` / `CohomologyComparison.lean` 同款）。
attribute [local instance] TopRep.distribMulAction

namespace L20261018

section Minimal

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]

/-- **`muP` 的 `ContinuousSMul`**：`muP` 的作用是平凡的（`GaloBase.muP_ρ` 由 `rfl` 证），
故 `fun q : G × muP.V ↦ q.1 • q.2` **定义上就是** `Prod.snd`。手法同
`ContCohomology/Bockstein/Basic.lean:83`（`muP` 的定义用 `letI` 局部引入实例，实例搜索不展开，
故必须在此补一条；`Hyp45` 只补了 `DiscreteTopology`，没补这条）。 -/
instance instContinuousSMulMuP :
    ContinuousSMul (TauCeti.AbsoluteGaloisGroup F) (GaloBase.muP F p).V :=
  ⟨continuous_snd⟩

/-- **路线 A 的正规形（关键引理）**：`muP` 的 `OfDiscrete` 比较 = `restrictScalarsIntEquiv` ∘ 显式比较。

三步：展开 `OfDiscrete` 的定义（`_apply`）、展开 `ofDiscreteModuleRestrictScalarsIntEquiv`
（`_apply`，暴露出一个 `eqToHom`）、再 `rfl`（该 `eqToHom` 在元素上是恒等）。 -/
theorem muP_explicitH1_eq_restrictScalars
    (x : H1 (TauCeti.AbsoluteGaloisGroup F) (GaloBase.muP F p).V) :
    (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x
      = TauCeti.ContCohomology.restrictScalarsIntEquiv (GaloBase.muP F p) 1
          (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
            (TauCeti.AbsoluteGaloisGroup F) (GaloBase.muP F p).V x) := by
  rw [TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
    TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv_apply]
  rfl

/-- **`h1ToVEquiv` 的正规形**：它就是把显式 `H¹` 类送进 `muP` 的典范比较。 -/
theorem h1ToVEquiv_apply_eq_muP (x : H1 (TauCeti.AbsoluteGaloisGroup F) (ZMod p)) :
    KummerBridge.h1ToVEquiv F p x
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete x := by
  show TauCeti.ContCohomology.restrictScalarsIntEquiv (GaloBase.muP F p) 1
      (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
        (TauCeti.AbsoluteGaloisGroup F) (ZMod p) x) = _
  exact (muP_explicitH1_eq_restrictScalars (F := F) p x).symm

/-- **路线 A 正规形（论文层）**：`KummerBridge.kummerClass` ＝
`muP` 的 `OfDiscrete` 比较 ∘ `kummerH1Equiv`。

这是比例性证明的起点：右端只剩**一个**载体比较，
故路线 B 侧只要也化到 `muP.EH1OfDiscrete ∘ (显式系数映射)`，比较就落到显式 `H¹` 层。 -/
theorem kummerClass_eq_muP_explicitH1 (hp : IsUnit (p : F)) (a : Fˣ) :
    KummerBridge.kummerClass F p hp a
      = (GaloBase.muP F p).explicitH1AddEquivContinuousCohomologyOfDiscrete
          ((KummerBridge.kummerH1Equiv F p hp) ((TauCeti.kummerMap F p hp a).toAdd)) := by
  rw [KummerBridge.kummerClass, h1ToVEquiv_apply_eq_muP]


#print axioms L20261018.muP_explicitH1_eq_restrictScalars
#print axioms L20261018.h1ToVEquiv_apply_eq_muP
#print axioms L20261018.kummerClass_eq_muP_explicitH1

end Minimal
