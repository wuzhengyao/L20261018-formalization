import L20261018.Hyp202

/-!
# R1059（**载体桥 `hbridge` 的第一块基建**）：`coeffMap` 与「限制纯量」交换

`hbridge`（`Hyp164`／`Hyp201`／`Hyp202` 的唯一残余）要把
`redEquiv1 ∘ KummerBridge.kummerClass` 与 `ClassFieldTheory.kummerClass` 两边
各五段的载体链折叠成同一个复合。其中一段是：

```
coeffMap (GaloTrivialFp.iso.inv)  ∘  restrictScalarsIntEquiv (muP)      -- ZMod p 系数 → trivialFp
```

而 `TauCeti` 已给出**范畴级**的自然性（`ContCohomology.coeffMap_comp_restrictScalarsIntIso_hom`）：

```
coeffMap (restrictScalarsInt.map f) n ≫ (restrictScalarsIntIso Y n).hom
  = (restrictScalarsIntIso X n).hom ≫ TopModuleCat.restrictScalarsInt.map (coeffMap f n)
```

本文件把它**降到元素级**并用 `restrictScalarsIntEquiv_apply` 换成战役侧用的 `≃+` 形式：

| 声明 | 内容 |
|---|---|
| **`coeffMap_restrictScalarsIntEquiv_comm`** | `RS Y (coeffMap (RS.map f) y) = coeffMap f (RS X y)` |

> 右端的 `TopModuleCat.restrictScalarsInt.map (coeffMap f n)`（纯量忘却）在元素上是恒等
> ⟹ 元素级等式成立（`rfl` 收尾）。这条正是 `PLAN-HBRIDGE.md` §6.3 的 **(★)** 的一半。
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section CommCoeffMap

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- **`coeffMap` 与限制纯量交换**（元素级）：把 `RS` 从 `coeffMap` 的右边搬到左边。 -/
theorem coeffMap_restrictScalarsIntEquiv_comm
    (X Y : TopRep (ZMod p) (AbsoluteGaloisGroup F)) [DiscreteTopology X.V] [DiscreteTopology Y.V]
    (f : X ⟶ Y) (n : ℕ)
    (y : ↑(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat) :
    ContCohomology.restrictScalarsIntEquiv Y n
        ((ContinuousCohomology.coeffMap (TopRep.restrictScalarsInt.map f) n).hom y)
      = (ContinuousCohomology.coeffMap f n).hom
          (ContCohomology.restrictScalarsIntEquiv X n y) := by
  have h := ContCohomology.coeffMap_comp_restrictScalarsIntIso_hom (X := X) (Y := Y) (f := f) (n := n)
  have h2 := congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g) y) h
  simp only [CategoryTheory.comp_apply] at h2
  rw [ContCohomology.restrictScalarsIntEquiv_apply, ContCohomology.restrictScalarsIntEquiv_apply]
  rw [h2]
  rfl

end CommCoeffMap

end L20261018

#print axioms L20261018.coeffMap_restrictScalarsIntEquiv_comm
