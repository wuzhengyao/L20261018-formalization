import L20261018.Hyp203

/-!
# R1060（**载体桥基建 2**）：`map`（群＋系数）与「限制纯量」交换

`Hyp203` 处理的是**纯系数**情形（同一群）。`hbridge` 的五段链里 `gE` 是**群同构**诱导的映射，
需要它的对应自然性：`TauCeti` 的 `ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom`
（`RestrictScalars.lean:556`）：

```
map phi (resRestrictScalarsIntMap phi f) n ≫ (restrictScalarsIntIso Y n).hom
  = (restrictScalarsIntIso X n).hom ≫ TopModuleCat.restrictScalarsInt.map (map phi f n)
```

本文件把它降到元素级（同 `Hyp203` 的手法）：

| 声明 | 内容 |
|---|---|
| **`map_restrictScalarsIntEquiv_comm`** | `RS Y (map phi (resRS.map phi f) y) = map phi f (RS X y)` |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

section CommMap

variable {p : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **`map` 与限制纯量交换**（元素级）：把 `RS` 从 `map` 的右边搬到左边。 -/
theorem map_restrictScalarsIntEquiv_comm {X : TopRep (ZMod p) G} {Y : TopRep (ZMod p) H}
    [DiscreteTopology X.V] [DiscreteTopology Y.V]
    (phi : H →ₜ* G) (f : TopRep.res (phi : H →* G) X ⟶ Y) (n : ℕ)
    (y : ↑(continuousCohomology n (TopRep.restrictScalarsInt.obj X)).toModuleCat) :
    ContCohomology.restrictScalarsIntEquiv Y n
        ((ContinuousCohomology.map phi (TopRep.resRestrictScalarsIntMap (phi : H →* G) f) n).hom y)
      = (ContinuousCohomology.map phi f n).hom
          (ContCohomology.restrictScalarsIntEquiv X n y) := by
  have h := ContCohomology.map_comp_restrictScalarsIntIso_hom_of_hom (phi := phi) (f := f) (n := n)
  have h2 := congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g) y) h
  simp only [CategoryTheory.comp_apply] at h2
  rw [ContCohomology.restrictScalarsIntEquiv_apply, ContCohomology.restrictScalarsIntEquiv_apply]
  rw [h2]
  rfl

end CommMap

end L20261018

#print axioms L20261018.map_restrictScalarsIntEquiv_comm
