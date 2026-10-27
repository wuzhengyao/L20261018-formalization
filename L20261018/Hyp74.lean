import L20261018.Hyp67
import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CentralSimple.Basic

/-!
# `(3)(ii)` 第一步：交叉积类 = 循环类的膨胀

`TauCeti` 有两条「膨胀」通路，各自通向 Brauer 群的不同模型：

* **交叉积侧**：`BrauerGroup.crossedProductClass z = mk (CSA.of K (CrossedProduct z))`，
  经 `brauerCohomologyEquiv` 送到连续上同调 `H²_cont(G_K, (Kˢ)ˣ)` 的显式模型，
  值是 `z.inflateClass L`（`brauerCohomologyEquiv_crossedProductClass`）；
* **群上同调侧**：`relBrInfl K L ι` 把 `H²(Gal(L/K), Lˣ)` 送到 `Br K`，
  在 `cyclicClass` 上值是 `unitsRepH2Equiv (relBrCocycle …)`（`relBrInfl_H2π`）。

本文件证明这两条通路在 `TwoCocycle` 上**给出同一个类**：

```lean
brauerGroupEquivBr K (ofMul (crossedProductClass z)) = relBrInfl K L L.val (z.cohomologyClass)
```

证明骨架：两侧都等于 `unitsRepH2Equiv K (H2π (显式余环))`，而两个显式余环
（`inflateZ2` 与 `relBrCocycle`）**逐点相同**（`(g,h) ↦ ι (z (g|_L, h|_L))`）。
这是 `TauCeti` 的库级缺口——`relBrInfl` 与 `CrossedProduct` 之间此前没有任何桥。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open TauCeti ContCohomology TauCeti.ClassFieldTheory

namespace SymbolCupBridge

variable {K : Type} [Field K]

/-- **两个膨胀余环逐点相同。**

`TwoCocycle.inflateZ2 L z` 把 `z` 沿 `L ↪ Kˢ` 与 `G_K ↠ Gal(L/K)` 拉回，取值为
`(g,h) ↦ ↑(z (g|_L, h|_L))`；`relBrCocycle K L L.val z.toCocycles₂` 用
`embeddedUnitsEquivInvariants` 表达同一取值——而 `embeddedUnitsInvariants` 的乘法侧正是
`Units.map L.val`，故二者是同一个函数。 -/
theorem inflateZ2_eq_relBrCocycle (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [Normal K L] (z : TwoCocycle K L) :
    TwoCocycle.inflateZ2 L z = relBrCocycle K ↥L L.val z.toCocycles₂ := by
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [TwoCocycle.coe_inflateZ2, TwoCocycle.coe_toCocycles₂]
  beta_reduce
  rw [TwoCocycle.inflate_toFun]
  rw [relBrCocycle_apply]
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [toMul_ofMul, embeddedUnitsEquivInvariants_apply,
    toMul_coe_embeddedUnitsInvariants, Units.coe_map]
  rfl

end SymbolCupBridge

namespace SymbolCupBridge

variable {K : Type} [Field K]

/-- **(A) 交叉积类的 Brauer 群认同。**

两条膨胀通路给出同一个 Brauer 类：`crossedProductClass z` 经 `brauerGroupEquivBr` 的像，
等于 `cyclicClass` 沿 `relBrInfl` 的像（在 `z.cohomologyClass` 处）。

证明：`brauerGroupEquivBr` 把交叉积侧化成 `z.inflateClass L = H2π (z.inflateZ2 L)`；
`relBrInfl` 把循环类侧化成 `H2π (relBrCocycle …)`；两个显式余环逐点相同
（`inflateZ2_eq_relBrCocycle`），于是 `unitsRepH2Equiv` 的像相同。 -/
theorem brauerGroupEquivBr_crossedProductClass (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [IsGalois K L] (z : TwoCocycle K L) :
    ClassFieldTheory.brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.crossedProductClass z))
      = ClassFieldTheory.relBrInfl K ↥L L.val z.cohomologyClass := by
  rw [ClassFieldTheory.brauerGroupEquivBr_apply,
    brauerCohomologyEquiv_crossedProductClass, TwoCocycle.inflateClass_def,
    AddEquiv.symm_apply_apply, TwoCocycle.cohomologyClass_def,
    ClassFieldTheory.relBrInfl_H2π, inflateZ2_eq_relBrCocycle]
  rfl

end SymbolCupBridge

#print axioms SymbolCupBridge.inflateZ2_eq_relBrCocycle

#print axioms SymbolCupBridge.brauerGroupEquivBr_crossedProductClass
