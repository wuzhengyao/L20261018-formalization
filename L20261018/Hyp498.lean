import Hyp497

/-!
# S41 R9（动作 V2f 第四块）：**`δ_0 : C^H → H¹(H,A)` 的显式模型载体**

## 本件在 GS §6.8 的哪一格

GS Construction 6.8.1 的最后一段要

> a map `C^H → H^1(H,A)`, which is a morphism of `G/H`-modules

本件把这条映射的**载体**在**显式模型**里机检到位：

| 声明 | 内容 |
|---|---|
| `h0EquivFixedPoints` | `H0 ↥H C ≃+ C^H`（显式模型的 0 次上同调就是不动点，两边的 `AddSubgroup` 判定只差 `⊤` 与 `H`） |
| **`residueCoeff`** | ★★★★ **`C^H →+ H¹(H,A)`**（= `(S.restrict H).explicitDelta0`，库内 `DiscreteShortExact.explicitDelta0`） |

## ★ 架构发现（本轮，重要）：**必须走显式模型，不能走 `TopRep`**

连续模型里要抬成 `coeffMap` 就得把 `H¹(H,A)` 装成 `TopRep (G⧸H)`，而 `ofDiscreteModule` 要求
**`ContinuousSMul (G ⧸ H) M`**——对离散 `M` 即要求每点**稳定子开**。对
`M = H¹(H, μ_p)`，这需要 `H¹(H,μ_p)` 的**有限性／`G⧸H`-轨道的有限性**，而那正是
`H¹(I,μ_p) ≅ ℤ/p` 的推论（**A.6.9 依赖**）⟹ **连续模型路线是循环的**。

而库内 **`explicitCoeff1 (f : M →+[G] N) (hf : Continuous f) : H1 G M →+ H1 G N`**
只要求**等变加性群**（无 `ContinuousSMul`、无 `TopRep`）⟹ **显式模型路线是唯一无循环的路**。
（注：`explicitCoeff1` 还要 `hf : Continuous f`；对离散 `M`、`N`，加性同态**自动连续**。）

## 诚实边界

* 本件只做**载体**。`δ_0` 的 `G⧸H`-等变性（库内连续模型有
  `DiscreteShortExact.delta_conjNormalMap`，须搬到显式模型）与 `explicitCoeff1` 的装配 —— **下一步**。
* 本件**不**触及 `KnrResidueObligation`。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology CategoryTheory

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : Subgroup G) [H.Normal]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- ★★★★★ **`δ_0 : H⁰(H,C) →+ H¹(H,A)`**（GS 的「`C^H → H^1(H,A)`」，库内 `explicitDelta0`）。

`S.restrict H` 是 `0 → A → B → C → 0` 在 `↥H` 上的限制；它在 0 次的连接映射即
`H⁰(H,C) →+ H¹(H,A)`，而 `H⁰(H,C) = C^H`（显式模型里 `H0` **就是**不动点子群）。 -/
noncomputable def residueCoeff (S : DiscreteShortExact G A B C) :
    ↥(TauCeti.ContCohomology.H0 ↥H C) →+ H1 ↥H A := by
  haveI : ContinuousSMul ↥H A := inferInstance
  exact (S.restrict H).explicitDelta0

end L20261018

#print axioms L20261018.residueCoeff
