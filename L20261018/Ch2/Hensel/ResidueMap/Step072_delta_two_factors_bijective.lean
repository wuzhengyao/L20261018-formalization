import L20261018.Ch2.Hensel.ResidueMap.Step071_delta_two_expansion

/-!
# S74 R8：`∂²` 三段因子的双射性 API（`Hyp781` 的补全）

## 为什么

`Hyp781` 给了「要证 `∂²(x) = w`，只需给出 `z` 使 `δ z = x` 且 `inflStep(h1BridgeQ z) = w`」。
反向（"`∂²` 的取值唯一决定 `z`"）也需要写成可用的引理：`deltaShift1`／`deltaTwoShift` 都是
`AddEquiv`，故**单射＋满射**；这两条让"`∂²(x)` 由 `δ⁻¹x` 唯一决定"可以直接引用，
而不必在证明里再展开 `deltaTwoShift` 的四段复合。

## 交付

| 声明 | 内容 |
|---|---|
| `deltaShift1_injective`／`_surjective` | `δ⁻¹ : H²(G,A) → H¹(G,C)` 双射 |
| `deltaTwoShift_injective`／`_surjective` | `∂²` 前三段 `H²(G,A) → H¹(G⧸H)(C^H)` 双射 |
| **`deltaTwoShift_eq_iff`** | ★ `∂²前三段(x) = w ↔ Infl⁻¹(桥(δ⁻¹x)) = w`（把"等于"完全化为 `δ⁻¹` 的取值） |

## 诚实边界

本件**仍是 API**，不含 GS 6.8.4 的数学。R8 的数学目标（连续模型的 Leibniz
`δ₁(Inf z₀ ⌣ Inf a) = δ₀(Inf z₀) ⌣ Inf a`）**本轮未动工**——见 `GAP3-PLAN.md` §11.3 的精确打法。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

open TauCeti ContCohomology CategoryTheory
open TauCeti.ContCohomology

namespace L20261018

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SeparatelyContinuousMul G] [TotallyDisconnectedSpace G]
variable (H : Subgroup G) [H.Normal] [IsClosed (H : Set G)]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]

section API

variable (S : DiscreteShortExact G A B C)
variable (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
variable (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))

/-- `δ⁻¹` 单射（`deltaShift1` 是 `AddEquiv`）。 -/
theorem deltaShift1_injective :
    Function.Injective (deltaShift1 (C := C) S hB1 hB2) :=
  (deltaShift1 (C := C) S hB1 hB2).injective

/-- `δ⁻¹` 满射。 -/
theorem deltaShift1_surjective :
    Function.Surjective (deltaShift1 (C := C) S hB1 hB2) :=
  (deltaShift1 (C := C) S hB1 hB2).surjective

variable [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)]
variable (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C)))

/-- `∂²` 前三段单射。 -/
theorem deltaTwoShift_injective :
    Function.Injective (deltaTwoShift (H := H) (C := C) S hB1 hB2 hC) :=
  (deltaTwoShift (H := H) (C := C) S hB1 hB2 hC).injective

/-- `∂²` 前三段满射。 -/
theorem deltaTwoShift_surjective :
    Function.Surjective (deltaTwoShift (H := H) (C := C) S hB1 hB2 hC) :=
  (deltaTwoShift (H := H) (C := C) S hB1 hB2 hC).surjective

/-- ★★★ **`∂²` 前三段的值完全由 `δ⁻¹` 的取值决定**：把"等于 `w`"拆成可喂 `z` 的形状。 -/
theorem deltaTwoShift_eq_iff (x : continuousCohomology 2 (ofDiscreteModule ℤ G A))
    (w : H1 (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)) :
    deltaTwoShift (H := H) (C := C) S hB1 hB2 hC x = w ↔
      inflStep (H := H) (C := C) hC
        (h1BridgeQ (C := C) (deltaShift1 (C := C) S hB1 hB2 x)) = w :=
  Iff.rfl

end API

end L20261018

#print axioms L20261018.deltaShift1_injective
#print axioms L20261018.deltaShift1_surjective
#print axioms L20261018.deltaTwoShift_injective
#print axioms L20261018.deltaTwoShift_surjective
#print axioms L20261018.deltaTwoShift_eq_iff
