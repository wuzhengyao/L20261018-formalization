import L20261018.Hyp780
import L20261018.Hyp719

/-!
# S74 R7：`∂²` 的**展开 API** —— 把 `deltaTwoShift` 拆成 `δ⁻¹` ＋ 桥 ＋ `Infl⁻¹`

## 为什么需要这件

路线 A（GS 6.8.4）的证明形态是：**给定 `x ∈ H²(Γ,μ_p)`，显式给出 `z` 使 `δ z = x`，再算 `∂²(x)`。**
要这么写，必须能把 `∂²` 从"四个不透明 `AddEquiv` 的复合"拆成可直接喂 `z` 的形状。

`∂²` 的四个因子（`Hyp719`／`Hyp723`／`Hyp724`）：
```
H²(G,A) --(δ⁻¹)--> H¹(G,C) --(h1BridgeQ)--> H1 G C --(Infl⁻¹)--> H1(G⧸H)(C^H) --(M)--> H1(G⧸H)(H¹(H,A))
```

本件交付**两次往返恒等式**（`δ⁻¹ ∘ δ = id`、`δ ∘ δ⁻¹ = id`）与 `deltaTwoShift` 的**逐点展开**，
使下一轮可以按

```
要证 ∂²(x) = w
⟸ 给出 z : H¹(G,C) 使 (S.delta 1) z = x，且 contM(inflStep(bridge z)) = w
```

来打。**这与 TauCeti 的 `HomologySequence.delta_apply`（`δ` 的余链代表公式
`δ([z₃]) = [d x₂]`，`x₂` 为 `z₃` 的提升）配套**：`delta_apply` 负责"验证 `δ z = x`"，
本件负责"把 `δ z = x` 换成 `∂²(x)`"。**这是路线 A 的准入件。**

## 诚实边界

* 本件**不含** GS 6.8.4 的数学（那需要 `H⁰`-槽的 Leibniz：`δ(x ⌣ y) = δx ⌣ y`，
  `x ∈ H⁰(G,C)`、`y ∈ H¹(G,A)`）；`delta_apply` 已确认存在（本轮侦察），是下一轮的引擎。
* `hB1`／`hB2` 仍是技术输入（`H¹`／`H²(G,B)=0`，余诱导零调性给出）。
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

/-- ★★★★ **`δ⁻¹ ∘ δ = id`**（`deltaShift1` 是 `S.delta 1` 的逆）。 -/
theorem deltaShift1_delta (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))
    (z : continuousCohomology 1 (ofDiscreteModule ℤ G C)) :
    deltaShift1 (C := C) S hB1 hB2 ((S.delta 1).hom z) = z :=
  AddEquiv.symm_apply_apply _ z

/-- ★★★★ **`δ ∘ δ⁻¹ = id`**。 -/
theorem delta_deltaShift1 (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))
    (x : continuousCohomology 2 (ofDiscreteModule ℤ G A)) :
    (S.delta 1).hom (deltaShift1 (C := C) S hB1 hB2 x) = x :=
  show (deltaAddEquiv_of_subsingleton S 1 hB1 hB2)
      (deltaShift1 (C := C) S hB1 hB2 x) = x from
    AddEquiv.apply_symm_apply _ x

/-- ★★★★ **`deltaTwoShift` 的逐点展开**：`∂²` 的前三段就是 `Infl⁻¹ ∘ 桥 ∘ δ⁻¹`。 -/
theorem deltaTwoShift_apply (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))
    [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)]
    (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C)))
    (x : continuousCohomology 2 (ofDiscreteModule ℤ G A)) :
    deltaTwoShift (H := H) (C := C) S hB1 hB2 hC x
      = inflStep (H := H) (C := C) hC
          (h1BridgeQ (C := C) (deltaShift1 (C := C) S hB1 hB2 x)) :=
  rfl

/-- ★★★★★ **路线 A 的攻击形态**：要证 `∂²(x) = w`，只需给出 `z` 使 `δ z = x` 且
`M(Infl⁻¹(桥 z)) = w`。

（把 `x = δ z` 代进去，用 `deltaShift1_delta` 消去 `δ⁻¹ ∘ δ`。） -/
theorem deltaTwoShift_eq_of_delta_eq (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))
    [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)]
    (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C)))
    (z : continuousCohomology 1 (ofDiscreteModule ℤ G C))
    {w : H1 (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)}
    (hw : inflStep (H := H) (C := C) hC (h1BridgeQ (C := C) z) = w) :
    deltaTwoShift (H := H) (C := C) S hB1 hB2 hC ((S.delta 1).hom z) = w := by
  show inflStep (H := H) (C := C) hC
      (h1BridgeQ (C := C) (deltaShift1 (C := C) S hB1 hB2 ((S.delta 1).hom z))) = w
  rw [deltaShift1_delta, hw]

end L20261018

#print axioms L20261018.deltaShift1_delta
#print axioms L20261018.delta_deltaShift1
#print axioms L20261018.deltaTwoShift_apply
#print axioms L20261018.deltaTwoShift_eq_of_delta_eq
