import L20261018.Infra.Cohomology.Coinduced.Step007_delta_zero_quotient_morphism
import L20261018.Infra.Cohomology.Coinduced.Step006_inf_h1_iso_closed_subgroup

/-!
# S64 R7：**`∂²` 的前两因子已装配** —— `H²(G,A) ≃+ H¹(G⧸H, C^H)`

GS 6.8.1 的 `∂²` 由三个因子组成：

```
H²(G,A) --(6.15 维数平移)--> H¹(G,C) --(Infl，C 步后为同构)--> H¹(G⧸H, C^H) --(系数映射 M)--> H¹(G⧸H, H¹(H,A))
```

本件装配**前两个**（第三个 ＝ `C2-F` 的 `M`，其 `G⧸H`-等变本体已在 `Hyp718` 机检）。

| 声明 | 内容 |
|---|---|
| `deltaShift1` | `H²(G,A) ≃+ H¹(G,C)`（GS (6.15) 的 `n = 1`，`Hyp492` ＋ 余诱导两度零调） |
| `h1BridgeQ` | `H¹(G,C) ≃+ H1 G C`（库内比较 `explicitH1AddEquivContinuousCohomology`） |
| `inflStep` | `H1 G C ≃+ H1 (G⧸H) (C^H)`（`Hyp717` 反向；输入 `H¹(H,C)=0`） |
| **`deltaTwoShift`**（曾名 `deltaTwo`，因与 `Hyp239` 同名件冲突而改名，R11） | ★★★★★ 三者复合：`H²(G,A) ≃+ H1 (G⧸H) (C^H)`（**对任意离散短正合列 `S`**） |

**抽象 `C` 而非直接写 `Q`**：`Q` 的展开使 `FixedPoints.addSubgroup ↥H (Q …)` 的 `whnf` 代价极高
（实测 `maxHeartbeats 4e7` 仍超时）⟹ 先证一般形态；`Q` 版由下游以 `S = coindShortExact` 实例化。

## 导入说明（R6 已解决的冲突）

本件同时 import `Hyp718`（显式模型族）与 `Hyp717`（B 步族）。两族原先各自定义了
`L20261018.coindShortExact`／`L20261018.explicitInfl1AddEquiv_of_subsingleton`，**无法共存**；
R6 已分别改名为 `coindShortExactCoker`（`Hyp493`）与 `infl1AddEquiv_of_H1_subsingleton`（`Hyp717`）。
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
variable (H : Subgroup G) [H.Normal]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable {B : Type} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
variable {C : Type} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C] [ContinuousSMul G C]

section Closed

variable [IsClosed (H : Set G)]

instance : CompactSpace ↥H := isCompact_iff_compactSpace.mp ‹IsClosed (H : Set G)›.isCompact

/-- ★★★★ **`∂²` 因子一**（GS (6.15) 在 `n = 1`）：`H²(G,A) ≃+ H¹(G,C)`。 -/
noncomputable def deltaShift1 (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B))) :
    continuousCohomology 2 (ofDiscreteModule ℤ G A) ≃+
      continuousCohomology 1 (ofDiscreteModule ℤ G C) :=
  (deltaAddEquiv_of_subsingleton S 1 hB1 hB2).symm

/-- ★★★★ **`∂²` 因子二**：显式模型 ↔ 连续模型的桥（库内比较定理）。 -/
noncomputable def h1BridgeQ :
    continuousCohomology 1 (ofDiscreteModule ℤ G C) ≃+ H1 G C :=
  (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G C).symm

/-- ★★★★ **`∂²` 因子三**（C2-D 反向）：`H1 G C ≃+ H1 (G⧸H) (C^H)`，输入只有 `H¹(H,C) = 0`。 -/
noncomputable def inflStep (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C))) :
    H1 G C ≃+ H1 (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C) :=
  (infl1AddEquiv_of_coindAcyclic (N := H) (M := C) hC).symm

/-- ★★★★★ **4d 第 4 步（消去格）★ 定义级**：`inflStep` 是 `explicitInfl1` 的左逆。

`infl1AddEquiv_of_H1_subsingleton`（`Hyp717:79`）以 `AddEquiv.ofBijective (explicitInfl1 …)` 定义，
故 `inflStep hC (explicitInfl1 z) = z` 就是 `AddEquiv.symm_apply_apply`。

**为何写在本文件**（`M18` 的正解，S66 R10 的 `Hyp741` 曾在此撞 `whnf` 超 8M）：
新文件里 `import Hyp719` 再展开会把 `Cᴵ` ＋ `[IsClosed]` ＋ 商类型同时展开；
这里上下文小、类型已展开，**一次即通**（实测 2.9s）。 -/
theorem inflStep_explicitInfl1
    [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)]
    (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C)))
    (z : H1 (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)) :
    inflStep (H := H) (C := C) hC (TauCeti.ContCohomology.explicitInfl1 G C H z) = z :=
  AddEquiv.symm_apply_apply _ z

/-- ★★★★★ **`∂²` 的前两因子已装配**：`H²(G,A) ≃+ H1 (G⧸H) (C^H)`（任意离散短正合列 `S`）。

`∂²` 只剩最后一格：`H1 (G⧸H) (C^H) → H1 (G⧸H) (H¹(H,A))`（系数映射 `M`；其 `G⧸H`-等变本体见 `Hyp718`）。 -/
noncomputable def deltaTwoShift (S : DiscreteShortExact G A B C)
    (hB1 : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ G B)))
    (hB2 : Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ G B)))
    [ContinuousSMul (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C)]
    (hC : Subsingleton (continuousCohomology 1 (ofDiscreteModule ℤ ↥H C))) :
    continuousCohomology 2 (ofDiscreteModule ℤ G A) ≃+
      H1 (G ⧸ H) ↥(FixedPoints.addSubgroup (↥H) C) :=
  (deltaShift1 (C := C) S hB1 hB2).trans
    ((h1BridgeQ (C := C)).trans (inflStep (H := H) (C := C) hC))

end Closed

end L20261018

#print axioms L20261018.deltaShift1
#print axioms L20261018.h1BridgeQ
#print axioms L20261018.inflStep
#print axioms L20261018.inflStep_explicitInfl1
#print axioms L20261018.deltaTwoShift
