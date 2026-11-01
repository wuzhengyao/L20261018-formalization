import Hyp504
import Hyp380

/-!
# S42 R3：把（★）条件定理**实例化到战役真实载体** —— `I = Gal(K_s/K_nr) = inertiaLoc`

## 本件做什么

`Hyp504` 把 GS A.6.9 的群论半写成**抽象**具名假设 `InertiaProPSylowData`，
并机检「（★）⟹ `cd_p(I) ≤ 1` ⟹ `H²(I,M) = 0`」。
本件把它**落到战役自己的惯性群**上：`I := L20261018.inertiaLoc F`（`Hyp380`，逐字即 GS 的
`Gal(K_s/K_nr)`，`fixedField_inertiaLoc` 机检过 `fixedField I = K_nr`）。

```
D : InertiaProPSylowData ↥(inertiaLoc F) p        -- （★）在本载体上的形态
⟹ CohomologicalDimensionLE p ↥(inertiaLoc F) 1    -- cd_p(I) ≤ 1
⟹ H²(↥I, ZMod p) = 0                              -- §4.6 的唯一外部输入（本载体版）
```

## ★★★ R3 发现：**载体身份问题（L16）—— `inertiaLoc` 只在 `IsNonarchimedeanLocalField` 上**

`Hyp380` 的 `variable` 是

```lean
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
```

而 mathlib 的 `IsNonarchimedeanLocalField K extends IsValuativeTopology K, LocallyCompactSpace K,
ValuativeRel.IsNontrivial K`（`Mathlib/NumberTheory/LocalField/Basic.lean:46`），
配合 `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
（同文件 `:149`）⟹ **剩余域有限**。

而**论文的设定是「Hensel 离散赋值域，剩余域 `K` 任意」**（`raw/L20261018.tex:987`：
"设 $(F,v)$ 为 Hensel 离散赋值域，剩余域为 $K$，$\operatorname{char}K\ne p$，且 $\mu_p\subset F$"）。
两者**不同身份**（L16）：`IsNonarchimedeanLocalField` ⊊「Hensel 离散赋值域」。

**后果（必须登记）**：

| 载体 | 本件的（★）条件定理 | 论文的一般 `κ` |
|---|---|---|
| `inertiaLoc F`（`IsNonarchimedeanLocalField`） | ✅ **本件已机检** | ❌ 载体太强 |
| 抽象 `KnrSubfield`（`Hyp466`：`⋃_{K'/K 有限可分} K'((π))`） | ⏳ 未做（需在该载体上重述（★）） | ✅ 论文设定 |

⟹ **即使（★）被解除，一般 `κ` 分支还需把（★）在 `KnrSubfield` 载体上重述一次**；
本件解决的是**有限剩余域分支的局部载体**（正是 `Hyp344` 已无条件成立的**同一分支**）。

## 诚实边界

* 本件**不**证明（★）（本载体版）。`Hyp344`（有限 `K` 无条件）与本件的关系：
  `Hyp344` 走的是**另一条**路（不经惯性群），本件给的是**经（★）的同一分支**备用链。
* 本件**不**触及一般 `κ` 分支（见上表）。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open TauCeti

namespace L20261018

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (p : ℕ) [NeZero p] [Fact p.Prime]

/-- `I` 紧：`I` 是绝对 Galois 群（射有限群，紧）的**闭**子群（`Hyp380.isClosed_inertiaLoc`）。 -/
local instance compactSpaceInertia : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- `↥(inertiaLoc F)` 在 `ZMod p` 上的**平凡作用**（`μ_p ⊂ F` ⟹ 惯性群在 `μ_p` 上平凡）。 -/
local instance trivialActionZModInertia : DistribMulAction ↥(inertiaLoc F) (ZMod p) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该作用下的 `ContinuousSMul`（`smul` 即投影）。 -/
local instance trivialContinuousSMulInertia : ContinuousSMul ↥(inertiaLoc F) (ZMod p) where
  continuous_smul := continuous_snd

-- @source file=raw/GilleSzamuely2017.tex locator=label:cons-residue-map-finite-coefficients-2 quote="write $G$ and $H$ for the Galois groups $\operatorname{Gal}(K_{s}|K)$ and $\operatorname{Gal}(K_{s}|K_{nr})$, respectively, where $K_{nr}$ is the maximal unramified extension of $K$"
-- @source file=raw/GilleSzamuely2017.tex locator=line:9627 quote="Therefore $\operatorname{cd}_{\ell}(H)\leq1$"
/-- ★★★★★ **（★）⟹ `cd_p(I) ≤ 1`**，`I = Gal(K_s/K_nr)`（战役载体 `inertiaLoc F`）。 -/
theorem inertia_cohomologicalDimensionAt_le_one
    (D : InertiaProPSylowData ↥(inertiaLoc F) p) :
    cohomologicalDimensionAt.{0, 0} p ↥(inertiaLoc F) ≤ 1 :=
  D.cohomologicalDimensionAt_le_one

/-- ★★★★★ **（★）⟹ `CohomologicalDimensionLE p I 1`**（`H^q(I,M) = 0`，`q > 1`）。 -/
theorem inertia_cdLE (D : InertiaProPSylowData ↥(inertiaLoc F) p) :
    CohomologicalDimensionLE.{0, 0} p ↥(inertiaLoc F) 1 :=
  D.cdLE

/-- ★★★★★ **（★）⟹ `H^q(I, M) = 0`（`q ≥ 2`）**，`M` 为 `p`-primary 挠离散模。 -/
theorem inertia_subsingleton_Hq (D : InertiaProPSylowData ↥(inertiaLoc F) p)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion p M) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (continuousCohomology q (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  D.subsingleton_Hq M hM hq

/-- ★★★★★ **（★）⟹ `H²(I, μ_p) = 0`**（`μ_p = ZMod p`，平凡作用）。

**这就是 S41 §4.6 记的「唯一外部数学输入 `H²(惯性群, μ_p) = 0`」在本载体上的条件形态。** -/
theorem inertia_subsingleton_H2_zmod (D : InertiaProPSylowData ↥(inertiaLoc F) p) :
    Subsingleton (continuousCohomology 2
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (ZMod p))) :=
  D.subsingleton_H2 (ZMod p) (isPPrimaryTorsion_of_module_zmod p (ZMod p))

/-- ★★★★ **（★）⟹ `H²(I, M) = 0`**（任意 `p`-primary 挠 `M`）。 -/
theorem inertia_subsingleton_H2 (D : InertiaProPSylowData ↥(inertiaLoc F) p)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  D.subsingleton_H2 M hM

end L20261018

#print axioms L20261018.inertia_cohomologicalDimensionAt_le_one
#print axioms L20261018.inertia_cdLE
#print axioms L20261018.inertia_subsingleton_Hq
#print axioms L20261018.inertia_subsingleton_H2_zmod
#print axioms L20261018.inertia_subsingleton_H2
