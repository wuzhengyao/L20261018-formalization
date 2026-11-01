import L20261018.Hyp517
import L20261018.Hyp518

/-!
# S43 R41：★★★★★ **(★) 直接供给 GS 6.8.5 的输入假设**（`cd_ℓ(I) ≤ 1` ⟹ `H^i(I,·) = 0`, `i ≥ 2`）

## 测量的结论（本轮核心）

`TauCeti.CohomologicalDimensionLE`（`ContCohomology/CohomologicalDimension/Basic.lean:131`）的定义是
**全次数统一**的：

```lean
def CohomologicalDimensionLE (n : ℕ) : Prop :=
  ∀ (M) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M], IsPPrimaryTorsion p M →
    ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M))
```

⟹ `Hyp517.inertiaLoc_cdLE : CohomologicalDimensionLE ℓ ↥(inertiaLoc F) 1`
**逐字就是** GS 6.8.5 所需的假设（`cd_ℓ(H) ≤ 1`），**不需要逐次数展开**。

## GS 6.8.5 的输入假设（本件把它命名为一个 `def`）

GS `cons-residue-map-finite-coefficients`（`raw/GilleSzamuely2017.tex:9455`）：

> 「Let `G` be a profinite group, and let `H` be a closed normal subgroup in `G` with
> `cd(H) ≤ 1`. We construct maps `∂^i : H^i(G,A) → H^{i-1}(G/H, H¹(H,A))`」

⟹ 所需输入 = 对所有 `p`-primary 挠 `M`、所有 `i ≥ 2`，`H^i(I, M) = 0`。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`GsInputHyp`** | 上述输入假设的**具名 `def`**（类型锁） |
| **`gsInputHyp_of_cdLE`** | ★★★★★ **`ℓ.Coprime q → GsInputHyp ℓ`**（由（★）`inertiaLoc_cdLE` **直接**得出） |

## 诚实边界（剩余工作的精确描述）

* 本件只用**连续**侧框架（`continuousCohomology`）。而战役的 `Hyp239.deltaTwo`
  （GS 6.8.5 的 `Rep`／`groupCohomology` 版）的 `hcd` 在**抽象**侧，实查**无见证**，
  且库内连续↔抽象桥只有「低次（≤ 2）」（`Hyp226` 记录）—— 不够 `hcd` 的**全次数**要求。
* ⟹ **正确路线**：在**连续**框架里做 GS 6.8.5。库内已有
  `ContCohomology/Inflation/{Basic,ConnectingMap}.lean`（膨胀 `explicitInfl1`、
  `explicitRes1_comp_explicitInfl1`、`delta_infl`），而 `hcd` 由本件供给。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- ★★★★★ **GS 6.8.5 的输入假设**：`cd_p(I) ≤ 1` 的**全次数**形式。

对每个 `p`-primary 挠的离散 `I`-模 `M` 与每个 `i ≥ 2`，`H^i(I, M)` 是单点。
（GS `cons-residue-map-finite-coefficients` 的第一句就是这个。） -/
def GsInputHyp (p : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M],
    IsPPrimaryTorsion p M → ∀ i : ℕ, 1 < i →
      Subsingleton (continuousCohomology i (ofDiscreteModule ℤ ↥(inertiaLoc F) M))

/-- ★★★★★ **（★）⟹ GS 6.8.5 的输入假设**（`ℓ.Coprime (char κ)`）。

直接由 `Hyp517.inertiaLoc_cdLE`（`CohomologicalDimensionLE ℓ I 1`）的**定义展开**得出 ——
`CohomologicalDimensionLE` 本就是全次数统一的，故无需任何逐次数工作。 -/
theorem gsInputHyp_of_cdLE (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (p : ℕ) [Fact p.Prime] (hpq : p.Coprime q) :
    GsInputHyp (F := F) p :=
  inertiaLoc_cdLE (F := F) q p hpq

/-- 与逐次数版本的一致性（回归对照）：本件的 `GsInputHyp` 与
`Hyp518.inertiaLoc_Hq_eq_zero` 给出**同一结论**。 -/
theorem gsInputHyp_apply (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (p : ℕ) [Fact p.Prime] (hpq : p.Coprime q)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion p M) {i : ℕ} (hi : 2 ≤ i) :
    Subsingleton (continuousCohomology i (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  gsInputHyp_of_cdLE (F := F) q p hpq M hM i hi

end L20261018

#print axioms L20261018.gsInputHyp_of_cdLE
#print axioms L20261018.gsInputHyp_apply
