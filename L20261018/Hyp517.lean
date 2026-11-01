import Hyp516
import Hyp511

/-!
# S43 R22（**去条件化 Hyp505**）：把（★）搬到**战役载体** `inertiaLoc F`

## 本件做什么

`Hyp516` 已在 **TauCeti 载体** `inertiaSubgroup F`（`Gal(F^alg/F)`）上证出（★）：
`InertiaProPSylowData ↥(inertiaSubgroup F) ℓ`，零条件（除 ℓ ≠ char κ）。

战役载体是 `inertiaLoc F`（`Hyp380`，`Gal(F^s/F_nr)`，逐字即 GS 的 `H`）。
`Hyp511` 已机检二者沿 `absoluteGaloisGroupRestrictEquiv F` **是同一个子群**：

```
inertiaLoc F = (inertiaSubgroup F).map (absoluteGaloisGroupRestrictEquiv F)
```

本件沿这个 `≃ₜ*` 把 `InertiaProPSylowData` 运输过去，于是 **`Hyp505` 的五条条件定理全部去条件化**：

| `Hyp505`（条件形态） | 本件（**无条件**） |
|---|---|
| `inertia_cohomologicalDimensionAt_le_one (D)` | **`inertiaLoc_cohomologicalDimensionAt_le_one`** |
| `inertia_cdLE (D)` | **`inertiaLoc_cdLE`** |
| `inertia_subsingleton_Hq (D) …` | **`inertiaLoc_subsingleton_Hq`** |
| `inertia_subsingleton_H2_zmod (D)` | **`inertiaLoc_subsingleton_H2_zmod`** |
| `inertia_subsingleton_H2 (D) …` | **`inertiaLoc_subsingleton_H2`** |

## 机检内容

| 声明 | 内容 |
|---|---|
| **`inertiaEquivInertiaLoc`** | `↥(inertiaSubgroup F) ≃ₜ* ↥(inertiaLoc F)`（`Hyp511` ＋ `subgroupMap`） |
| **`InertiaProPSylowData.congrContinuousMulEquiv`** | 数据沿 `≃ₜ*` 运输（Sylow 用 `map_continuousMulEquiv`） |
| **`inertiaProPSylowData_inertiaLoc`** | ★★★★★ **（★）在战役载体上，无条件** |
| **`inertiaLoc_cdLE`** 等 5 条 | ★★★★★ **`Hyp505` 去条件化** |

## 诚实边界（L16 载体身份，**不变**）

* 载体仍是 `IsNonarchimedeanLocalField F`（**完备**、剩余域**有限**）。
  论文的 `F` 是「Hensel 离散赋值域，剩余域 `κ` 任意」⟹ **`C2`（Hensel → 完备）仍待做**。
* `B1`（`Finite (H¹(I, μ_p))`）与 `Hyp506`（GS §7）未触及。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti
open scoped TauCeti.zHat

namespace L20261018

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- `↥(inertiaLoc F)` 紧（闭子群 of 紧群）。 -/
local instance compactSpaceInertiaLoc : CompactSpace ↥(inertiaLoc F) :=
  isCompact_iff_compactSpace.mp (isClosed_inertiaLoc F).isCompact

/-- ★★★★ **战役载体与 TauCeti 载体的拓扑同构**
（`Hyp511` 的等号 ＋ `ContinuousMulEquiv.subgroupMap`）。 -/
noncomputable def inertiaEquivInertiaLoc :
    ↥(TauCeti.inertiaSubgroup F) ≃ₜ* ↥(inertiaLoc F) :=
  -- `Hyp511` 的等号（两个 `Subgroup.map` 的 `MonoidHom` 形状定义上相同，`rfl` 可过）
  have h : Subgroup.map (↑↑(TauCeti.absoluteGaloisGroupRestrictEquiv F))
      (TauCeti.inertiaSubgroup F) = inertiaLoc F :=
    map_inertiaSubgroup_eq_inertiaLoc F
  h ▸ ContinuousMulEquiv.subgroupMap (TauCeti.absoluteGaloisGroupRestrictEquiv F)
    (TauCeti.inertiaSubgroup F)

/-- ★★★★ **`InertiaProPSylowData` 沿拓扑群同构运输**：
Sylow 沿 `IsProPSylow.map_continuousMulEquiv`，`ℤ_p`-同构沿 `subgroupMap`。 -/
noncomputable def InertiaProPSylowData.congrContinuousMulEquiv {I J : Type}
    [Group I] [TopologicalSpace I] [IsTopologicalGroup I] [CompactSpace I]
    [TotallyDisconnectedSpace I]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J] [CompactSpace J]
    [TotallyDisconnectedSpace J]
    (p : ℕ) [Fact p.Prime] (D : InertiaProPSylowData I p) (e : I ≃ₜ* J) :
    InertiaProPSylowData J p where
  P := Subgroup.map (↑e) D.P
  isProPSylow := D.isProPSylow.map_continuousMulEquiv e
  padicEquiv :=
    ⟨(ContinuousMulEquiv.subgroupMap e D.P).symm.trans D.padicEquiv.some⟩

/-- ★★★★★ **（★）在战役载体 `inertiaLoc F` 上，无条件**（只需 ℓ 与 char κ 互素）。

由 `Hyp516.inertiaProPSylowData_inertia`（TauCeti 载体）沿
`inertiaEquivInertiaLoc` 运输。 -/
noncomputable def inertiaProPSylowData_inertiaLoc (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    InertiaProPSylowData ↥(inertiaLoc F) ℓ :=
  (inertiaProPSylowData_inertia (K := F) q ℓ hℓ).congrContinuousMulEquiv ℓ
    (inertiaEquivInertiaLoc (F := F))

/-- ★★★★★ **`cd_ℓ(I) ≤ 1`，`I = Gal(F^s/F_nr)`，无条件**（`Hyp505` 的去条件化）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9627 quote="Therefore $\operatorname{cd}_{\ell}(H)\leq1$"
theorem inertiaLoc_cohomologicalDimensionAt_le_one (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    cohomologicalDimensionAt.{0, 0} ℓ ↥(inertiaLoc F) ≤ 1 :=
  (inertiaProPSylowData_inertiaLoc (F := F) q ℓ hℓ).cohomologicalDimensionAt_le_one

/-- ★★★★★ **`CohomologicalDimensionLE ℓ I 1`，无条件**。 -/
theorem inertiaLoc_cdLE (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    CohomologicalDimensionLE.{0, 0} ℓ ↥(inertiaLoc F) 1 :=
  (inertiaProPSylowData_inertiaLoc (F := F) q ℓ hℓ).cdLE

/-- ★★★★★ **`H^q(I, M) = 0`（`q ≥ 2`），无条件**（`M` 为 `ℓ`-primary 挠，作用任意）。 -/
theorem inertiaLoc_subsingleton_Hq (q' : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q')
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion ℓ M) {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  (inertiaProPSylowData_inertiaLoc (F := F) q' ℓ hℓ).subsingleton_Hq M hM hn

/-- **`↥(inertiaLoc F)` 在 `ZMod n` 上的平凡作用**（下游 `μ_ℓ` 情形的一个合法实例）。 -/
local instance trivialActionZModInertiaLoc (n : ℕ) :
    DistribMulAction ↥(inertiaLoc F) (ZMod n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- 该平凡作用下的 `ContinuousSMul`。 -/
local instance trivialContinuousSMulInertiaLoc (n : ℕ) :
    ContinuousSMul ↥(inertiaLoc F) (ZMod n) where
  continuous_smul := continuous_snd

/-- ★★★★★ **`H²(I, μ_ℓ) = 0`，无条件** ——
**S41 §4.6 记的「唯一外部数学输入 `H²(惯性群, μ_ℓ) = 0`」在战役载体上已无条件成立**。 -/
theorem inertiaLoc_subsingleton_H2_zmod (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q) :
    Subsingleton (continuousCohomology 2
      (ofDiscreteModule ℤ ↥(inertiaLoc F) (ZMod ℓ))) :=
  (inertiaProPSylowData_inertiaLoc (F := F) q ℓ hℓ).subsingleton_H2 (ZMod ℓ)
    (isPPrimaryTorsion_of_module_zmod ℓ (ZMod ℓ))

/-- ★★★★ **`H²(I, M) = 0`（任意 `ℓ`-primary 挠 `M`），无条件**。 -/
theorem inertiaLoc_subsingleton_H2 (q' : ℕ)
    [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) q']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime q')
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ↥(inertiaLoc F) M] [ContinuousSMul ↥(inertiaLoc F) M]
    (hM : IsPPrimaryTorsion ℓ M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ ↥(inertiaLoc F) M)) :=
  (inertiaProPSylowData_inertiaLoc (F := F) q' ℓ hℓ).subsingleton_H2 M hM

end L20261018

#print axioms L20261018.inertiaEquivInertiaLoc
#print axioms L20261018.InertiaProPSylowData.congrContinuousMulEquiv
#print axioms L20261018.inertiaProPSylowData_inertiaLoc
#print axioms L20261018.inertiaLoc_cohomologicalDimensionAt_le_one
#print axioms L20261018.inertiaLoc_cdLE
#print axioms L20261018.inertiaLoc_subsingleton_Hq
#print axioms L20261018.inertiaLoc_subsingleton_H2_zmod
#print axioms L20261018.inertiaLoc_subsingleton_H2
