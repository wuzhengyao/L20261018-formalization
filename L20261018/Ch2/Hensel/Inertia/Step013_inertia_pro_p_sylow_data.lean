import L20261018.Ch2.Rost.Step001_cd_p_z_p_le_one
import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Containment

/-!
# S42 R2（A.6.9 群论半）：**具名假设 `InertiaProPSylowData` ＋ `cd_p(I) ≤ 1` 的机检运输**

## 本件在 A.6.9 的哪一格

S42 R1（`Hyp503`）机检了 A.6.9 的**上同调半**：`cd_p(ℤ_p) = 1`。
缺的只剩**群论半**（GS A.6.9）：

> **（★）惯性群 `I = Gal(K_s/K_nr)` 的最大 pro-`p` 商 ≅ `ℤ_p`**。

本件把（★）写成**一个 type-locked 具名假设** `InertiaProPSylowData`，
并机检**「（★）⟹ `cd_p(I) ≤ 1`」的运输**（GS `:9626`–`:9628` 的原文论证）：

```
（★）: ∃ P ≤ I, IsProPSylow p P ∧ P ≃ₜ* ℤ_p
  ⟹ cd_p(I) ≤ cd_p(P)            -- TauCeti.IsProPSylow.cohomologicalDimensionAt_le
  ⟹ cd_p(P) = cd_p(ℤ_p)          -- TauCeti.cohomologicalDimensionAt_congr（沿 ≃ₜ*）
  ⟹ cd_p(ℤ_p) = 1                -- ★ Hyp503（S42 R1）
  ⟹ cd_p(I) ≤ 1  且  H^q(I, M) = 0（q ≥ 2，M 为 p-primary 挠）
```

## 为什么把（★）写成「Sylow ≅ ℤ_p」而不是「`I` 的 pro-`p` 商 ≅ `ℤ_p`」

* 「Sylow ≅ `ℤ_p`」是 GS 的**逐字形态**（`raw/GilleSzamuely2017.tex:9625`：
  "the $\ell$-Sylow subgroups of $H$ are isomorphic to $\mathbf{Z}_{\ell}$"）；
* 它是**能直接喂给库内定理**的形态（`IsProPSylow.cohomologicalDimensionAt_le` 要的正是它）；
* 「最大 pro-`p` 商 ≅ `ℤ_p`」与它等价（pro-`p` Sylow ↠ 最大 pro-`p` 商），
  但要**从**商形态**回到** Sylow 形态需另证（`IsProPSylow` 的定义里还有「所有开正规商的像的指数与 `p` 互素」）。

## 主要声明

| 声明 | 内容 |
|---|---|
| **`InertiaProPSylowData`** | ★★★★★ **（★）的 type-locked 形态**（具名假设） |
| **`cohomologicalDimensionAt_le_one_of_proPSylowData`** | ★★★★★ **（★）⟹ `cd_p(I) ≤ 1`** |
| **`cdLE_of_proPSylowData`** | **（★）⟹ `CohomologicalDimensionLE p I 1`** |
| **`subsingleton_Hq_of_proPSylowData`** | ★★★★ **（★）⟹ `H^q(I,M) = 0`（`q ≥ 2`）** |
| **`subsingleton_H2_of_proPSylowData`** | ★★★★★ **（★）⟹ `H²(I,μ_p) = 0`**（= §4.6 的唯一外部输入） |
| **`inertiaProPSylowData_witness`** | ★★★ **非空见证（L1／L10①）**：`I = ℤ_p`、`P = ⊤` 满足（★） |

## 诚实边界

* 本件**不**证明（★）。（★）＝ GS A.6.9 的群论半，两库皆无；可行性裁定见
  `S42-STATUS.md` §7／`RECON-R3` §127（两条候选路线与代价）。
* 本件给的是**条件定理**：把 §4.6 的「唯一外部输入」从一个**复合陈述**（`H²(I,μ_p)=0`）
  换成一个**结构陈述**（`I` 的 `p`-Sylow ≅ `ℤ_p`）——后者是 GS 的原文形态、**且是可被
  驯歧理论一次性打掉的形态**。
* 本件**不**涉及 `Finite (H¹(I,μ_p))`（§4.7 的另一半）；该半的路线见 `S42-REMAINING-PLAN` §3 B1。
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open TauCeti

namespace L20261018

/-- ★★★★★ **A.6.9 群论半的 type-locked 具名假设**：`I`（惯性群）有一个 Sylow pro-`p` 子群 `P`
与 `ℤ_p` 拓扑同构。

**逐字对应 GS**（`raw/GilleSzamuely2017.tex:9625`）：
"the $\ell$-Sylow subgroups of $H$ are isomorphic to $\mathbf{Z}_{\ell}$ for $\ell$ prime to
$\operatorname{char}(\kappa(v))$"。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9625 quote="the $\ell$-Sylow subgroups of $H$ are isomorphic to $\mathbf{Z}_{\ell}$ for $\ell$ prime to $\operatorname{char}(\kappa(v))$"
structure InertiaProPSylowData (I : Type) [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
    [CompactSpace I] [TotallyDisconnectedSpace I] (p : ℕ) [Fact p.Prime] where
  /-- 所取的 `p`-Sylow 子群。 -/
  P : Subgroup I
  /-- 它是 Sylow pro-`p`（闭 ＋ pro-`p` ＋ 所有开正规商的像指数与 `p` 互素）。 -/
  isProPSylow : IsProPSylow p P
  /-- 它与 `ℤ_p` 拓扑同构（A.6.9 的结论）。 -/
  padicEquiv : Nonempty (↥P ≃ₜ* Multiplicative ℤ_[p])

namespace InertiaProPSylowData

variable {p : ℕ} [Fact p.Prime] {I : Type} [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [CompactSpace I] [TotallyDisconnectedSpace I]

/-- ★★★★★ **（★）⟹ `cd_p(I) ≤ cd_p(ℤ_p)`**：Sylow 单调 ＋ 沿 `≃ₜ*` 不变。

（GS 原文：`cd_ℓ(H) ≤ 1` by `prop-cd-Z-hat` and `lemma-cd-subgroup`。） -/
theorem cohomologicalDimensionAt_le_padicInt (D : InertiaProPSylowData I p) :
    cohomologicalDimensionAt.{0, 0} p I ≤ cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) := by
  obtain ⟨e⟩ := D.padicEquiv
  calc cohomologicalDimensionAt.{0, 0} p I
      ≤ cohomologicalDimensionAt.{0, 0} p ↥D.P := D.isProPSylow.cohomologicalDimensionAt_le
    _ = cohomologicalDimensionAt.{0, 0} p (Multiplicative ℤ_[p]) :=
        cohomologicalDimensionAt_congr e

/-- ★★★★★ **（★）⟹ `cd_p(I) ≤ 1`**（A.6.9 的群论半 ＋ S42 R1 的上同调半）。 -/
-- @source file=raw/GilleSzamuely2017.tex locator=line:9627 quote="Therefore $\operatorname{cd}_{\ell}(H)\leq1$"
theorem cohomologicalDimensionAt_le_one (D : InertiaProPSylowData I p) :
    cohomologicalDimensionAt.{0, 0} p I ≤ 1 :=
  le_trans D.cohomologicalDimensionAt_le_padicInt
    (le_of_eq (cohomologicalDimensionAt_padicInt_eq_one p))

/-- **（★）⟹ `CohomologicalDimensionLE p I 1`**：`H^q(I, M) = 0` 对一切 `q > 1`。 -/
theorem cdLE (D : InertiaProPSylowData I p) : CohomologicalDimensionLE.{0, 0} p I 1 :=
  (cohomologicalDimensionAt_le_iff p I 1).1 D.cohomologicalDimensionAt_le_one

/-- ★★★★ **（★）⟹ `H^q(I, M) = 0`（`q ≥ 2`）**，`M` 为 `p`-primary 挠离散模（作用**任意**）。 -/
theorem subsingleton_Hq (D : InertiaProPSylowData I p)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction I M] [ContinuousSMul I M] (hM : IsPPrimaryTorsion p M)
    {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (continuousCohomology q (ofDiscreteModule ℤ I M)) :=
  cohomologicalDimensionLE_iff.1 D.cdLE M hM q (by omega)

/-- ★★★★★ **（★）⟹ `H²(I, M) = 0`**（`q = 2`）：正是 §4.6 记作「唯一外部数学输入」的那一格。 -/
theorem subsingleton_H2 (D : InertiaProPSylowData I p)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction I M] [ContinuousSMul I M] (hM : IsPPrimaryTorsion p M) :
    Subsingleton (continuousCohomology 2 (ofDiscreteModule ℤ I M)) :=
  D.subsingleton_Hq M hM le_rfl

/-- **（★）⟹ `cd_p(I) ≠ 0` 时 `cd_p(I) = 1`**：若 `I` 的 `p`-Sylow 非平凡（`ℤ_p` 非平凡），
则 `cd_p(I) = 1`（上下界夹住），故 `cd_p(I) ≤ 1` **不是空洞的**。 -/
theorem cohomologicalDimensionAt_eq_one (D : InertiaProPSylowData I p)
    (h : cohomologicalDimensionAt.{0, 0} p I ≠ 0) :
    cohomologicalDimensionAt.{0, 0} p I = 1 := by
  refine le_antisymm D.cohomologicalDimensionAt_le_one ?_
  exact Order.one_le_iff_ne_zero.2 h

end InertiaProPSylowData

/-! ### 非空见证（L1／L10①）：假设类非空 -/

/-- ★★★ **非空见证（L1／L10①）**：取 `I = ℤ_p`、`P = ⊤`，则（★）成立。

（反方向也说明：本件条件定理的**假设类非空**，故 `cd_p(I) ≤ 1` 的结论不空洞。） -/
theorem inertiaProPSylowData_witness (p : ℕ) [Fact p.Prime] :
    Nonempty (InertiaProPSylowData (Multiplicative ℤ_[p]) p) :=
  ⟨{ P := ⊤
     isProPSylow := IsProP.isProPSylow_top (isProP_multiplicative_padicInt p)
     padicEquiv := ⟨{ toMulEquiv := Subgroup.topEquiv
                      continuous_toFun := continuous_subtype_val
                      continuous_invFun := Continuous.subtype_mk continuous_id fun _ => trivial }⟩ }⟩

/-- 见证的推论：`I = ℤ_p` 时由 `InertiaProPSylowData` 得到 `cd_p ≤ 1`（与 `Hyp503` 一致）。 -/
theorem cdLE_padicInt_via_data (p : ℕ) [Fact p.Prime] :
    CohomologicalDimensionLE.{0, 0} p (Multiplicative ℤ_[p]) 1 :=
  (inertiaProPSylowData_witness p).elim fun D => D.cdLE

end L20261018

#print axioms L20261018.InertiaProPSylowData.cohomologicalDimensionAt_le_padicInt
#print axioms L20261018.InertiaProPSylowData.cohomologicalDimensionAt_le_one
#print axioms L20261018.InertiaProPSylowData.cdLE
#print axioms L20261018.InertiaProPSylowData.subsingleton_Hq
#print axioms L20261018.InertiaProPSylowData.subsingleton_H2
#print axioms L20261018.inertiaProPSylowData_witness
#print axioms L20261018.cdLE_padicInt_via_data
