import L20261018.Hyp283
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Comparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.ConnectingMap

/-!
# R1165（**第 5 项组装：`cd ≤ 1` 的 `H²` 零化 ＋ `residueSpan = ⊥` 时的归约**）

## 本轮做什么

`R1164` 发现库内 `cd` 与 inflation 基建齐全，`port_tau.py` 的 `FAIL` 实为**当前工作目录**问题
（Lean 的 root dir 取 CWD；从仓库根运行即成功）—— `CohomologicalDimension.Comparison` 与
`Inflation.{Basic,ConnectingMap}` 现已 port ✓。

本轮给出两块机检：

**(甲)** `h2_eq_zero_of_cd_le_one`：`cd_p(G) ≤ 1` ⟹ 每个 `p`-primary torsion 系数的 `H²` 类为 `0`
（`CohomologicalDimensionLE.subsingleton_H2` 的封装，建立「库内 `cd` 与本工程可用」的连通性）。

**(乙)** `tameResidueFacts_of_span_eq_bot`：**若单位杯积张成块 `residueSpan = ⊥`，
则 `TameResidueFacts` ⟺ (R1)（`phi_injective`）** —— 这正是有限剩余域（`H²(𝕜,μ_p) = 0`）一档的形态，
把 (R2) 从「`disjoint`」降为「`residueSpan` 为零」，而后者由 `cd` 断言。

## 本轮

| 声明 | 内容 |
|---|---|
| **`h2_eq_zero_of_cd_le_one`** | ★★★ `cd_p(G) ≤ 1 ⟹ H²(G,A) 中每类为零` |
| **`tameResidueFacts_of_span_eq_bot`** | ★★★★ **`residueSpan = ⊥ ⟹ TameResidueFacts ⟺ (R1)`** |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

/-! ### (甲) `cd ≤ 1` 的 `H²` 零化 -/

universe u

/-- ★★★ **`cd_p(G) ≤ 1` ⟹ `H²(G,A)` 中每个类为零**（`p`-primary torsion 系数）。 -/
theorem h2_eq_zero_of_cd_le_one {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    (hcd : TauCeti.CohomologicalDimensionLE.{u, u} p G 1)
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
    [ContinuousSMul G A] (hA : TauCeti.IsPPrimaryTorsion p A)
    (x : TauCeti.ContCohomology.H2 G A) : x = 0 := by
  haveI := TauCeti.CohomologicalDimensionLE.subsingleton_H2 hcd A hA
  exact Subsingleton.elim x 0

/-! ### (乙) `residueSpan = ⊥` 时的归约 -/

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]
variable {cup : V →ₗ[k] V →ₗ[k] H2} {val : V →ₗ[k] k} {π : V}

/-- ★★★★ **`residueSpan = ⊥` 时 `TameResidueFacts` ⟺ (R1)**。

（`residueSpan` 由单位×单位杯积张成；它为零时 `disjoint` 自动成立，两条事实只剩 `phi_injective`。） -/
theorem tameResidueFacts_of_span_eq_bot
    (hspan : residueSpan cup val = ⊥) (hR1 : Function.Injective (residuePhi cup val π)) :
    TameResidueFacts cup val π where
  phi_injective := hR1
  disjoint := by
    rw [hspan]
    exact disjoint_bot_right

end L20261018

#print axioms L20261018.h2_eq_zero_of_cd_le_one
#print axioms L20261018.tameResidueFacts_of_span_eq_bot
