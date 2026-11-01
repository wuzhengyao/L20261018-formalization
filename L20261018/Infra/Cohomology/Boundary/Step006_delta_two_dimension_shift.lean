import L20261018.Infra.Cohomology.Boundary.Step005_coinduced_invariants_recon
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import TauCeti.RepresentationTheory.Induction.DimensionShift

/-!
# R1097（**(R2)：抽象侧 `∂₂` 组装第 1 步 —— 维数平移同构 `H^n(G,C) ≅ H^{n+1}(G,A)`**）

## 路线（`PLAN-R2` §H-9）

GS 6.8.5 的 `∂₂`（`i = 2`）＝ 三段复合：

| 段 | 内容 | 状态 |
|---|---|---|
| **(1)** | `H^{i}(G,A) ≅ H^{i-1}(G,C)`（`0 → A → M^G(A) → C → 0` 的长正合列，用 `H^*(G, Coind_⊥^G A) = 0`） | ★ **本轮** |
| (2) | `H^{i-1}(G,C) ≅ H^{i-1}(G/H, C^H)`（inflation；用 `H^j(H,C) = 0`，由 `Hyp226` 的两条零调性） | 下一轮 |
| (3) | `C^H = H^0(H,C) → H^1(H,A)`（`H` 侧 LES 的 `δ`） | 下一轮 |

## 本轮（段 (1)）

库内零件：`Rep.dimensionShiftUp A := cokernel (coindBotUnit A)`（正是 GS 的 `C`）、
`dimensionShiftUpπ`、`coindBotUnit_comp_dimensionShiftUpπ`（复合为 `0`）、
`dimensionShiftUpSES_shortExact`（短正合）、`groupCohomology.isZero_coindBot_succ`（`H^{m+1}(G, Coind_⊥^G A) = 0`）、
`isIso_map_of_shortExact_of_isZero` 的同族 `ShortExact.δIso`，以及 `groupCohomology.map_cochainsFunctor_shortExact`（余链层短正合）。

| 声明 | 内容 |
|---|---|
| **`coindBot_dimensionShift`** | `H^n(G, C) ≅ H^{n+1}(G, A)`（`n ≥ 1`，`C = cokernel(coindBotUnit A)`） |
| **`coindBot_dimensionShift_two`** | 特例 `H¹(G,C) ≅ H²(G,A)`（GS 的 `i = 2` 段） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- 维数平移短正合列的**短复形**（与 GS 的 `0 → A → M^G(A) → C → 0` 一致）。 -/
noncomputable abbrev coindBotSES (A : Rep k G) : ShortComplex (Rep k G) :=
  Rep.dimensionShiftUpSES A

/-- ★ **维数平移同构**：`H^n(G, C) ≅ H^{n+1}(G, A)`，其中 `C = cokernel (coindBotUnit A)`。

GS 6.8.5：`0 → A → M^G(A) → C → 0` 的长正合列，配合 `H^*(G, M^G(A)) = 0`（`*>0`）给出。 -/
noncomputable def coindBot_dimensionShift (A : Rep k G) (n : ℕ) (hn : 1 ≤ n) :
    groupCohomology (Rep.dimensionShiftUp A) n ≅ groupCohomology A (n + 1) :=
  (groupCohomology.map_cochainsFunctor_shortExact (Rep.dimensionShiftUpSES_shortExact A)).δIso
    n (n + 1) rfl
    (by
      have := groupCohomology.isZero_coindBot_succ (k := k) (G := G) A.V (n - 1)
      rwa [Nat.sub_add_cancel hn] at this)
    (groupCohomology.isZero_coindBot_succ (k := k) (G := G) A.V n)

/-- ★ **GS 的 `i = 2` 段**：`H¹(G, C) ≅ H²(G, A)`。 -/
noncomputable def coindBot_dimensionShift_two (A : Rep k G) :
    groupCohomology (Rep.dimensionShiftUp A) 1 ≅ groupCohomology A 2 :=
  coindBot_dimensionShift A 1 le_rfl

end L20261018

#print axioms L20261018.coindBot_dimensionShift
#print axioms L20261018.coindBot_dimensionShift_two
