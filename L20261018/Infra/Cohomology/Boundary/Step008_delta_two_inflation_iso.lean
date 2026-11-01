import L20261018.Infra.Cohomology.Boundary.Step007_delta_two_gating
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# R1099（**(R2)：抽象侧 `∂₂` 第 2 段 —— inflation 同构 `H^m(G ⧸ S, C^S) ≅ H^m(G, C)`**）

## 路线（`PLAN-R2` §H-9）

`∂₂` 三段：**(1)** 维数平移（R1097 ✓）；**(2)** inflation（**本轮**）；**(3)** `C^S → H^1(S,A)`（`S` 侧 LES 的 `δ`）。

## 本轮（段 (2)）

GS 6.8.5（tex `:9486–9495`）：「for `i>2` … the inflation maps
`Inf : H^{i-1}(G/H, C^H) → H^{i-1}(G,C)` are isomorphisms」。库内抽象件：
**`TauCeti.groupCohomology.isIso_HInfRes_f`**（Milne II 1.34）：
`H^{n+1}(G ⧸ S, A^S) ⟶ H^{n+1}(G, A)` 为同构，只要 `H^i(S,A) = 0` 对 `0 < i ≤ n+1`。

**本轮与 R1098 正好衔接**：所需的 `H^j(S, C) = 0` 就是
`Hyp228.isZero_res_dimensionShiftUp_of_cd`（`cd(S) ≤ 1` 的抽象形式）。

| 声明 | 内容 |
|---|---|
| **`isIso_HInfRes_dimensionShiftUp`** | `IsIso (HInfRes C S m).f`（`m ≥ 1`，`C = Rep.dimensionShiftUp A`） |
| **`inflationIso_dimensionShiftUp`** | ★ `H^m(G ⧸ S, C^S) ≅ H^m(G, C)` |
| **`inflationIso_dimensionShiftUp_oneH`** | 特例 `H¹(G ⧸ S, C^S) ≅ H¹(G, C)`（`∂₂` 的 `i = 2` 段） |
| **`deltaTwo_firstHalf`** | ★ **`∂₂` 的前半**：`H²(G,A) ≅ H¹(G, C) ≅ H¹(G ⧸ S, C^S)`（(1)＋(2) 复合） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **GS 6.8.5 的 inflation 段（同构性）**：`H^{n+1}(G ⧸ S, C^S) ⟶ H^{n+1}(G, C)` 是同构。

前提 `cd(S) ≤ 1` 的抽象形式经 `Hyp228.isZero_res_dimensionShiftUp_of_cd` 提供所需的 `H^j(S,C) = 0`。 -/
theorem isIso_HInfRes_dimensionShiftUp (A : Rep k G)
    {S : Subgroup G} [S.Normal] (n : ℕ)
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    IsIso (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S (n + 1)).f :=
  TauCeti.groupCohomology.isIso_HInfRes_f (Rep.dimensionShiftUp A) (S := S) n
    (fun i _hi => isZero_res_dimensionShiftUp_of_cd A S hcd (i + 1) (by omega))

/-- ★ **GS 6.8.5 的 inflation 段**：`H^{n+1}(G ⧸ S, C^S) ≅ H^{n+1}(G, C)`（`C = Rep.dimensionShiftUp A`）。 -/
noncomputable def inflationIso_dimensionShiftUp (A : Rep k G)
    {S : Subgroup G} [S.Normal] (n : ℕ)
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    groupCohomology ((Rep.dimensionShiftUp A).quotientToInvariants S) (n + 1) ≅
      groupCohomology (Rep.dimensionShiftUp A) (n + 1) :=
  @asIso _ _ _ _ (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S (n + 1)).f
    (isIso_HInfRes_dimensionShiftUp A n hcd)

/-- 该同构就是 `HInfRes` 的 `.f`。 -/
theorem inflationIso_dimensionShiftUp_hom (A : Rep k G)
    {S : Subgroup G} [S.Normal] (n : ℕ)
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    (inflationIso_dimensionShiftUp A n hcd).hom =
      (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S (n + 1)).f :=
  (rfl)

/-- 特例：`H¹(G ⧸ S, C^S) ≅ H¹(G, C)`（`∂₂` 的 `i = 2` 段）。 -/
noncomputable def inflationIso_dimensionShiftUp_oneH (A : Rep k G)
    {S : Subgroup G} [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    groupCohomology ((Rep.dimensionShiftUp A).quotientToInvariants S) 1 ≅
      groupCohomology (Rep.dimensionShiftUp A) 1 :=
  inflationIso_dimensionShiftUp A 0 hcd

/-- ★ **`∂₂` 的前半**：`H²(G,A) ≅ H¹(G, C) ≅ H¹(G ⧸ S, C^S)`
（维数平移 `Hyp227` ＋ inflation 本轮）。GS 6.8.5 的 (1)+(2)。 -/
noncomputable def deltaTwo_firstHalf (A : Rep k G) {S : Subgroup G} [S.Normal]
    (hcd : ∀ k' : ℕ, 2 ≤ k' → IsZero (groupCohomology (Rep.res S.subtype A) k')) :
    groupCohomology A 2 ≅ groupCohomology ((Rep.dimensionShiftUp A).quotientToInvariants S) 1 :=
  (coindBot_dimensionShift_two A).symm.trans (inflationIso_dimensionShiftUp_oneH A hcd).symm

end L20261018

#print axioms L20261018.isIso_HInfRes_dimensionShiftUp
#print axioms L20261018.inflationIso_dimensionShiftUp
#print axioms L20261018.inflationIso_dimensionShiftUp_oneH
#print axioms L20261018.deltaTwo_firstHalf
