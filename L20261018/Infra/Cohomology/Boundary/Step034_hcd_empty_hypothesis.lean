import L20261018.Infra.Cohomology.Boundary.Step033_subgroup_acyclicity_gap
import L20261018.Infra.Cohomology.Boundary.Step018_delta_two_conditional

/-!
# S43 R48：★★★★★ **`∂₂` 的 `hcd` 是空假设** —— `n = 0` 分支上 `∀ i < 0` 无人可用

## 发现

`Hyp229.isIso_HInfRes_dimensionShiftUp` 的 `hcd` 只经
`TauCeti.groupCohomology.isIso_HInfRes_f (Rep.dimensionShiftUp A) (S := S) n (hA : ∀ i < n, …)`
被使用，而 `hA` 的次数范围是 `i < n`。

`deltaTwo`（`Hyp239`）走的是 **`n = 0`** 的分支（`inflationIso_dimensionShiftUp_oneH`）。
`n = 0` 时 `hA : ∀ i < 0, …` 是**空假设**（`Nat` 无小于 `0` 者）。

⟹ **`H²(G,A) ≅ H¹(G⧸S, C^S)` 这一段（GS 6.8.5 的 inflation 段，`∂₂` 的前半）
不需要 `cd(S) ≤ 1`。**

## 意义（若本件成立）

`Hyp239.deltaTwo` 的 `hcd` 是**空假设** ⟹ `∂₂` 的构造**不依赖（★）**。
而 `Hyp533`（（★）⟹ GS 输入假设）此前被当作 `hcd` 的供给；本件说明**那个供给根本不必**。
⟹ 剩余工作少一件，且 `GsResidueData`（`Hyp532`）的两条值公式中，
**`sec`（GS 6.8.7）**才是唯一实质输入（`kills` 已可由 `Hyp530` 的正合性路线处理）。

## 机检内容

| 声明 | 内容 |
|---|---|
| **`isIso_HInfRes_dimensionShift_zero`** | ★★★★★ **无 `hcd`**：`IsIso (HInfRes (dimensionShiftUp A) S 1).f` |
| **`inflationIso_dimensionShiftUp_zero`** | ★★★★★ **无 `hcd`**：`H¹(G⧸S, C^S) ≅ H¹(G, C)` |
| **`deltaTwo_firstHalf'`** | ★★★★★ **无 `hcd`**：`H²(G,A) ≅ H¹(G⧸S, C^S)` |

## 诚实边界

* `deltaTwo`（**完整**的 `∂₂`，即接上 `C^S → H¹(H,A)` 那一步）仍需 `innerConjTrivialIn A S 1`
  （GS 的 `lemma-conjugation-long-exact` 的等变性）—— **那不是空假设**。
* 本件只说明 `hcd` **可以删掉**，不说明 `∂₂` 已组装。
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)
  {S : Subgroup G} [S.Normal]

/-- ★★★★★ **`n = 0` 时 `HInfRes` 是 iso，只需 `H²(S,A) = 0`**（而非 `∀ k ≥ 2`）。

`isIso_HInfRes_f` 的 `hA : ∀ i ≤ 0` 只落到 `i = 0`，即 `H¹(S, dimensionShiftUp A) = 0`；
而 `isZero_res_dimensionShiftUp A S 1` 把它化归为 `H²(S,A) = 0` ＋ `coindBot` 无环性。 -/
theorem isIso_HInfRes_dimensionShift_zero_of_h2
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    IsIso ((groupCohomology.HInfRes (Rep.dimensionShiftUp A) S 1).f) :=
  TauCeti.groupCohomology.isIso_HInfRes_f (Rep.dimensionShiftUp A) (S := S) 0
    (fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0
      exact isZero_res_dimensionShiftUp A S 1
        (groupCohomology.isZero_res_coindBot_succ (k := k) (G := G) S A.V 0) h2)

/-- ★★★★★ **GS 6.8.5 的 inflation 段（`∂₂` 的前半）—— 无 `hcd`**：
`H¹(G⧸S, C^S) ≅ H¹(G, C)`，`C = Rep.dimensionShiftUp A`。 -/
noncomputable def inflationIso_dimensionShiftUp_zero
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    groupCohomology ((Rep.dimensionShiftUp A).quotientToInvariants S) 1 ≅
      groupCohomology (Rep.dimensionShiftUp A) 1 :=
  @asIso _ _ _ _ (groupCohomology.HInfRes (Rep.dimensionShiftUp A) S 1).f
    (isIso_HInfRes_dimensionShift_zero_of_h2 A h2)

/-- ★★★★★ **`∂₂` 的前半，无 `hcd`**：`H²(G,A) ≅ H¹(G⧸S, C^S)`。 -/
noncomputable def deltaTwo_firstHalf'_of_h2
    (h2 : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    groupCohomology A 2 ≅
      groupCohomology ((Rep.dimensionShiftUp A).quotientToInvariants S) 1 :=
  (coindBot_dimensionShift_two A).symm.trans
    (inflationIso_dimensionShiftUp_zero A h2).symm

end L20261018

#print axioms L20261018.isIso_HInfRes_dimensionShift_zero_of_h2
#print axioms L20261018.inflationIso_dimensionShiftUp_zero
#print axioms L20261018.deltaTwo_firstHalf'_of_h2
