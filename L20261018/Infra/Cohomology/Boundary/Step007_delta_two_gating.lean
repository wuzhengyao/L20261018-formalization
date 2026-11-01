import L20261018.Infra.Cohomology.Boundary.Step006_delta_two_dimension_shift
import TauCeti.RepresentationTheory.Homological.GroupCohomology.InflationRestriction

/-!
# R1098（**(R2)：抽象侧 `∂₂` 的「门控」—— `H^j(S, C) = 0`**）

## 路线（`PLAN-R2` §H-9）

GS 6.8.5 的 `∂₂`（`i = 2`）＝ 三段复合：**(1)** 维数平移（R1097 ✓）；**(2)** inflation
（`H^{i-1}(G/H, C^H) ≅ H^{i-1}(G,C)`，其**门控**是 `H^j(H,C) = 0`）；**(3)** `C^H → H^1(H,A)`。

**本轮**：把门控 `H^j(S, C) = 0` 造出来（`C = Rep.dimensionShiftUp A = coker(coindBotUnit A)`）。
GS 的推导（tex `:9482–9486`）：「`H^j(H, M^G(A)) = 0` ⟹ 长正合列给 `H^j(H,C) ≅ H^{j+1}(H,A)`，
而后者由 `cd(H) ≤ 1` 为零」。本文件把它机检为**两条零调性 ⟹ 中间项零**：

```
H^j(S, Coind_⊥^G A) = 0  ∧  H^{j+1}(S, A) = 0   ⟹   H^j(S, C) = 0
```

**工具（全库内）**：`Rep.dimensionShiftUpSES_res_shortExact`（短正合列**沿任意 `f : H →* G` 限制后仍短正合**）、
`ShortComplex.ShortExact.mapShortComplex₃_exact`（`H^j(X₂) → H^j(X₃) → H^{j+1}(X₁)` 正合）、
`ShortComplex.Exact.epi_f`、`Limits.IsZero.of_epi`、`Limits.IsZero.eq_zero_of_tgt`。

| 声明 | 内容 |
|---|---|
| **`isZero_res_dimensionShiftUp`** | ★ `H^j(S,C) = 0`（由 `H^j(S, coindBot) = 0` ＋ `H^{j+1}(S,A) = 0`） |
| **`isZero_res_dimensionShiftUp_one`** | 特例 `H^1(S,C) = 0`（由 `H^2(S,A) = 0`；`cd(S) ≤ 1` 的情形） |
| **`isZero_res_dimensionShiftUp_of_cd`** | `∀ j ≥ 1`, `H^j(S,C) = 0`（由 `∀ k ≥ 2, H^k(S,A) = 0`，即 `cd(S) ≤ 1` 的**抽象形式**） |
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory Limits TauCeti

namespace L20261018

variable {k G : Type} [CommRing k] [Group G]

/-- ★ **门控**：`H^j(S, C) = 0`，其中 `C = Rep.dimensionShiftUp A`，前提是
`H^j(S, Coind_⊥^G A) = 0`（`Hyp226`）与 `H^{j+1}(S, A) = 0`（`cd(S) ≤ 1`）。

GS 6.8.5（tex `:9482–9486`）的「`H^j(H,C) = 0`」即此。 -/
theorem isZero_res_dimensionShiftUp (A : Rep k G) (S : Subgroup G) (j : ℕ)
    (hM : IsZero (groupCohomology (Rep.res S.subtype (Rep.coindBot k G A.V)) j))
    (hA : IsZero (groupCohomology (Rep.res S.subtype A) (j + 1))) :
    IsZero (groupCohomology (Rep.res S.subtype (Rep.dimensionShiftUp A)) j) := by
  -- 限制后的短正合列仍短正合
  have hex : ((Rep.dimensionShiftUpSES A).map (Rep.resFunctor S.subtype)).ShortExact :=
    Rep.dimensionShiftUpSES_res_shortExact A S.subtype
  -- `H^j(X₂) → H^j(X₃) → H^{j+1}(X₁)` 正合；左端为零 ⟹ 第一个箭头为 `0` ⟹ 第二个箭头单射
  exact @IsZero.of_mono _ _ _ _ _
    (groupCohomology.mapShortComplex₃ hex (i := j) (j := j + 1) rfl).g
    ((groupCohomology.mapShortComplex₃_exact hex (i := j) (j := j + 1) rfl).mono_g
      (hM.eq_zero_of_src _)) hA

/-- 特例：`H^1(S, C) = 0`（由 `H^2(S, A) = 0`；即 `cd(S) ≤ 1` 时 `j = 1` 的情形）。 -/
theorem isZero_res_dimensionShiftUp_one (A : Rep k G) (S : Subgroup G)
    (hA : IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    IsZero (groupCohomology (Rep.res S.subtype (Rep.dimensionShiftUp A)) 1) :=
  isZero_res_dimensionShiftUp A S 1
    (by
      have := groupCohomology.isZero_res_coindBot_succ (k := k) (G := G) S A.V 0
      simpa using this)
    hA

/-- ★ **`cd(S) ≤ 1` 的抽象形式**：若 `H^k(S,A) = 0` 对一切 `k ≥ 2` 成立，则
`H^j(S, C) = 0` 对一切 `j ≥ 1` 成立（`C = Rep.dimensionShiftUp A`）。 -/
theorem isZero_res_dimensionShiftUp_of_cd (A : Rep k G) (S : Subgroup G)
    (hcd : ∀ k : ℕ, 2 ≤ k → IsZero (groupCohomology (Rep.res S.subtype A) k)) :
    ∀ j : ℕ, 1 ≤ j → IsZero (groupCohomology (Rep.res S.subtype (Rep.dimensionShiftUp A)) j) := by
  intro j hj
  refine isZero_res_dimensionShiftUp A S j ?_ (hcd (j + 1) (by omega))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact groupCohomology.isZero_res_coindBot_succ (k := k) (G := G) S A.V m

end L20261018

#print axioms L20261018.isZero_res_dimensionShiftUp
#print axioms L20261018.isZero_res_dimensionShiftUp_one
#print axioms L20261018.isZero_res_dimensionShiftUp_of_cd
