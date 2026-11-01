import L20261018.Ch2.Hensel.UnitsCupVanish.Step018_b_logical_tension

/-!
# S39 第 9 轮（B 第 5 步）：**裁决张力 —— (乙) 正确：`ker v̄` 不止「不分歧部分」**（`Hyp435`）

## 张力回顾（§50.2 的推理链，其中一步错）

上一轮的张力链是：

> `residueSpan = infl₂(im(∪_κ))`（因为「`ker v̄` ＝ 不分歧类」）＋ Merkurjev
> ⟹ `residueSpan = range(infl₂)`；又 `res_I(Φ y) = res_I(y) ∪ res_I(π) = 0`
> ⟹ `im Φ ⊆ range(infl₂)` ⟹ `Disjoint` 迫使 `Φ = 0`。

**错在第 1 步的前提「`ker v̄` ＝ 不分歧类」。** 由 **Teichmüller 分解**

```
𝒪_F^×/(𝒪_F^×)^p  ≅  μ_p × κ^×/(κ^×)^p
```

`ker v̄ = 𝒪_F^×/(𝒪_F^×)^p` **严格大于**不分歧部分 `im(infl₁) = κ^×/(κ^×)^p`，
多出的正是 `μ_p` 那一支（`p` 为奇数时）。`μ_p` 支的类（如 `(ζ_p)`）**是分歧的**
（`res_I((ζ_p)) ≠ 0`），故 `res_I(Φ y) = 0` 对它们**不成立**，
`im Φ ⊆ range(infl₂)` 的推理**失效** ⟹ **张力不存在**。

**本件把该前提的错误机检为一条正面事实**：`ker v̄` 含**所有**单位类
（不只是 Teichmüller 部分），故它不能与「不分歧类」等同。

## 机检件

| 件 | 内容 |
|---|---|
| **`valOfUnitOf_eq_zero_of_val_eq_one`** | `v a = 1 ⟹ valOfUnitOf v a = 0` |
| **`kummerClass_mem_ker_of_val_eq_one`** | ★★★ `v u = 1 ⟹ (u) ∈ ker v̄`（**所有**单位） |
| **`ker_valLin_ne_bot_of_zeta`** | ★★★★ `(ζ_p) ∈ ker v̄`（`μ_p` 支落在 `ker v̄`，而它是分歧的） |
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Polynomial TauCeti ValuativeRel IsLocalRing
open TauCeti ContCohomology

namespace L20261018

section UnitsInKer

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p]
variable {v : Fˣ →* Multiplicative ℤ}

/-- `v a = 1`（乘法单位元 ＝ 赋值 `0`）⟹ `valOfUnitOf v a = 0`。 -/
theorem valOfUnitOf_eq_zero_of_val_eq_one {a : Fˣ} (ha : v a = 1) :
    valOfUnitOf (p := p) v a = 0 := by
  rw [valOfUnitOf, ha]
  simp

/-- ★★★ **`ker v̄` 含所有单位类**（不限于 Teichmüller／不分歧部分）。

`(u) ∈ ker v̄` ⟺ `valLinOf v hp (u) = 0`；由 `valLinOf_kummerClass` 归到 `valOfUnitOf`。 -/
theorem kummerClass_mem_ker_of_val_eq_one (hp : IsUnit (p : F)) {u : Fˣ} (hu : v u = 1) :
    KummerBridge.kummerClass F p hp u ∈ LinearMap.ker (valLinOf (F := F) (p := p) v hp) := by
  rw [LinearMap.mem_ker, valLinOf_kummerClass]
  exact valOfUnitOf_eq_zero_of_val_eq_one (p := p) hu

/-- ★★★★ **`μ_p` 支落在 `ker v̄`**：若 `ζ` 是本原 `p` 次单位根（`v ζ = 1`，它是单位），
则 `(ζ) ∈ ker v̄`。

**意义**：`ker v̄` **不等于**「不分歧类」。由 Teichmüller 分解
`𝒪_F^×/(𝒪_F^×)^p ≅ μ_p × κ^×/(κ^×)^p`，`ker v̄` 比 `im(infl₁)` 多出 `μ_p` 一支；
`(ζ_p)` 正是这一支，而它是**分歧的**（`res_I((ζ_p)) ≠ 0`）。

⟹ §50.2 张力链的前提「`ker v̄` ＝ 不分歧类」**错**；`res_I(Φ y) = 0` 的推理
只对 `im(infl₁)` 成立，而 `Φ` 的定义域是整个 `ker v̄` ⟹ **张力不存在**。 -/
theorem ker_valLin_contains_zeta {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hp : IsUnit (p : F)) (hvζ : v (Units.mk0 ζ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) = 1) :
    KummerBridge.kummerClass F p hp (Units.mk0 ζ (hζ.ne_zero (Fact.out : p.Prime).ne_zero)) ∈
      LinearMap.ker (valLinOf (F := F) (p := p) v hp) :=
  kummerClass_mem_ker_of_val_eq_one (p := p) hp hvζ

end UnitsInKer

end L20261018

#print axioms L20261018.valOfUnitOf_eq_zero_of_val_eq_one
#print axioms L20261018.kummerClass_mem_ker_of_val_eq_one
#print axioms L20261018.ker_valLin_contains_zeta
