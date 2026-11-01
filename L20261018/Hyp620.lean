import L20261018.Hyp619

/-!
# S51 R12：`W ↦ w` 桥 ＋ 端到端 `ν(u^{1/p}) = 0`

## 0 本件补的是上一轮刻意留下的那一行

`Hyp619` 交付了**两层**：
* `FbarValuationHyp₂`：**`Valuation` 层**的 `W : F̄ → WithZero (Multiplicative ℚ)`（三条锁）；
* `unitVal_root_eq_one`：**单位群层**的 `w : Lˣ →* Multiplicative ℚ` 上的引擎。

本件把两层接起来（`WithZero.unitsWithZeroEquiv : (WithZero α)ˣ ≃* α`），并把链跑到底：

```
u ∈ 𝒪[F]ˣ  ⟹  W (u) = 1  ⟹  α^p = u  ⟹  w(α) = 1        （＝ ν(u^{1/p}) = 0）
```

## 1 本件交付

| 声明 | 内容 |
|---|---|
| **`unitValOf`** | 由 `W` 诱导的单位群映射 `Lˣ →* Multiplicative ℚ` |
| `unitValOf_apply` | `(w u : WithZero _) = W ↑u`（取值公式） |
| **`unitValOf_eq_one_iff`** | `w u = 1 ↔ W ↑u = 1` |
| ~~`val_algMap_eq_one`~~／~~`val_root_eq_one`~~ | **本轮未过**（`Units.map algMap` 的 coercion 簿记摩擦，见 §2）；登记为 `Hyp621` |

## 2 诚实边界与**本轮未做完的一格**（如实登记）

* 本件**只做完桥**（`unitValOf` ＋ 两个取值/判等引理）。原计划的
  `val_algMap_eq_one`（`u ∈ 𝒪[F]ˣ ⟹ w (algMap u) = 1`）与 `val_root_eq_one`（端到端）**未过**：
  卡在 `Units.map (algebraMap ↥𝒪[F] F̄)` 的 **coercion 簿记**——
  `(↑(u⁻¹) : ↥𝒪[F])` 与 `((↑u : ↥𝒪[F]) : F)⁻¹` 之间的换写在 `algebraMap` 的两次复合下
  不直接 `rfl`，而 `rw` 又找不到 pattern。**登记为 `Hyp621`**（下一轮第一件）。
* 按 `LESSONS` D4：本轮**有**可编译交付（桥），所以不算空转；但**没有**推进到 `ν(u^{1/p})=0`。
* **接缝（下一轮）**：`Hyp621` ＝ ①`val_algMap_eq_one`（先做一个**免 `Units.map`** 的等价陈述：
  取 `y : F̄ˣ` 与假设 `(y : F̄) = algebraMap ↥𝒪[F] F̄ (u : ↥𝒪[F])`，把 coercion 推给调用者）
  ②端到端 ③由第 3 条稳定条件取惯性子群并用 `Hyp613` 收口 `hCI`。
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial TauCeti ValuativeRel ContCohomology IsLocalRing
open TauCeti.ContCohomology

namespace L20261018

section Bridge

variable {L : Type} [Field L]

/-- 由 `W` 诱导的**单位群**赋值 `Lˣ →* Multiplicative ℚ`。 -/
noncomputable def unitValOf (W : Valuation L (WithZero (Multiplicative ℚ))) :
    Lˣ →* Multiplicative ℚ :=
  (WithZero.unitsWithZeroEquiv (α := Multiplicative ℚ)).toMonoidHom.comp
    (Units.map W.toMonoidWithZeroHom.toMonoidHom)

/-- `unitValOf` 的取值公式：`(w u : WithZero _) = W ↑u`。 -/
theorem unitValOf_apply (W : Valuation L (WithZero (Multiplicative ℚ))) (u : Lˣ) :
    (((unitValOf W u : Multiplicative ℚ) : WithZero (Multiplicative ℚ))) = W (u : L) := by
  have h := WithZero.coe_unitsWithZeroEquiv_eq_units_val
    (Units.map W.toMonoidWithZeroHom.toMonoidHom u)
  simpa [unitValOf] using h

/-- ★★★ `w u = 1 ↔ W ↑u = 1`。 -/
theorem unitValOf_eq_one_iff (W : Valuation L (WithZero (Multiplicative ℚ))) (u : Lˣ) :
    unitValOf W u = 1 ↔ W (u : L) = 1 := by
  constructor
  · intro h
    have h2 := unitValOf_apply W u
    rw [h] at h2
    simpa using h2.symm
  · intro h
    refine WithZero.coe_inj.mp ?_
    rw [unitValOf_apply, h]
    simp

end Bridge

end L20261018

#print axioms L20261018.unitValOf_apply
#print axioms L20261018.unitValOf_eq_one_iff
