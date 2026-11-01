import Hyp608

/-!
# S50 R4：R3 的第一格 —— `ZMod p` 的**平凡作用实例**与固定点系数桥

## 为什么需要这一件

`S50-R2-CARRIER-PLAN.md` §8 的实测读数：`DistribMulAction G (ZMod p)` **不在** mathlib 的
默认实例里（`synthInstanceFailed`）。而 `(CI)`（`S50-R2-CARRIER-PLAN.md` §2）

```
(CI)  ker v̄ = range (infl₁ : H¹(Γ⧸I, μ_p) → H¹(Γ, μ_p))
```

要用的 `explicitInfl1` 的系数是 `↥(FixedPoints.addSubgroup ↥I (ZMod p))`，要把它与 `ZMod p`
对齐就必须先有「`ZMod p` 上 `Γ⧸I` 平凡作用」这个**显式**实例（不能靠实例搜索）。

## 本件交付

| 声明 | 内容 |
|---|---|
| `instTrivialSMulZMod` | `SMul G (ZMod p)` 的平凡作用（**局部实例**，不跨文件） |
| `instTrivialDistribMulActionZMod` | 其 `DistribMulAction` 提升 |
| **`fixedPoints_zmod_eq_top`** | 该作用下 `FixedPoints.addSubgroup G (ZMod p) = ⊤` |
| **`fixedPointsZModEquiv`** | `↥(FixedPoints.addSubgroup G (ZMod p)) ≃+ ZMod p` |

## 诚实边界

* 本件**不含** `H¹` 层的系数桥（`explicitCoeff1` 双向合成）——下一轮。
* 平凡作用实例标 `local`（`S49` §5.4 规则 1：`local instance` 不跨文件，用者须重声明）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti ContCohomology

namespace L20261018

section TrivialAction

variable (G : Type*) [Monoid G]

/-- `ZMod p` 上 `G` 的**平凡** `SMul`。 -/
local instance instTrivialSMulZMod : SMul G (ZMod p) := ⟨fun _ x => x⟩

/-- 其 `DistribMulAction` 提升（全部字段都是 `rfl`）。 -/
local instance instTrivialDistribMulActionZMod : DistribMulAction G (ZMod p) where
  smul := fun _ x => x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

/-- ★★★★ 平凡作用下**每个元素都是固定点**：`μ_p^{G} = μ_p`（子群形态）。 -/
theorem fixedPoints_zmod_eq_top (p : ℕ) :
    FixedPoints.addSubgroup G (ZMod p) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  show (∀ g : G, g • x = x)
  intro g
  rfl

/-- ★★★★★ **固定点系数桥**：`↥(μ_p^{G}) ≃+ ZMod p`（平凡作用）。 -/
noncomputable def fixedPointsZModEquiv (p : ℕ) :
    ↥(FixedPoints.addSubgroup G (ZMod p)) ≃+ ZMod p where
  toFun x := (x : ZMod p)
  invFun x := ⟨x, fun _ => rfl⟩
  left_inv x := by ext; rfl
  right_inv x := rfl
  map_add' x y := rfl

end TrivialAction

end L20261018

#print axioms L20261018.fixedPoints_zmod_eq_top
#print axioms L20261018.fixedPointsZModEquiv
