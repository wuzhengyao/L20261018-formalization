import L20261018.Ch2.Hensel.TameSymbol.Step011_tame_sum_condition

/-!
# S59 R7：**`res` 构造的两个对象 ＋ 最干净的入口条件**（`Finsupp` 版）

## 为什么把入口条件从 `Fin n` 换成 `Finsupp`

`Hyp685.tameSumCond` 是 `Fin n` 形式；要用它做构造必须先把 `f : (V×V) →₀ k` 的支撑重编号成
`Fin n`（`f.support.equivFin`），多一层易错的搬运。**`Finsupp` 版入口条件与之等价，但直接就是
构造所需的 `ker F ≤ ker G`**：

```
cupLC  cup : ((V × V) →₀ k) →ₗ[k] H2              -- range = span{∪ a b}   （Finsupp.range_linearCombination）
tameLC val : ((V × V) →₀ k) →ₗ[k] ker v̄
tameKernelCond cup val := ∀ f, cupLC cup f = 0 → tameLC val f = 0        （＝ ker (cupLC) ≤ ker (tameLC)）
```

⟹ 下一轮的构造**原样照抄**施工图即可：`hker := tameKernelCond`（本件的 `tameKernelCond_iff_ker_le`）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`cupLC`** | `Finsupp.linearCombination k (fun p => ∪ p.1 p.2)` |
| **`tameLC`** | `Finsupp.linearCombination k (fun p => tameExpr val p.1 p.2)` |
| **`tameKernelCond`** | 谓词（构造的入口） |
| **`tameKernelCond_iff_ker_le`** | ★ 与 `ker (cupLC) ≤ ker (tameLC)` **同一**（构造直接用后者） |

## API 侦察（`#check` 实测，本轮）

| API | 读数 |
|---|---|
| `Finsupp.linearCombination` | ✅ 在库（**旧名 `Finsupp.total` 已不存在**） |
| `Finsupp.range_linearCombination` | ✅ 在库（**旧名 `range_total` 已不存在**） |
| `Submodule.liftQ`／`LinearMap.quotKerEquivRange`／`LinearMap.exists_leftInverse_of_injective` | ✅ 在库 |

## 诚实边界

本件**只定义对象 ＋ 锁定入口**；`tameKernelCond ⟹ TameSymbolFactors`（即 `g`／`proj`／`res` 的组装）
**未做**，是下一轮的唯一内容（`G2-PLAN.md` §A1 的施工图，≈40 行、API 已全部对号）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section FinsuppCond

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- `(a,b) ↦ ∪ a b` 的 `Finsupp` 线性化（其 `range = span{∪ a b}`）。 -/
noncomputable def cupLC (cup : V →ₗ[k] V →ₗ[k] H2) : ((V × V) →₀ k) →ₗ[k] H2 :=
  Finsupp.linearCombination k (fun p : V × V => cup p.1 p.2)

/-- `(a,b) ↦ tame a b` 的 `Finsupp` 线性化。 -/
noncomputable def tameLC (val : V →ₗ[k] k) :
    ((V × V) →₀ k) →ₗ[k] ↥(LinearMap.ker val) :=
  Finsupp.linearCombination k (fun p : V × V => tameExpr val p.1 p.2)

/-- **`res` 构造的入口条件**（`Finsupp` 版）：`ker (cupLC) ≤ ker (tameLC)`。 -/
def tameKernelCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) : Prop :=
  ∀ f : (V × V) →₀ k, cupLC cup f = 0 → tameLC val f = 0

/-- ★ 入口条件的**核包含形态**（构造直接用这一条）。 -/
theorem tameKernelCond_iff_ker_le (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) :
    tameKernelCond cup val
      ↔ LinearMap.ker (cupLC cup) ≤ LinearMap.ker (tameLC val) := by
  constructor
  · intro h f hf
    exact h f (LinearMap.mem_ker.mp hf)
  · intro h f hf
    exact LinearMap.mem_ker.mp (h (LinearMap.mem_ker.mpr hf))

end FinsuppCond

end L20261018

/-! ## 机检读数 -/

#print axioms L20261018.cupLC
#print axioms L20261018.tameLC
#print axioms L20261018.tameKernelCond_iff_ker_le
