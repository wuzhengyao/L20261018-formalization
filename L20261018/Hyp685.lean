import L20261018.Hyp684

/-!
# S59 R6：**`res` 构造的正确入口条件** —— `tameSumCond`（带标量的有限和）

## 定位

构造 `res : H2 →ₗ ker v̄` 的**唯一**输入是「`span{∪ a b}` 上良定义」。`Finsupp` 化之后它恰好是：

```
F := Finsupp.total (V × V) H2 k (fun p => ∪ p.1 p.2)     -- range F = span{∪ a b}
G := Finsupp.total (V × V) (ker v̄) k (fun p => tame p.1 p.2)
构造 res 需要  ker F ≤ ker G  ⟺  tameSumCond（本件的 def：带标量的有限和）
```

本件交该谓词 ＋ 两条蕴含；**构造 `res` 本身**（`Submodule.liftQ` ＋ `LinearMap.quotKerEquivRange`
＋ `LinearMap.exists_leftInverse_of_injective`）留给下一轮，五件 API 已点名（见 `G2-PLAN.md` §A1）。

## 机检件

| 声明 | 内容 |
|---|---|
| **`tameSumCond`** | 谓词：`∑ cᵢ • ∪(aᵢ)(bᵢ) = 0 ⟹ ∑ cᵢ • tame(aᵢ)(bᵢ) = 0`（**带标量**，即 `ker F ≤ ker G`） |
| **`tameSumCond_of_tameSymbolFactors`** | ★ 易向（`map_sum` ＋ `map_smul`） |
| **`tameChainCond_of_tameSumCond`** | ★ 链式判据（`n = 2`）是它的特例 |

## 诚实边界

**不**证 `TameSymbolFactors`；本件只把它的**唯一入口条件**固定成 `tameSumCond`。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing

namespace L20261018

section SumCond

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {H2 : Type*} [AddCommGroup H2] [Module k H2]

/-- **`res` 构造的入口条件**（带标量的有限和；即 `Finsupp.total` 两像的核包含）。 -/
def tameSumCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k) : Prop :=
  ∀ (n : ℕ) (c : Fin n → k) (as bs : Fin n → V),
    (∑ i, c i • cup (as i) (bs i)) = 0 →
      (∑ i, c i • tameExpr val (as i) (bs i)) = 0

theorem tameSumCond_of_tameSymbolFactors (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : TameSymbolFactors cup val) : tameSumCond cup val := by
  obtain ⟨res, hres⟩ := h
  intro n c as bs hsum
  have h1 : res (∑ i, c i • cup (as i) (bs i))
      = ∑ i, c i • tameExpr val (as i) (bs i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hres]
  rw [hsum, map_zero] at h1
  exact h1.symm

/-- ★ 链式判据（`n = 2`，`c = 1`）是 `tameSumCond` 的特例。 -/
theorem tameChainCond_of_tameSumCond (cup : V →ₗ[k] V →ₗ[k] H2) (val : V →ₗ[k] k)
    (h : tameSumCond cup val) : tameChainCond cup val := by
  intro a b a' b' hsum
  have h2 := h 2 (fun _ => 1) ![a, a'] ![b, b'] ?_
  · simpa [Fin.sum_univ_two] using h2
  · simpa [Fin.sum_univ_two] using hsum

end SumCond

end L20261018

/-! ## 机检读数 -/

#print axioms L20261018.tameSumCond_of_tameSymbolFactors
#print axioms L20261018.tameChainCond_of_tameSumCond
