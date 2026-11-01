import L20261018.Hyp194

/-!
# R1048（**S29 · ④.1 第三步的核心重排**）：拆首项 ＋ 提出一个 `s`

整性判据的最后一步要把 `s`-展开的**常数项**换成 `sᵖ·c₀' = s·(s^{p−1}c₀')`，从而**提出一个 `s`**、
把指数从 `n+1` 降到 `n`。本文件机检这一步的纯代数核心：

```
∑_{i<p} aᵢ sⁱ  =  a₀ + s · ∑_{i<p−1} a_{i+1} sⁱ
```

⚠️ **必须对一般 `s : A` 陈述**：在模型里 `s = AdjoinRoot.root (X^p − Cπ)` 的**定义含 `p`**，
若直接对模型 `s` 用 `conv_lhs => rw [← (p−1)+1 = p]`，会因 `s` 依赖 `p` 而报
「Motive is dependent」。故先做一般版，再实例化。

| 声明 | 内容 |
|---|---|
| **`sum_range_split`** | 一般 `F`-代数 `A` 中的上式 |
| **`sum_range_split_adjoinRoot`** | 模型 `A = AdjoinRoot_F(X^p − Cπ)`、`s = root` 的实例 |
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section SumRangeSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {A : Type} [CommRing A] [Algebra F A]

/-- **拆首项并提出一个 `s`**（一般 `F`-代数）：`∑_{i<p} aᵢ sⁱ = a₀ + s · ∑_{i<p−1} a_{i+1} sⁱ`。 -/
theorem sum_range_split (s : A) (a : ℕ → F) :
    (∑ i ∈ Finset.range p, a i • s ^ i)
      = algebraMap F A (a 0) + s * (∑ i ∈ Finset.range (p - 1), a (i + 1) • s ^ i) := by
  have hp : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
  conv_lhs => rw [← hp]
  rw [Finset.sum_range_succ']
  have hstep : (∑ k ∈ Finset.range (p - 1), a (k + 1) • s ^ (k + 1))
      = (∑ k ∈ Finset.range (p - 1), a (k + 1) • s ^ k) * s := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ, ← smul_mul_assoc]
  rw [hstep, pow_zero, ← Algebra.algebraMap_eq_smul_one, mul_comm, add_comm]

end SumRangeSplit

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- 模型实例：`s = AdjoinRoot.root (X^p − Cπ)`。 -/
theorem sum_range_split_adjoinRoot (π : Fˣ) (a : ℕ → F) :
    (∑ i ∈ Finset.range p, a i • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i)
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) (a 0)
        + (AdjoinRoot.root (X ^ p - C (π : F)))
          * (∑ i ∈ Finset.range (p - 1),
              a (i + 1) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i) :=
  sum_range_split (F := F) p (AdjoinRoot.root (X ^ p - C (π : F))) a

end Model

end L20261018

#print axioms L20261018.sum_range_split
#print axioms L20261018.sum_range_split_adjoinRoot
