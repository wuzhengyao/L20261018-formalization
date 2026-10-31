import Hyp195

/-!
# R1049（**S29 · ④.1 第三步的零件**）：消去 `s` ＋ 拆末项 ＋ 下标重排

极小性论证（④.1）的最后一步要把「`c₀ ∈ 𝔪`」变成「指数降一」：

```
sⁿ·x = Σ_{i<p} cᵢ sⁱ,  c₀ = π·c₀'   ⟹   s^{n−1}·x = Σ_{j<p} c'ⱼ sʲ
```

本文件机检其中的**三个纯代数零件**：

| 声明 | 内容 |
|---|---|
| **`sum_range_split_last`** | 一般 `F`-代数：`∑_{j<p} aⱼ sʲ = (∑_{j<p−1} aⱼ sʲ) + a_{p−1} • s^{p−1}` |
| **`root_mul_eq_zero_iff`** | **`s · z = 0 ↔ z = 0`**（`s` 是非零因子：`sᵖ = π ≠ 0`） |
| `root_mul_left_cancel` | `s · a = s · b → a = b` |
| **`sumCoeff_eq_root_mul`** | **`Σ_{i<p} cᵢ sⁱ = s · Σ_{j<p} c'ⱼ sʲ`**，其中 `c'ⱼ = c₀`（`j = p−1`）／`c (j+1)` |

## 关键点

* **消去 `s` 不需要 `NoZeroDivisors`**：乘上 `s^{p−1}` 即得 `sᵖ z = of π · z = 0`，而 `of π` 是**单位**
  （`π ≠ 0` ⟹ `algebraMap π` 可逆）⟹ `z = 0`。这条绕开了「`Xᵖ − π` 不可约／`L` 是域」这类额外假设。
* **`sum_range_split_last` 必须对一般 `s : A` 陈述**（同 `Hyp195` 的教训）：模型里 `s` 的定义含 `p`，
  对它 `conv_lhs => rw [show p = (p−1)+1 from …]` 会报 `Motive is dependent`。
* **重排的末项**：`s · (c₀ • s^{p−1}) = c₀ • sᵖ = algebraMap (c₀) * algebraMap (π) = algebraMap (c₀·π)`
  `= algebraMap (c 0)`（`c 0 = b·c₀`、`(b:F) = (π:F)`）—— 这正是「`c₀ ∈ 𝔪` 时提出一个 `s`」的代数内容。
-/

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section SumRangeSplitLast

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]
variable {A : Type} [CommRing A] [Algebra F A]

/-- **拆末项**（一般 `F`-代数）：`∑_{j<p} aⱼ sʲ = (∑_{j<p−1} aⱼ sʲ) + a_{p−1} • s^{p−1}`。 -/
theorem sum_range_split_last (s : A) (a : ℕ → F) :
    (∑ j ∈ Finset.range p, a j • s ^ j)
      = (∑ j ∈ Finset.range (p - 1), a j • s ^ j) + a (p - 1) • s ^ (p - 1) := by
  have hp2 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
  conv_lhs => rw [← hp2]
  rw [Finset.sum_range_succ]

end SumRangeSplitLast

section Cancellation

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`s` 是非零因子**：`s · z = 0 ↔ z = 0`。

乘 `s^{p−1}` 得 `sᵖ z = of π · z = 0`，而 `of π` 可逆（`π ≠ 0`）。 -/
theorem root_mul_eq_zero_iff (π : Fˣ) {z : AdjoinRoot (X ^ p - C (π : F))} :
    (AdjoinRoot.root (X ^ p - C (π : F))) * z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    have h1 : (AdjoinRoot.root (X ^ p - C (π : F))) ^ p * z = 0 := by
      calc (AdjoinRoot.root (X ^ p - C (π : F))) ^ p * z
          = ((AdjoinRoot.root (X ^ p - C (π : F))) ^ (p - 1)
              * (AdjoinRoot.root (X ^ p - C (π : F)))) * z := by
            rw [← pow_succ, Nat.sub_add_cancel hp1]
        _ = (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p - 1)
              * ((AdjoinRoot.root (X ^ p - C (π : F))) * z) := by
            rw [mul_assoc]
        _ = 0 := by rw [hz, mul_zero]
    rw [root_pow_eq_of] at h1
    have hunit : IsUnit (AdjoinRoot.of (X ^ p - C (π : F)) (π : F)) :=
      (isUnit_iff_ne_zero.mpr (Units.ne_zero π)).map (AdjoinRoot.of (X ^ p - C (π : F)))
    exact (IsUnit.mul_right_eq_zero hunit).mp h1
  · rintro rfl
    rw [mul_zero]

/-- **左消去**：`s · a = s · b → a = b`。 -/
theorem root_mul_left_cancel (π : Fˣ) {a b : AdjoinRoot (X ^ p - C (π : F))}
    (h : (AdjoinRoot.root (X ^ p - C (π : F))) * a
      = (AdjoinRoot.root (X ^ p - C (π : F))) * b) : a = b := by
  have h' : (AdjoinRoot.root (X ^ p - C (π : F))) * (a - b) = 0 := by
    rw [mul_sub, h, sub_self]
  exact sub_eq_zero.mp ((root_mul_eq_zero_iff (F := F) p π).mp h')

end Cancellation

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **下标重排（提出一个 `s`）**：若 `c 0 = b · c₀`（`b` 是 `π` 的像），则

```
Σ_{i<p} cᵢ sⁱ  =  s · Σ_{j<p} c'ⱼ sʲ ,   c'ⱼ = c₀ (j = p−1) ／ c (j+1) (否则)
``` -/
theorem sumCoeff_eq_root_mul (π : Fˣ) {b : ↥𝒪[F]} (hb : (b : F) = (π : F)) {c : ℕ → ↥𝒪[F]}
    {c₀ : ↥𝒪[F]} (hc0 : c 0 = b * c₀) :
    sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))
      = (AdjoinRoot.root (X ^ p - C (π : F)))
        * sumCoeff (F := F) p π
            (fun j => ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)) := by
  classical
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsp : (AdjoinRoot.root (X ^ p - C (π : F))) ^ p
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) ((π : F)) := by
    rw [root_pow_eq_of]; rfl
  have hsc : (AdjoinRoot.root (X ^ p - C (π : F)))
      * (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p - 1)
      = (AdjoinRoot.root (X ^ p - C (π : F))) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  -- 左端：拆首项 ＋ 提出 `s`
  have hL : sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) (((c 0 : ↥𝒪[F]) : F))
        + (AdjoinRoot.root (X ^ p - C (π : F)))
          * (∑ i ∈ Finset.range (p - 1),
              (((c (i + 1) : ↥𝒪[F]) : F)) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ i) := by
    rw [← sum_range_eq_sumCoeff (F := F) p π (fun i => ((c i : ↥𝒪[F]) : F))]
    exact sum_range_split (F := F) p (AdjoinRoot.root (X ^ p - C (π : F)))
      (fun i => ((c i : ↥𝒪[F]) : F))
  -- 右端：拆末项
  have h0 : (∑ j ∈ Finset.range (p - 1),
        ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)
          • (AdjoinRoot.root (X ^ p - C (π : F))) ^ j)
      = (∑ j ∈ Finset.range (p - 1),
          (((c (j + 1) : ↥𝒪[F]) : F)) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≠ p - 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [show ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)
        = ((c (j + 1) : ↥𝒪[F]) : F) from by simp [hj']]
  have h1 : ((if p - 1 = p - 1 then c₀ else c (p - 1 + 1) : ↥𝒪[F]) : F)
      = ((c₀ : ↥𝒪[F]) : F) := by simp
  have hsum : sumCoeff (F := F) p π
        (fun j => ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F))
      = (∑ j ∈ Finset.range (p - 1),
          (((c (j + 1) : ↥𝒪[F]) : F)) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ j)
        + ((c₀ : ↥𝒪[F]) : F) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p - 1) := by
    rw [← sum_range_eq_sumCoeff (F := F) p π
      (fun j => ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)),
      sum_range_split_last (F := F) p (AdjoinRoot.root (X ^ p - C (π : F)))
        (fun j => ((if j = p - 1 then c₀ else c (j + 1) : ↥𝒪[F]) : F)), h0, h1]
  -- 末项：`s * (c₀ • s^{p−1}) = algebraMap (c 0)`
  have hlast : (AdjoinRoot.root (X ^ p - C (π : F)))
      * ((((c₀ : ↥𝒪[F]) : F)) • (AdjoinRoot.root (X ^ p - C (π : F))) ^ (p - 1))
      = algebraMap F (AdjoinRoot (X ^ p - C (π : F))) (((c 0 : ↥𝒪[F]) : F)) := by
    rw [Algebra.mul_smul_comm, hsc, hsp, Algebra.smul_def, ← map_mul]
    congr 1
    rw [hc0]
    push_cast
    rw [hb]
    ring
  rw [hL, hsum, mul_add, hlast,
    add_comm (algebraMap F (AdjoinRoot (X ^ p - C (π : F))) (((c 0 : ↥𝒪[F]) : F)))]

end Split

end L20261018

#print axioms L20261018.sum_range_split_last
#print axioms L20261018.root_mul_eq_zero_iff
#print axioms L20261018.root_mul_left_cancel
#print axioms L20261018.sumCoeff_eq_root_mul
