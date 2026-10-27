import L20261018.Hyp36
/-!
# 缺口 1 的核心域论：第一槽是 `p` 次幂时，`K(a^{1/p}) = K`

`(f)` 剩下的具名假设 `[[hyp-symbol-cup]]` 的内容是
`[(a,b)_F] = (a) ∪ (b)`（GS2017 `cor-cyclic-special-presentations` ＋
`prop-cyclic-algebra-galois-symbol`）。但 `(f)` 只用到它的**一个特例**：

> `a ∈ E^{×p}` ⟹ 符号代数 `(a,b)_E` 分裂。

而按 GS 的**循环代数**定义 `(a,b)_K = (K(a^{1/p})/K, σ, b)`，这一特例是**域的平凡性**：

> 若 `a = α ^ p`（`α ∈ K^×`）且 `K` 含本原 `p` 次单位根，则 `a` 的**每个** `p` 次根都在 `K` 里，
> 故 `K(a^{1/p}) = K`，扩张平凡，符号代数没有非平凡的分量。

本文件把这条域论事实机检化。它是 `[[hyp-symbol-cup]]` 残余里**唯一与「符号」有关**的数学内容；
剩下的是 `cyclicClass → TwoCocycle` 的翻译（纯基建）。

## 主结果

* `SymbolAlg.mem_bot_of_pow_eq_one`：`y ^ p = 1` 在可分闭包中 ⟹ `y ∈ K`
  （`K` 已含本原 `p` 次单位根，故所有 `p` 次单位根都在 `K` 里）。
* `SymbolAlg.adjoin_rootSet_eq_bot_of_isPow`：**`a ∈ (K^×)^p` ⟹ `K(a^{1/p}) = K`**。
-/

open TauCeti

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace SymbolAlg

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

/-- **`p` 次单位根都在 `K` 里。** 若 `y` 在可分闭包中满足 `y ^ p = 1`，则 `y` 是 `K` 的像：
`K` 含本原 `p` 次单位根 `ζ`，而 `p` 次单位根群由它生成。 -/
theorem mem_bot_of_pow_eq_one {y : SeparableClosure K} (hy : y ^ p = 1) :
    y ∈ (⊥ : IntermediateField K (SeparableClosure K)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K p
  have hζ' : IsPrimitiveRoot (algebraMap K (SeparableClosure K) ζ) p :=
    hζ.map_of_injective (algebraMap K (SeparableClosure K)).injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hy
  rw [← hi]
  exact pow_mem (IntermediateField.mem_bot.mpr ⟨ζ, rfl⟩) i

/-- **`a ∈ (K^×)^p` ⟹ `K(a^{1/p}) = K`。** 取 `a = α ^ p`；`a` 的任一 `p` 次根 `x` 满足
`(x / α) ^ p = 1`，故 `x / α ∈ K`（`mem_bot_of_pow_eq_one`），从而 `x ∈ K`。

这是 `[[hyp-symbol-cup]]` 在 `(f)` 中的用法的**全部域论内容**：第一槽成为 `p` 次幂时，
符号代数所在的循环扩张退化为平凡扩张。 -/
theorem adjoin_rootSet_eq_bot_of_isPow {a : Kˣ} (ha : ∃ α : Kˣ, α ^ p = a) :
    IntermediateField.adjoin K
      {x : SeparableClosure K | x ^ p = algebraMap K (SeparableClosure K) (a : K)}
      = ⊥ := by
  obtain ⟨α, hα⟩ := ha
  refine le_antisymm ?_ bot_le
  rw [IntermediateField.adjoin_le_iff]
  rintro x hx
  -- `a` 在可分闭包中的像等于 `α` 的像的 `p` 次幂
  have hα' : algebraMap K (SeparableClosure K) (a : K)
      = (algebraMap K (SeparableClosure K) (α : K)) ^ p := by
    rw [← hα]
    simp
  have hc : algebraMap K (SeparableClosure K) (α : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (SeparableClosure K)).injective).mpr (α : Kˣ).ne_zero
  -- 故 `(x / α) ^ p = 1`
  have hy : (x / algebraMap K (SeparableClosure K) (α : K)) ^ p = 1 := by
    rw [div_pow, hx, hα', div_self (pow_ne_zero p hc)]
  have h1 : x / algebraMap K (SeparableClosure K) (α : K)
      ∈ (⊥ : IntermediateField K (SeparableClosure K)) := mem_bot_of_pow_eq_one hy
  have h2 : algebraMap K (SeparableClosure K) (α : K)
      ∈ (⊥ : IntermediateField K (SeparableClosure K)) :=
    IntermediateField.mem_bot.mpr ⟨(α : K), rfl⟩
  have hx' : x = (x / algebraMap K (SeparableClosure K) (α : K))
      * algebraMap K (SeparableClosure K) (α : K) := (div_mul_cancel₀ x hc).symm
  rw [hx']
  exact mul_mem h1 h2

end SymbolAlg
