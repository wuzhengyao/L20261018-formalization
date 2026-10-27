import L20261018.Hyp43
import TauCeti.NumberTheory.ClassFieldTheory.Local.HilbertPairing
import TauCeti.NumberTheory.LocalField.Uniformizer

/-!
# C2 真实域层：**非退化性给出非零杯积**（差最后一步「`b` 不是 `n` 次幂」）

`Hyp43` 把 C2 真实层归约到「存在非零的局部符号」。本文件用 TauCeti 的
**Hilbert 配对非退化性**把这一步**做到只差一个初等事实**：

`TauCeti.ClassFieldTheory.forall_localSymbol_kummerClass_eq_zero_iff`（Serre 的论证）说

```
(∀ a : Kˣ, (a, b) = 0)  ↔  b ∈ (Kˣ)ⁿ
```

于是 **`b ∉ (Kˣ)ⁿ` ⟹ 存在 `a` 使 `(a, b) ≠ 0`**，再由 `Hyp43` 得 `cupFp (a) (b) ≠ 0`。

⟹ C2 真实层现在只差 **`∃ b ∉ (Kˣ)ⁿ`** —— 对非阿基米德局部域这是初等事实
（uniformizer `ϖ` 满足 `v(ϖ) = 1 ∉ nℤ`，`n > 1` 时故 `ϖ` 不是 `n` 次幂），
不是数学障碍。本文件把这一步也形式化（见下）。

## 主结果

* `C2Local.exists_localSymbol_ne_zero_of_notMem_powerSubgroup`：非退化性的直接推论。
* `C2Local.exists_cupFp_ne_zero_of_notMem_powerSubgroup`：落到 `ZMod n` 平凡系数。
* `C2Local.exists_notMem_powerSubgroup`：**`∃ b ∉ (Kˣ)ⁿ`**（`n > 1` 的非阿基米德局部域）。
* `C2Local.exists_cupFp_ne_zero`：**C2 真实层的完整形式**（无额外假设，除 `n > 1`）。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace C2Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [NeZero n] {ζ : K}

/-- **非退化性 ⟹ 存在非零局部符号。** `b` 不是 `n` 次幂时，必有某个 `a` 使 `(a, b) ≠ 0`。 -/
theorem exists_localSymbol_ne_zero_of_notMem_powerSubgroup (hζ : IsPrimitiveRoot ζ n)
    (tr : ↥(continuousCohomology 2 (ClassFieldTheory.muNRep n K)).toModuleCat ≃+ ZMod n)
    {b : Kˣ} (hb : b ∉ powerSubgroup Kˣ n) :
    ∃ a : Kˣ, ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr
      (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a)
      (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b) ≠ 0 := by
  by_contra h
  push Not at h
  exact hb ((ClassFieldTheory.forall_localSymbol_kummerClass_eq_zero_iff hζ tr b).mp h)

/-- **落到 `ZMod n` 平凡系数**（即 `GaloBase.cup` 所在的那一层）：
`b ∉ (Kˣ)ⁿ` ⟹ 存在 `a` 使 `cupFp (a) (b) ≠ 0`。 -/
theorem exists_cupFp_ne_zero_of_notMem_powerSubgroup (hζ : IsPrimitiveRoot ζ n)
    (tr : ↥(continuousCohomology 2 (ClassFieldTheory.muNRep n K)).toModuleCat ≃+ ZMod n)
    {b : Kˣ} (hb : b ∉ powerSubgroup Kˣ n) :
    ∃ a : Kˣ, cupFp n (Field.absoluteGaloisGroup K)
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a))
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b)) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_localSymbol_ne_zero_of_notMem_powerSubgroup hζ tr hb
  refine ⟨a, ?_⟩
  rw [← ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup]
  intro hz
  have h0 : ((ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1)
      (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a)
      (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b) = 0 :=
    (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 2).map_eq_zero_iff.mp hz
  exact ha (by rw [ClassFieldTheory.localSymbol_apply, h0, map_zero])

/-- `Multiplicative.toAdd` 把 `Multiplicative ℤ` 的幂变成 `ℤ` 的倍数：
`toAdd (x ^ n) = n * toAdd x`。（mathlib 没有这条的现成版本，`toAdd` 是 `AddEquiv`，
`toAdd (a * b) = toAdd a + toAdd b` 是 `rfl`。） -/
theorem toAdd_pow (x : Multiplicative ℤ) (n : ℕ) :
    Multiplicative.toAdd (x ^ n) = (n : ℤ) * Multiplicative.toAdd x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    show Multiplicative.toAdd (x ^ m) + Multiplicative.toAdd x
      = (↑(m + 1) : ℤ) * Multiplicative.toAdd x
    rw [ih]
    push_cast
    ring

/-- **`n > 1` 时 uniformizer 不是 `n` 次幂。** `v(π) = 1`，而 `v(xⁿ) = n·v(x) ∈ nℤ`；
`n * k = 1` 且 `n ≥ 2` 不可能。 -/
theorem notMem_powerSubgroup_of_isUniformizer {n : ℕ} (hn : 1 < n) {π : Kˣ}
    (hπ : IsUniformizer (K := K) π) : π ∉ powerSubgroup Kˣ n := by
  rw [mem_powerSubgroup_iff]
  rintro ⟨x, rfl⟩
  have h1 : (normalizedValuation K x) ^ n = Multiplicative.ofAdd (1 : ℤ) := by
    rw [← map_pow]
    exact hπ
  have h2 : (n : ℤ) * Multiplicative.toAdd (normalizedValuation K x) = 1 := by
    rw [← toAdd_pow]
    exact congrArg Multiplicative.toAdd h1
  have hnpos : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hunit : (n : ℤ) = 1 ∨ (n : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h2
  omega

/-- **存在不是 `n` 次幂的元素**（`n > 1` 的非阿基米德局部域）：取 uniformizer。 -/
theorem exists_notMem_powerSubgroup {n : ℕ} (hn : 1 < n) :
    ∃ b : Kˣ, b ∉ powerSubgroup Kˣ n := by
  obtain ⟨π, hπ⟩ := TauCeti.exists_isUniformizer (K := K)
  exact ⟨π, notMem_powerSubgroup_of_isUniformizer hn hπ⟩

/-- **C2 真实层：存在非零的 Kummer 杯积**（`n > 1` 的非阿基米德局部域，含本原 `n` 次单位根）。

**无额外假设**：`b` 取 uniformizer（不是 `n` 次幂，`exists_notMem_powerSubgroup`），
Hilbert 配对的非退化性给出 `a`，再经 `Hyp43` 的桥落到 `ZMod n` 平凡系数上的 `cupFp`。 -/
theorem exists_cupFp_ne_zero (hn : 1 < n) (hζ : IsPrimitiveRoot ζ n)
    (tr : ↥(continuousCohomology 2 (ClassFieldTheory.muNRep n K)).toModuleCat ≃+ ZMod n) :
    ∃ a b : Kˣ, cupFp n (Field.absoluteGaloisGroup K)
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit a))
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n K hζ 1
        (ClassFieldTheory.kummerClass K hζ.neZero'.out.isUnit b)) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_notMem_powerSubgroup (K := K) hn
  obtain ⟨a, ha⟩ := exists_cupFp_ne_zero_of_notMem_powerSubgroup (K := K) hζ tr hb
  exact ⟨a, b, ha⟩

end C2Local