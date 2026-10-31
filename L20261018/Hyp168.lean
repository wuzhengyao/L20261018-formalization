import Hyp167
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# R1021（路径 A · **A1′·2·a**）：`v` 与赋值环滤过的对接 ＋ `X^p − C π` 在 `𝒪_F` 上 **Eisenstein**

`Hyp167` 已给 `[F⟮s⟯ : F] = p`（`s^p = π`）。下一步（A1′·2）是范数残差
`N(x) ≡ a_0^p (mod s)`，它需要把**抽象数据** `v : Fˣ →* Multiplicative ℤ`（R1014）
与赋值环 `𝒪_F` 的 **`𝔪`／`𝔪²` 滤过**对接 —— 论文的「`(F,v)` 为**离散赋值**域」正是这个意思。

本文件把该对接**显式化为假设**（`ValFiltrationCompat`，三字段），并机检它的直接后果：

| 声明 | 内容 |
|---|---|
| `ValFiltrationCompat` | ① 非负赋值元素落在 `𝒪_F` 中；② `b ∈ 𝔪 ⟺ 0 < v(b)`；③ `b ∈ 𝔪² ⟺ 1 < v(b)`（`b ∈ 𝒪_Fˣ`） |
| `uniformizer_mem_maximalIdeal` | 一致化元 `π` 的 `𝒪_F`-单位落在 `𝔪` |
| `uniformizer_notMem_maximalIdeal_sq` | 且**不**在 `𝔪²`（`v(π)=1`） |
| **`isEisensteinAt_uniformizer`** | **`X^p − C π` 在 `𝒪_F` 上关于 `𝔪` Eisenstein**（mathlib `Monic.isEisensteinAt_of_mem_of_notMem`） |

> **为什么要 Eisenstein**：它给 `𝒪_F[X]/(X^p − π)` 的整性/域性以及 `(s)` 的极大性，
> 是 A1′·2 里「`N(x)` 的模 `s` 计算」的环论前提。`X^p − π` 不可约（域上）已由 `Hyp167` 给出。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel IsLocalRing Polynomial

namespace L20261018

section Eisenstein

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] (p : ℕ) [Fact p.Prime]

/-- **`v` 是离散赋值**（论文假设的 Lean 落地）：抽象数据 `v` 与 `𝒪_F` 的 `𝔪`／`𝔪²` 滤过对接。 -/
structure ValFiltrationCompat (v : Fˣ →* Multiplicative ℤ) : Prop where
  /-- 非负赋值的元素是 `𝒪_F` 的单位（`𝒪_F` 在 `F` 中的“整数性”）。 -/
  exists_integerUnit : ∀ a : Fˣ, (∃ n : ℤ, 0 ≤ n ∧ v a = Multiplicative.ofAdd n) →
    ∃ b : 𝒪[F]ˣ, Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = a
  /-- `b ∈ 𝔪 ⟺ 0 < v(b)`。 -/
  mem_maximalIdeal : ∀ b : 𝒪[F]ˣ,
    ((b : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F]) ↔
      ∃ n : ℤ, 0 < n ∧
        v (Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b) = Multiplicative.ofAdd n
  /-- `b ∈ 𝔪² ⟺ 1 < v(b)`。 -/
  mem_maximalIdeal_sq : ∀ b : 𝒪[F]ˣ,
    ((b : ↥𝒪[F]) ∈ (IsLocalRing.maximalIdeal ↥𝒪[F]) ^ 2) ↔
      ∃ n : ℤ, 1 < n ∧
        v (Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b) = Multiplicative.ofAdd n

variable {v : Fˣ →* Multiplicative ℤ}

/-- **一致化元落在 `𝔪`**：存在 `𝒪_F` 的单位 `b`（`b ↦ π`），它在 `𝔪` 中。 -/
theorem uniformizer_mem_maximalIdeal (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) :
    ∃ b : 𝒪[F]ˣ, Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π ∧
      (b : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
  obtain ⟨b, hb⟩ := hv.exists_integerUnit π ⟨1, by norm_num, hπ⟩
  exact ⟨b, hb, (hv.mem_maximalIdeal b).mpr ⟨1, one_pos, by rw [hb, hπ]⟩⟩

/-- **一致化元不在 `𝔪²`**（因为 `v(π) = 1`，而 `𝔪²` 对应 `v > 1`）。 -/
theorem uniformizer_notMem_maximalIdeal_sq (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) :
    (b : ↥𝒪[F]) ∉ (IsLocalRing.maximalIdeal ↥𝒪[F]) ^ 2 := by
  intro hmem
  obtain ⟨n, hn, hvn⟩ := (hv.mem_maximalIdeal_sq b).mp hmem
  rw [hb, hπ] at hvn
  have h1 : n = 1 := Multiplicative.ofAdd.injective hvn.symm
  omega

/-- **A1′·2·a：`X^p − C π` 在 `𝒪_F` 上关于 `𝔪` Eisenstein**（`π` 为一致化元）。 -/
theorem isEisensteinAt_uniformizer (hv : ValFiltrationCompat (F := F) v) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) {b : 𝒪[F]ˣ}
    (hb : Units.map (Subring.subtype 𝒪[F] : ↥𝒪[F] →* F) b = π) :
    (X ^ p - C (b : ↥𝒪[F])).IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[F]) := by
  have hmemπ : (b : ↥𝒪[F]) ∈ IsLocalRing.maximalIdeal ↥𝒪[F] :=
    (hv.mem_maximalIdeal b).mpr ⟨1, one_pos, by rw [hb, hπ]⟩
  have hnotMemπ : (b : ↥𝒪[F]) ∉ (IsLocalRing.maximalIdeal ↥𝒪[F]) ^ 2 :=
    uniformizer_notMem_maximalIdeal_sq (F := F) hv hπ hb
  have hmonic : (X ^ p - C (b : ↥𝒪[F])).Monic :=
    monic_X_pow_sub_C _ (Fact.out : p.Prime).pos.ne'
  have hp0 : ¬ (0 = p) := fun h => (Fact.out : p.Prime).ne_zero h.symm
  have hcoeff0 : (X ^ p - C (b : ↥𝒪[F])).coeff 0 = -(b : ↥𝒪[F]) := by
    rw [coeff_sub, coeff_X_pow, if_neg hp0, coeff_C, if_pos rfl, zero_sub]
  refine hmonic.isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[F]).ne_top ?_ ?_
  · intro n hn
    rw [natDegree_X_pow_sub_C] at hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [hcoeff0]
      exact neg_mem_iff.mpr hmemπ
    · have hn1 : ¬ (n = p) := by omega
      have hn0 : ¬ (n = 0) := by omega
      rw [coeff_sub, coeff_X_pow, if_neg hn1, coeff_C, if_neg hn0, sub_zero]
      exact Ideal.zero_mem _
  · rw [hcoeff0, neg_mem_iff]
    exact hnotMemπ

end Eisenstein

end L20261018

#print axioms L20261018.uniformizer_mem_maximalIdeal
#print axioms L20261018.uniformizer_notMem_maximalIdeal_sq
#print axioms L20261018.isEisensteinAt_uniformizer
