import L20261018.Ch2.Hensel.Valuation.Step001_residue_valuation_without_completeness
import Mathlib.FieldTheory.KummerExtension

/-!
# R1020（路径 A · **A1′ 第一小步**）：`[F⟮s⟯ : F] = p`（`s^p = π`，`π` 一致化元）

`PLAN-A-HENSEL-LAYER.md` 的 A1 一般路线（valuation ring 的整闭包 → 局部化是 valuation ring）
因 mathlib **无 Prüfer 域理论**而关闭（R1019 实测），故走 **A1′ 窄路线**：只对 `L = F⟮s⟯`（`s^p = π`）做。

本文件是 A1′ 的第一块：**素数次纯分歧扩张的次数**。

| 声明 | 内容 |
|---|---|
| `pow_ne_uniformizer_unit` | 一致化元在 `Fˣ` 中不是 `p` 次幂（`v(π)=1` ⟹ `p·v(b) = 1` 不可能） |
| `pow_ne_uniformizer` | 域元素版（`b^p ≠ π`，`b = 0` 单独处理） |
| **`irreducible_X_pow_sub_C_uniformizer`** | **`X^p - C π` 不可约**（mathlib `X_pow_sub_C_irreducible_of_odd`） |
| **`finrank_eq_prime_of_root_uniformizer`** | **`s^p = π ∧ F⟮s⟯ = ⊤ ⟹ [L : F] = p`** |

> `p ≠ 2` 来自论文的「`p` 为奇素数」；mathlib 的 `X^n - C a` 不可约判据要求 `n` 奇（`X^4 - 4` 是反例）。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open TauCeti ValuativeRel Polynomial
open IntermediateField

namespace L20261018

section Uniformizer

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime]

/-- **一致化元不是 `p` 次幂**（单位版）：`v(π) = 1` 时 `b^p = π` 不可能。 -/
theorem pow_ne_uniformizer_unit (v : Fˣ →* Multiplicative ℤ) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (b : Fˣ) : b ^ p ≠ π := by
  intro hb
  have h1 : Multiplicative.toAdd (v (b ^ p)) = Multiplicative.toAdd (v π) := by rw [hb]
  rw [map_pow, toAdd_pow', hπ] at h1
  have hdvd : (p : ℤ) ∣ 1 := Dvd.intro (Multiplicative.toAdd (v b)) h1
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have hgt : (1 : ℤ) < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  omega

/-- **一致化元不是 `p` 次幂**（域元素版）：`b ^ p ≠ (π : F)`。 -/
theorem pow_ne_uniformizer (v : Fˣ →* Multiplicative ℤ) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (b : F) : b ^ p ≠ (π : F) := by
  intro hb
  by_cases hb0 : b = 0
  · subst hb0
    have hzero : (π : F) = 0 := by
      simpa [zero_pow (Fact.out : p.Prime).pos.ne'] using hb.symm
    exact π.ne_zero hzero
  · refine pow_ne_uniformizer_unit (F := F) p v hπ (Units.mk0 b hb0) ?_
    ext
    push_cast
    exact hb

/-- **`X^p - C π` 不可约**（`p` 奇素、`π` 一致化元）。 -/
theorem irreducible_X_pow_sub_C_uniformizer (v : Fˣ →* Multiplicative ℤ) {π : Fˣ}
    (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2) :
    Irreducible (X ^ p - C (π : F)) := by
  refine X_pow_sub_C_irreducible_of_odd ((Fact.out : p.Prime).odd_of_ne_two hp2) ?_
  intro q hq hqp b
  have hqeq : q = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd q hqp with h | h
    · exact absurd h hq.ne_one
    · exact h
  rw [hqeq]
  exact pow_ne_uniformizer (F := F) p v hπ b

/-- **A1′·1**：`s^p = π` 且 `F⟮s⟯ = ⊤` ⟹ `[L : F] = p`（素数次纯分歧扩张的次数）。 -/
theorem finrank_eq_prime_of_root_uniformizer {L : Type} [Field L] [Algebra F L] {π : Fˣ}
    (v : Fˣ →* Multiplicative ℤ) (hπ : v π = Multiplicative.ofAdd (1 : ℤ)) (hp2 : p ≠ 2)
    {s : L} (hs : s ^ p = algebraMap F L (π : F)) (hgen : IntermediateField.adjoin F {s} = ⊤) :
    Module.finrank F L = p := by
  have hmonic : (X ^ p - C (π : F)).Monic :=
    monic_X_pow_sub_C _ (Fact.out : p.Prime).pos.ne'
  have hroot : aeval s (X ^ p - C (π : F)) = 0 := by
    simp [map_pow, hs]
  have hirr : Irreducible (X ^ p - C (π : F)) :=
    irreducible_X_pow_sub_C_uniformizer (F := F) p v hπ hp2
  have hmin : minpoly F s = X ^ p - C (π : F) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
  have hint : IsIntegral F s := ⟨_, hmonic, hroot⟩
  have hdeg : Module.finrank F ↥(IntermediateField.adjoin F {s}) = p := by
    rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]
  have htop : Module.finrank F ↥(IntermediateField.adjoin F {s}) = Module.finrank F L := by
    rw [hgen]
    exact LinearEquiv.finrank_eq
      (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv
  rw [← htop, hdeg]

end Uniformizer

end L20261018

#print axioms L20261018.pow_ne_uniformizer_unit
#print axioms L20261018.pow_ne_uniformizer
#print axioms L20261018.irreducible_X_pow_sub_C_uniformizer
#print axioms L20261018.finrank_eq_prime_of_root_uniformizer
