import L20261018.Hyp60
/-!
# `(1b)` 第三阶段（三）：`carryExp (gen ^ i) = i % p` 与 `gen ^ p = 1`

`u_gen ^ p = b` 的乘积 `∏_{i<p} c(gen^i, gen)` 里，第 `i` 个因子是 `bL ^ ⌊(carryExp(gen^i) + 1)/p⌋`。
本文件算出 **`carryExp (gen^i) = i % p`**（故 `i < p` 时就是 `i`），于是
`⌊(i+1)/p⌋ = 1 ⟺ i = p−1`，乘积只剩一个因子 `bL`。

**记法注意**：本文件里 `X` 是 `Hyp59` 的 `CrossedProduct` 版，`Polynomial.X` 须写全名。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- `Gal(L/K)` 的生成元：`carryExp = 1` 的那个元素。 -/
noncomputable def gen : L K p a ≃ₐ[K] L K p a :=
  (expEquiv (p := p) (a := a) hζ ha).symm (Multiplicative.ofAdd (1 : ZMod p))

theorem carryExp_gen : carryExp hζ ha (gen hζ ha) = 1 := by
  simp only [carryExp, gen, MulEquiv.apply_symm_apply]
  exact ZMod.val_one p

/-- **`carryExp (gen ^ i) = i % p`**。 -/
theorem carryExp_gen_pow (i : ℕ) :
    carryExp hζ ha (gen hζ ha ^ i) = i % p := by
  induction i with
  | zero => rw [pow_zero, carryExp_one, Nat.zero_mod]
  | succ i ih =>
    rw [pow_succ, carryExp_mul, ih, carryExp_gen]
    have h1 : (1 : ℕ) % p = 1 := by
      rw [Nat.mod_eq_of_lt]
      have h2 := (Fact.out : p.Prime).two_le
      omega
    have hstep : (i + 1) % p = (i % p + 1) % p := by rw [Nat.add_mod, h1]
    rw [← hstep]

/-- `i < p` 时指数就是 `i`。 -/
theorem carryExp_gen_pow_of_lt (i : ℕ) (hi : i < p) :
    carryExp hζ ha (gen hζ ha ^ i) = i := by
  rw [carryExp_gen_pow, Nat.mod_eq_of_lt hi]

end

end SymbolCarryCocycle
