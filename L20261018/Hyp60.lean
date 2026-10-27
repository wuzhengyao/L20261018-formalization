import L20261018.Hyp59
/-!
# `(1b)` 第三阶段（二）：基元素的**幂公式**（望远镜化乘积）

在 `CP = CrossedProduct c` 里，标准基元素的幂满足

    u_σ ^ n = inc (∏_{i<n} c(σ^i, σ)) · u_{σ^n}

（对 `n` 归纳，用 TauCeti 的余环规则 `basis_mul_basis`）。取 `n = p`、`σ = gen`、`c = carryCocycle b`
即得 **`u_gen ^ p = b`**（下一轮把乘积算成 `b`）。

归约需要余环**正规化** `c(1,1) = 1`（carry 余环满足：`carryExp 1 = 0` ⟹ `c(1,1) = bL^0 = 1`）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace SymbolCarryCocycle

open TauCeti

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- 正规化余环：`c(1, 1) = 1`。 -/
theorem basis_one_eq_one (c : TwoCocycle K L) (h1 : c.toFun 1 1 = 1) :
    CrossedProduct.basis c (1 : L ≃ₐ[K] L) = 1 := by
  rw [CrossedProduct.basis_one, h1]
  exact map_one (CrossedProduct.inc c)

/-- **幂公式**：`u_σ ^ n = inc (∏_{i<n} c(σ^i, σ)) · u_{σ^n}`。 -/
theorem basis_pow (c : TwoCocycle K L) (h1 : c.toFun 1 1 = 1) (σ : L ≃ₐ[K] L) (n : ℕ) :
    CrossedProduct.basis c σ ^ n
      = CrossedProduct.inc c ((Finset.range n).prod fun i => (c.toFun (σ ^ i) σ : L))
        * CrossedProduct.basis c (σ ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Finset.prod_range_zero, pow_zero, map_one (CrossedProduct.inc c), one_mul]
    exact (basis_one_eq_one (K := K) c h1).symm
  | succ n ih =>
    rw [pow_succ, ih, mul_assoc, CrossedProduct.basis_mul_basis, ← mul_assoc, ← map_mul,
      Finset.prod_range_succ, ← pow_succ]

end SymbolCarryCocycle
