import L20261018.Hyp57
import TauCeti.Algebra.CrossedProduct.Basic

/-!
# `(1b)` 第二阶段（三）：**carry 余环 `TwoCocycle`**

在 Kummer 扩张 `L = K[p√a]` 上，取 `b ∈ Kˣ`，定义

    c(σ^i, σ^j) := b_L ^ ⌊(i+j)/p⌋        （i, j = carryExp 的典范代表）

并证明它是 `TauCeti.TwoCocycle`。余环恒等式
`c(g*h, j) * c(g, h) = g • c(h, j) * c(g, h*j)` 两边都是 `bL` 的幂：

* 左边指数 `⌊(g+h) mod p + j)/p⌋ + ⌊(g+h)/p⌋`；
* 右边指数 `⌊(h+j)/p⌋ + ⌊(g + (h+j) mod p)/p⌋`（`g • bL = bL` 由 `Hyp57.smul_bL`），

二者相等由 **`Hyp56.carry_assoc`** 给出。
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

variable [NeZero p] [Fact (Irreducible (X ^ p - C a : K[X]))]
  [IsSplittingField K (L K p a) (X ^ p - C a : K[X])]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

/-- **`bL` 的幂在 `Gal(L/K)` 下不动**。 -/
theorem smul_pow_bL (b : Kˣ) (n : ℕ) (τ : L K p a ≃ₐ[K] L K p a) :
    τ • (bL (p := p) (a := a) b ^ n) = bL (p := p) (a := a) b ^ n := by
  rw [AlgEquiv.smul_units_def, map_pow]
  rw [show (Units.map ↑τ) (bL (p := p) (a := a) b) = τ • bL (p := p) (a := a) b from
    (AlgEquiv.smul_units_def τ (bL (p := p) (a := a) b)).symm, smul_bL]

/-- carry 余环的**函数部分**：`c(σ^i, σ^j) = bL ^ ⌊(i+j)/p⌋`。 -/
noncomputable def carryFun (b : Kˣ) (τ ρ : L K p a ≃ₐ[K] L K p a) : (L K p a)ˣ :=
  bL (p := p) (a := a) b ^
    ((carryExp (p := p) (a := a) hζ ha τ + carryExp (p := p) (a := a) hζ ha ρ) / p)

/-- **carry 余环**：`c(σ^i, σ^j) = bL ^ ⌊(i+j)/p⌋` 是 `TauCeti.TwoCocycle`。

余环恒等式的两端都是 `bL` 的幂（`g • bL = bL`），指数相等由 `carry_assoc` 给出。 -/
noncomputable def carryCocycle (b : Kˣ) : TwoCocycle K (L K p a) where
  toFun := carryFun (p := p) (a := a) hζ ha b
  isMulCocycle₂ := by
    intro g h j
    have hg : carryExp (p := p) (a := a) hζ ha (g * h)
        = (carryExp (p := p) (a := a) hζ ha g
            + carryExp (p := p) (a := a) hζ ha h) % p :=
      carryExp_mul (p := p) (a := a) hζ ha g h
    have hj : carryExp (p := p) (a := a) hζ ha (h * j)
        = (carryExp (p := p) (a := a) hζ ha h
            + carryExp (p := p) (a := a) hζ ha j) % p :=
      carryExp_mul (p := p) (a := a) hζ ha h j
    simp only [carryFun, hg, hj]
    rw [smul_pow_bL (p := p) (a := a) (b := b) (τ := g)]
    rw [← pow_add, ← pow_add]
    congr 1
    rw [add_comm]
    exact SymbolCarry.carry_assoc (Fact.out : p.Prime).pos _ _ _

end

end SymbolCarryCocycle
