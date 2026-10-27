import L20261018.Hyp56
/-!
# `(1b)` 第二阶段（二）：carry 余环的**指数标号**与**固定的单位**

carry 余环按 `c(σ^i, σ^j) = b^{⌊(i+j)/p⌋}` 定义，其中 `i, j` 是 `Gal(L/K) ≃* ZMod p`
（mathlib `autEquivZmod`）下的典范代表（`ZMod.val`）。本文件给出构造它的两块零件：

* `bL`：`b ∈ Kˣ` 在 `L` 中的单位像，且**在 `Gal(L/K)` 作用下不动**（`smul_bL`）；
* `carryExp`：指数标号，以及它的三条基本性质
  （小于 `p`、在 `1` 处为 `0`、在乘法下取模相加）。

下一轮用它们证明 `TwoCocycle` 的余环恒等式（由 `Hyp56.carry_assoc` 收）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (X ^ p - C a : K[X]))]
  [IsSplittingField K (L K p a) (X ^ p - C a : K[X])]

/-- `b ∈ Kˣ` 在 `L = K[p√a]` 中的单位像。 -/
noncomputable def bL (b : Kˣ) : (L K p a)ˣ :=
  Units.map (algebraMap K (L K p a)).toMonoidHom b

/-- **`bL` 在 `Gal(L/K)` 作用下不动**（它是 `K` 的元素的像）。 -/
theorem smul_bL (b : Kˣ) (τ : L K p a ≃ₐ[K] L K p a) :
    τ • bL (p := p) (a := a) b = bL (p := p) (a := a) b := by
  ext
  change τ (algebraMap K (L K p a) (b : K)) = algebraMap K (L K p a) (b : K)
  exact AlgEquiv.commutes τ (b : K)

/-- **指数标号**：`Gal(L/K) ≃* Multiplicative (ZMod p)`（mathlib `autEquivZmod`）。 -/
noncomputable def expEquiv (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a) :
    (L K p a ≃ₐ[K] L K p a) ≃* Multiplicative (ZMod p) :=
  autEquivZmod (irreducible ha) (L K p a) hζ

/-- **carry 指数**：典范代表（`0 ≤ · < p`）。 -/
noncomputable def carryExp (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)
    (τ : L K p a ≃ₐ[K] L K p a) : ℕ :=
  (expEquiv (p := p) (a := a) hζ ha τ).toAdd.val

theorem carryExp_lt (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)
    (τ : L K p a ≃ₐ[K] L K p a) : carryExp (p := p) (a := a) hζ ha τ < p :=
  ZMod.val_lt _

theorem carryExp_one (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a) :
    carryExp (p := p) (a := a) hζ ha 1 = 0 := by
  rw [carryExp, map_one]
  exact ZMod.val_zero

/-- **乘法下的指数**：`carryExp (σ * τ) = (carryExp σ + carryExp τ) % p`。 -/
theorem carryExp_mul (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)
    (σ τ : L K p a ≃ₐ[K] L K p a) :
    carryExp (p := p) (a := a) hζ ha (σ * τ)
      = (carryExp (p := p) (a := a) hζ ha σ
          + carryExp (p := p) (a := a) hζ ha τ) % p := by
  rw [carryExp, carryExp, carryExp, map_mul]
  exact ZMod.val_add _ _

end

end SymbolCarryCocycle
