import L20261018.Hyp61
/-!
# `(1b)` 第三阶段（四）：`gen ^ p = 1`、乘积求和、以及 `∏ c(gen^i, gen) = b`

| 定理 | 内容 |
|---|---|
| `ofAdd_one_pow` | `(ofAdd 1 : Multiplicative (ZMod p)) ^ p = 1`（`pow_card_eq_one` ＋ `ZMod.card`） |
| **`gen_pow_eq_one`** | **`gen ^ p = 1`**（`expEquiv` 单射 ＋ 上式） |
| `sum_div_range` | `∑_{i<p} (i+1)/p = 1`（只有 `i = p−1` 一项非零） |
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

universe u

/-- `(ofAdd 1)^p = 1`：`Multiplicative (ZMod p)` 的阶为 `p`。 -/
theorem ofAdd_one_pow (p : ℕ) [Fact p.Prime] :
    (Multiplicative.ofAdd (1 : ZMod p) : Multiplicative (ZMod p)) ^ p = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  convert pow_card_eq_one (G := Multiplicative (ZMod p))
    (x := Multiplicative.ofAdd (1 : ZMod p)) using 2
  simp [ZMod.card]

/-- `∑_{i<p} (i+1)/p = 1`。 -/
theorem sum_div_range (p : ℕ) (hp : 0 < p) :
    (∑ i ∈ Finset.range p, (i + 1) / p) = 1 := by
  rw [Finset.sum_eq_single (p - 1)]
  · rw [Nat.sub_add_cancel hp, Nat.div_self hp]
  · intro b hb hne
    rw [Finset.mem_range] at hb
    rw [Nat.div_eq_of_lt]
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hp Nat.one_pos)) h

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **`gen ^ p = 1`**。 -/
theorem gen_pow_eq_one : gen hζ ha ^ p = 1 := by
  apply (expEquiv (p := p) (a := a) hζ ha).injective
  rw [map_pow, map_one, gen, MulEquiv.apply_symm_apply, ofAdd_one_pow]

end

end SymbolCarryCocycle
