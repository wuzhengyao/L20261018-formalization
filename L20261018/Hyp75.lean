import L20261018.Hyp67
import TauCeti.Algebra.CrossedProduct.Cohomology
import TauCeti.FieldTheory.GaloisCohomology.Cyclic

/-!
# `(3)(ii)` 第二步：carry 余环的类 = 循环类（一般 `p`）

TauCeti 的 `TwoCocycle.cohomologyClass` 把交叉积余环读成 `H²(Gal(L/K), Lˣ)` 里的类；
`TauCeti.cyclicClass` 是循环代数 `(L/K, g, b)` 的类。`cohomologyClass_quadratic` 只在
`d = 2` 时把两者等同。本文件把这一步推广到 **任意素数 `p`**：

```lean
(carryCocycle hζ ha b).cohomologyClass = cyclicClass (mem_zpowers_gen hζ ha) (Additive.ofMul b)
```

证明用 `TauCeti.H2π_eq_cyclicClass`：它只要求余环在 `(g^i, g^j)`（`i,j < orderOf g`）上取
`if orderOf g ≤ i + j then b else 1` 的值。而 `carryCocycle` 的取值是
`bL ^ ((carryExp (gen^i) + carryExp (gen^j)) / p) = bL ^ ((i+j)/p)`（`Hyp61`），
在 `i,j < p` 下正是这两个分支（`Nat.div_eq_of_lt_le` / `Nat.div_eq_of_lt`）。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  [Fintype (L K p a ≃ₐ[K] L K p a)] [FiniteDimensional K (L K p a)]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **`gen` 生成 `Gal(L/K)`**：每个 `σ` 是 `gen` 的 `carryExp σ` 次幂（`Hyp66`）。 -/
theorem mem_zpowers_gen (σ : L K p a ≃ₐ[K] L K p a) :
    σ ∈ Subgroup.zpowers (gen hζ ha) :=
  Subgroup.mem_zpowers_iff.2
    ⟨(carryExp (p := p) (a := a) hζ ha σ : ℤ),
      (zpow_natCast (gen hζ ha) (carryExp (p := p) (a := a) hζ ha σ)).trans
        (gen_pow_carryExp (p := p) (a := a) hζ ha σ)⟩

/-- **`gen` 的阶是 `p`**：`orderOf = Nat.card Gal = finrank = p`。 -/
theorem orderOf_gen : orderOf (gen hζ ha) = p := by
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_gen (p := p) (a := a) hζ ha),
    IsGalois.card_aut_eq_finrank K (L K p a), finrank_eq (p := p) (a := a) hζ ha]

/-- **carry 余环的类就是 `b` 的循环类**（`(a,b)_ζ` 的交叉积侧代表）。

这是 `TauCeti.TwoCocycle.cohomologyClass_quadratic`（`d = 2`）在任意素数 `p` 上的推广。 -/
theorem cohomologyClass_carryCocycle (b : Kˣ) :
    (carryCocycle (p := p) (a := a) hζ ha b).cohomologyClass
      = cyclicClass (mem_zpowers_gen (p := p) (a := a) hζ ha) (Additive.ofMul b) := by
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  rw [TwoCocycle.cohomologyClass_def]
  refine H2π_eq_cyclicClass (mem_zpowers_gen (p := p) (a := a) hζ ha) _ b fun i j hi hj ↦ ?_
  rw [orderOf_gen (p := p) (a := a) hζ ha] at hi hj ⊢
  rw [TwoCocycle.coe_toCocycles₂]
  simp only [Prod.fst, Prod.snd, toMul_ofMul]
  show bL (p := p) (a := a) b ^
      ((carryExp (p := p) (a := a) hζ ha (gen hζ ha ^ i)
        + carryExp (p := p) (a := a) hζ ha (gen hζ ha ^ j)) / p) = _
  rw [carryExp_gen_pow_of_lt (p := p) (a := a) hζ ha i hi,
    carryExp_gen_pow_of_lt (p := p) (a := a) hζ ha j hj]
  by_cases h : p ≤ i + j
  · have h1 : (i + j) / p = 1 := Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)
    rw [if_pos h, h1, pow_one]
    rfl
  · have h0 : (i + j) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [if_neg h, h0, pow_zero]

end

end SymbolCarryCocycle

#print axioms SymbolCarryCocycle.mem_zpowers_gen
#print axioms SymbolCarryCocycle.orderOf_gen
#print axioms SymbolCarryCocycle.cohomologyClass_carryCocycle
