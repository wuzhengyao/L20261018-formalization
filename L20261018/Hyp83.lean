import L20261018.Hyp68
import L20261018.Hyp50
import L20261018.Hyp67
import L20261018.Hyp47
import TauCeti.Algebra.CrossedProduct.CentralSimple

/-!
# 符号代数的**实例栈从 `ha` 推出**：`index ≤ p` 的无条件形式（R898）

`Hyp68.index_symbolAlg_le` 把五条「技术实例」作为 section variable／binder 收：
`[Fact (Irreducible (X^p − C a))]`、`[IsSplittingField …]`、`[Fintype Gal]`、
`[Algebra.IsInvariant …]`，以及 `SymbolAlg` 上的 `Algebra.IsCentral`／`IsSimpleRing`／
`FiniteDimensional`。这些**全部可以由 `ha : ∀ b, b^p ≠ a`（`a ∉ K^{×p}`）＋ `hζ` 推出**，
本文件把这件事机检化：

| 实例 | 来源 |
|---|---|
| `Fact (Irreducible (X^p − C a))` | `Hyp55.irreducible ha`（mathlib `X_pow_sub_C_irreducible_of_prime`） |
| `IsSplittingField K (L K p a) …` | `Hyp55.isSplittingField hζ ha` |
| `FiniteDimensional K (L K p a)` | `IsSplittingField.finiteDimensional` |
| `IsGalois K (L K p a)` | `Hyp55.isGalois hζ ha` |
| `Fintype (L K p a ≃ₐ[K] L K p a)` | mathlib `AlgEquiv.fintype` |
| `Algebra.IsInvariant K L (L ≃ₐ[K] L)` | **`inferInstance`**（`IsGalois` 即够——本轮实测） |
| `Algebra.IsCentral K (SymbolAlg …)` | `Hyp50.isCentral_of_algEquiv`（沿 `Hyp67` 的同构从 `CrossedProduct` 搬） |
| `IsSimpleRing (SymbolAlg …)` | `Hyp50.isSimpleRing_of_algEquiv`（同上） |
| `FiniteDimensional K (SymbolAlg …)` | `Hyp47.finiteDimensional`（`p` 素 ⟹ `1 < p`） |

## 主结果

* `isCentral_symbolAlg`／`isSimpleRing_symbolAlg`／`finiteDimensional_symbolAlg`：三条 CSA 实例。
* **`index_symbolAlg_le_of_notMem_pow`**：`a ∉ K^{×p}` ＋ `ζ` 本原 ⟹ **`index K (SymbolAlg K p a b ζ) ≤ p`**
  —— `Hyp68` 的**无条件版**（只剩 `hζ`、`ha`、`b`）。这是 3.2(1)(2) 的 `hind` 只差的那一块。
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti
open SymbolPres SymbolPres.SymbolAlg

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p]

/-- **`ha` 给出 `X ^ p - C a` 不可约**（`Fact` 形式，供实例搜索用）。 -/
theorem fact_irreducible_of_notMem_pow (ha : ∀ b : K, b ^ p ≠ a) :
    Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X])) :=
  ⟨irreducible (K := K) (p := p) (a := a) ha⟩

/-- **`SymbolAlg` 的中心性**（沿 (1b) 的同构从 `CrossedProduct` 搬）。 -/
theorem isCentral_symbolAlg (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a) (b : Kˣ) :
    Algebra.IsCentral K (SymbolAlg K p a (b : K) ζ) := by
  haveI : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X])) := fact_irreducible_of_notMem_pow ha
  haveI : IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X]) := isSplittingField hζ ha
  haveI : FiniteDimensional K (L K p a) :=
    IsSplittingField.finiteDimensional (L := L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])
  haveI : IsGalois K (L K p a) := isGalois hζ ha
  haveI : Fintype (L K p a ≃ₐ[K] L K p a) := AlgEquiv.fintype K (L K p a)
  haveI : Algebra.IsInvariant K (L K p a) (L K p a ≃ₐ[K] L K p a) := inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_crossedProduct (p := p) (a := a) hζ ha b
  exact SymbolBrauer.isCentral_of_algEquiv (K := K) e.symm

/-- **`SymbolAlg` 的单性**。 -/
theorem isSimpleRing_symbolAlg (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)
    (b : Kˣ) : IsSimpleRing (SymbolAlg K p a (b : K) ζ) := by
  haveI : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X])) := fact_irreducible_of_notMem_pow ha
  haveI : IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X]) := isSplittingField hζ ha
  haveI : FiniteDimensional K (L K p a) :=
    IsSplittingField.finiteDimensional (L := L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])
  haveI : IsGalois K (L K p a) := isGalois hζ ha
  haveI : Fintype (L K p a ≃ₐ[K] L K p a) := AlgEquiv.fintype K (L K p a)
  haveI : Algebra.IsInvariant K (L K p a) (L K p a ≃ₐ[K] L K p a) := inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_crossedProduct (p := p) (a := a) hζ ha b
  exact SymbolBrauer.isSimpleRing_of_algEquiv (K := K) e.symm

/-- **`SymbolAlg` 的有限维性**（取 `Hyp47` 的呈现侧证明：`p` 素 ⟹ `1 < p`）。 -/
theorem finiteDimensional_symbolAlg (b : K) :
    FiniteDimensional K (SymbolAlg K p a b ζ) :=
  finiteDimensional (p := p) (a := a) (b := b) (ζ := ζ) (Fact.out : p.Prime).one_lt

/-- **`hind` 的实体（无条件版）**：`a ∉ K^{×p}` ＋ `ζ_p ∈ K` ⟹
`index K (SymbolAlg K p a b ζ) ≤ p`。

这是 `Hyp68.index_symbolAlg_le` 去掉全部技术实例 hypothesis 后的形式——它的前提只余
`hζ`（本原 `p` 次单位根）与 `ha`（`a` 不是 `p` 次幂），而这两条正是论文自身的假设。 -/
theorem index_symbolAlg_le_of_notMem_pow (hζ : IsPrimitiveRoot ζ p)
    (ha : ∀ b : K, b ^ p ≠ a) (b : Kˣ)
    [Algebra.IsCentral K (SymbolAlg K p a (b : K) ζ)]
    [IsSimpleRing (SymbolAlg K p a (b : K) ζ)]
    [FiniteDimensional K (SymbolAlg K p a (b : K) ζ)] :
    TauCeti.Algebra.index K (SymbolAlg K p a (b : K) ζ) ≤ p := by
  haveI : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X])) := fact_irreducible_of_notMem_pow ha
  haveI : IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X]) := isSplittingField hζ ha
  haveI : FiniteDimensional K (L K p a) :=
    IsSplittingField.finiteDimensional (L := L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])
  haveI : IsGalois K (L K p a) := isGalois hζ ha
  haveI : Fintype (L K p a ≃ₐ[K] L K p a) := AlgEquiv.fintype K (L K p a)
  haveI : Algebra.IsInvariant K (L K p a) (L K p a ≃ₐ[K] L K p a) := inferInstance
  exact index_symbolAlg_le (p := p) (a := a) hζ ha b

end

end SymbolCarryCocycle

#print axioms SymbolCarryCocycle.fact_irreducible_of_notMem_pow
#print axioms SymbolCarryCocycle.isCentral_symbolAlg
#print axioms SymbolCarryCocycle.isSimpleRing_symbolAlg
#print axioms SymbolCarryCocycle.finiteDimensional_symbolAlg
#print axioms SymbolCarryCocycle.index_symbolAlg_le_of_notMem_pow
