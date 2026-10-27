import L20261018.Hyp67
import L20261018.Hyp15
import TauCeti.Algebra.CrossedProduct.CentralSimple
import L20261018.Hyp54
import L20261018.Hyp50
/-!
# `(3)` 的 `hind`：**符号代数的指数 `≤ p`**

`3.2(1)(2)` 的 `hind` 需要 `ind ≤ p`。对符号代数本身，这由 (1b) 的同构送到交叉积，
再用 `Hyp15.index_crossedProduct_le_of_finrank`（`index ≤ [L:K] = p`）收。

`(3)(ii)`（把 `h = (a₁)∪(a₂)` 认成符号代数的**类**）仍需类层面的杯积公式
（`cor:symbol-cup`，Merkurjev–Suslin 层面）——本文件给的是它的 `hind` 那一半。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti
open SymbolPres SymbolPres.SymbolAlg

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  [Fintype (L K p a ≃ₐ[K] L K p a)]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **`hind`（符号代数版，实例显式）**：`index K (SymbolAlg K p a b ζ) ≤ p`。

`SymbolAlg` 的 CSA 实例由 (1b) 的同构从交叉积搬来（`Hyp50` 的两条搬运引理）——本定理把它们
作为**显式 binder**，避免在 `haveI` 里做实例搬运（Lean 在该形态下会卡，见 `ASSUMPTIONS` R880）。 -/
theorem index_symbolAlg_le (b : Kˣ)
    [Algebra.IsCentral K (SymbolAlg K p a b ζ)] [IsSimpleRing (SymbolAlg K p a b ζ)]
    [FiniteDimensional K (SymbolAlg K p a b ζ)]
    [Algebra.IsInvariant K (L K p a) (L K p a ≃ₐ[K] L K p a)] :
    TauCeti.Algebra.index K (SymbolAlg K p a b ζ) ≤ p := by
  haveI hLfin : FiniteDimensional K (L K p a) :=
    IsSplittingField.finiteDimensional (L := L K p a)
      (Polynomial.X ^ p - Polynomial.C a : K[X])
  haveI hLgal : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  obtain ⟨e⟩ := nonempty_algEquiv_crossedProduct (p := p) (a := a) hζ ha b
  rw [TauCeti.Algebra.index_eq_of_algEquiv (K := K) e]
  exact SymbolAlgebra.index_crossedProduct_le_of_finrank (cYC hζ ha b) p
    (finrank_eq (K := K) (p := p) (a := a) hζ ha)

end

end SymbolCarryCocycle
