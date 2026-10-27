import L20261018.Hyp63
/-!
# `(1b)` 第三阶段（六）：满射性的两块砖

`Hyp47.nonempty_algEquiv_of_finrank` 的收口还差 `liftOf` 的**满射性**，即
`Algebra.adjoin K {X, Y} = ⊤`（`X = inc α`、`Y = u_gen`）。本文件给出两块砖：

* `adjoin_alpha : Algebra.adjoin K {α} = ⊤`（`α` 生成 Kummer 扩张，mathlib `adjoinRoot_eq_top`）；
* `inc_mem_adjoin`：`inc` 把 `K[α]` 送进 `K[inc α]`（`AlgHom.map_adjoin`）。

下一轮：`basis (gen^i) = inc(∏)⁻¹ * Y^i` ⟹ 基元素都在 `adjoin` 里 ⟹ 满射性。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Polynomial AdjoinRoot

namespace SymbolCarryCocycle

open SymbolKummerField
open TauCeti

universe u

variable {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

/-- **`α` 生成 Kummer 扩张**：`Algebra.adjoin K {α} = ⊤`。 -/
theorem adjoin_alpha :
    Algebra.adjoin K (Set.singleton (α (K := K) (p := p) (a := a))) = ⊤ := by
  rw [α]
  exact AdjoinRoot.adjoinRoot_eq_top

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]

variable (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

/-- **`inc` 与 `adjoin` 交换**：`l ∈ K[α] ⟹ inc l ∈ K[inc α]`。 -/
theorem inc_mem_adjoin (b : Kˣ) {l : L K p a}
    (hl : l ∈ Algebra.adjoin K (Set.singleton (α (K := K) (p := p) (a := a)))) :
    CrossedProduct.inc (carryCocycle hζ ha b) l ∈
      Algebra.adjoin K (Set.singleton (CrossedProduct.inc (carryCocycle hζ ha b)
        (α (K := K) (p := p) (a := a)))) := by
  have hmap : (Algebra.adjoin K (Set.singleton (α (K := K) (p := p) (a := a)))).map
        (CrossedProduct.inc (carryCocycle hζ ha b))
      = Algebra.adjoin K (Set.singleton (CrossedProduct.inc (carryCocycle hζ ha b)
          (α (K := K) (p := p) (a := a)))) := by
    rw [AlgHom.map_adjoin]
    congr 1
    exact Set.image_singleton
  rw [← hmap]
  exact Subalgebra.mem_map.mpr ⟨l, hl, rfl⟩

end

end SymbolCarryCocycle