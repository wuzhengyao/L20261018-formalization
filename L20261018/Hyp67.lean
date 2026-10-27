import L20261018.Hyp66
import L20261018.Hyp47
/-!
# `(1b)` 收口：**`SymbolAlg K p a b ζ ≃ₐ CrossedProduct (carryCocycle b)`**

非退化支（`a` 不是 `p` 次幂）的呈现：`L = K[p√a]` 上取 carry 余环 `c`，
则 `SymbolAlg K p a b ζ ≅ CrossedProduct c`。

三条关系都已机检：`X_pow`（`Hyp59`）、`Y_pow`（`Hyp63`）、`Y_mul_X`（`Hyp59`）；
满射性由 `adjoin_genSet_eq_top`（`Hyp66`）＋ `liftOf_x`/`liftOf_y`（`Hyp47`）给出；
维数 `finrank = p * p` 由 `CrossedProduct.finrank_eq_finrank_mul_card` ＋
`IsGalois.card_aut_eq_finrank` ＋ `[L:K] = p`（`Hyp55`）给出。
最后套 `Hyp47.nonempty_algEquiv_of_finrank`。
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

/-- **`gen` 在半线性规则里的作用**：`gen α = ζ • α`。 -/
theorem gen_alpha :
    gen hζ ha (α (K := K) (p := p) (a := a)) = ζ • α (K := K) (p := p) (a := a) := by
  rw [gen, expEquiv]
  have h := autEquivZmod_symm_apply_natCast (irreducible ha) (L K p a)
    (α_pow (K := K) (p := p) (a := a)) hζ 1
  simpa using h

/-- **`(1b)` 主定理**：非退化支的呈现。 -/
theorem nonempty_algEquiv_crossedProduct (b : Kˣ) :
    Nonempty (SymbolAlg K p a b ζ ≃ₐ[K] CrossedProduct (cYC hζ ha b)) := by
  classical
  -- 三条关系
  have h1 : X (cYC hζ ha b) (α (K := K) (p := p) (a := a)) ^ p
      = algebraMap K (CrossedProduct (cYC hζ ha b)) a :=
    X_pow (cYC hζ ha b) (α (K := K) (p := p) (a := a)) (α_pow (K := K) (p := p) (a := a))
  have h2 : Y (cYC hζ ha b) (gen hζ ha) ^ p
      = algebraMap K (CrossedProduct (cYC hζ ha b)) (b : K) :=
    Y_pow (p := p) (a := a) hζ ha b
  have h3 : Y (cYC hζ ha b) (gen hζ ha) * X (cYC hζ ha b) (α (K := K) (p := p) (a := a))
      = algebraMap K (CrossedProduct (cYC hζ ha b)) ζ
        * (X (cYC hζ ha b) (α (K := K) (p := p) (a := a)) * Y (cYC hζ ha b) (gen hζ ha)) := by
    rw [Y_mul_X (cYC hζ ha b) (gen hζ ha) (α (K := K) (p := p) (a := a))
      (gen_alpha (p := p) (a := a) hζ ha), Algebra.smul_def]
  -- 满射性
  have hsurj : Function.Surjective
      (liftOf (p := p) a b ζ (X (cYC hζ ha b) (α (K := K) (p := p) (a := a)))
        (Y (cYC hζ ha b) (gen hζ ha)) h1 h2 h3) := by
    rw [← AlgHom.range_eq_top]
    refine top_le_iff.mp ?_
    rw [← adjoin_genSet_eq_top (p := p) (a := a) hζ ha b]
    refine Algebra.adjoin_le ?_
    intro z hz
    rw [genSet] at hz
    rw [Set.mem_insert_iff] at hz
    rcases hz with rfl | hz
    · exact ⟨x a b ζ, liftOf_x (p := p) (a := a) (b := b) (ζ := ζ) _ _ h1 h2 h3⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨y a b ζ, liftOf_y (p := p) (a := a) (b := b) (ζ := ζ) _ _ h1 h2 h3⟩
  -- 维数
  haveI : FiniteDimensional K (L K p a) :=
    IsSplittingField.finiteDimensional (L := L K p a)
      (Polynomial.X ^ p - Polynomial.C a : K[X])
  haveI : IsGalois K (L K p a) := isGalois (p := p) (a := a) hζ ha
  have hdim : Module.finrank K (CrossedProduct (cYC hζ ha b)) = p * p := by
    rw [CrossedProduct.finrank_eq_finrank_mul_card,
      finrank_eq (K := K) (p := p) (a := a) hζ ha, IsGalois.card_aut_eq_finrank,
      finrank_eq (K := K) (p := p) (a := a) hζ ha]
  exact SymbolPres.SymbolAlg.nonempty_algEquiv_of_finrank (p := p) (a := a) (b := b) (ζ := ζ)
    (Fact.out : p.Prime).one_lt _ _ h1 h2 h3 hsurj hdim

end

end SymbolCarryCocycle
