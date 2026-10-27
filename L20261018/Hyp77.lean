import L20261018.Hyp76
/-!
# `cor:symbol-cup` 的逐字形式（去掉 ζ-约定的负号）

`Hyp76.symbolAlg_brauerClass_eq` 给出

```lean
brauerGroupEquivBr K (mk (CSA.of K (SymbolAlg K p a b ζ))) = - kummerBrauerClass ζ hζ b (aUnit a)
```

右端的负号来自 TauCeti 的约定：`kummerBrauerClass ζ hζ x y` 是杯积 `(x) ∪ (y)`，
而 `kummerBrauerClass_eq_neg_relBrInfl_cyclicClass` 的输出带负号。本文件补上
**杯积的斜对称性** `(x) ∪ (y) = -((y) ∪ (x))`，于是右端可写成 `kummerBrauerClass ζ hζ (a) b`，
**与论文 `cor:symbol-cup` 的 `[(a,b)_F] = (a)∪(b)` 逐字同形**。

斜对称性的来源是 `TopPairing.cup_gradedComm`（分级交换性）＋
`TauCeti.ClassFieldTheory.kummerCupPairing_flip`（配对对称）——与 `A.lean` 的 `GaloBase.cup_skew`
同一套零件，只是换到 `μ_n` 系数上。
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial AdjoinRoot

namespace SymbolCupBridge

open SymbolKummerField SymbolCarryCocycle SymbolPres
open TauCeti

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {a : K} {ζ : K}

section

variable [NeZero p] [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a : K[X]))]
  [IsSplittingField K (L K p a) (Polynomial.X ^ p - Polynomial.C a : K[X])]
  [Fintype (L K p a ≃ₐ[K] L K p a)] [FiniteDimensional K (L K p a)] [IsGalois K (L K p a)]
  (hζ : IsPrimitiveRoot ζ p) (ha : ∀ b : K, b ^ p ≠ a)

include hζ ha

/-- **杯积的斜对称性**（`μ_n` 系数，`n = p`）：`(x) ∪ (y) = -((y) ∪ (x))`。

与 `A.lean` 的 `GaloBase.cup_skew` 同一套零件：`cup_gradedComm`（分级交换性，`(-1)^(1*1) = -1`）
＋ `kummerCupPairing_flip`（ζ-配对对称）。 -/
theorem kummerCupPairing_skew
    {x y : ↑(continuousCohomology 1 (TauCeti.ClassFieldTheory.muNRep p K)).toModuleCat} :
    (TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 x y
      = -((TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ).cup 1 1 y x) := by
  have h := TauCeti.TopPairing.cup_gradedComm
    (TauCeti.ClassFieldTheory.kummerCupPairing ζ hζ) 1 1 x y
  rw [show (1 * 1 : ℕ) = 1 by norm_num, pow_one] at h
  rw [show Nat.add_comm 1 1 = rfl from Subsingleton.elim _ _] at h
  rw [ContinuousCohomology.degreeCast_rfl] at h
  rw [TauCeti.ClassFieldTheory.kummerCupPairing_flip] at h
  simpa using h

/-- **`kummerBrauerClass` 的交换斜对称性**：`(a)∪(b) = -((b)∪(a))`。

直接重写即可：`kummerBrauerClass_def` 两次把两侧化到 `h2MuToBr (cup …)`，
`kummerCupPairing_skew` 把左端的杯积换成负的下标对换，`map_neg` 把负号提到 `h2MuToBr` 外。
**不需要** `h2MuToBr` 的单射性。 -/
theorem kummerBrauerClass_swap (x y : Kˣ) :
    TauCeti.ClassFieldTheory.kummerBrauerClass ζ hζ x y
      = -TauCeti.ClassFieldTheory.kummerBrauerClass ζ hζ y x := by
  rw [TauCeti.ClassFieldTheory.kummerBrauerClass_def,
    TauCeti.ClassFieldTheory.kummerBrauerClass_def,
    kummerCupPairing_skew (p := p) (a := a) hζ ha, map_neg]

/-- **论文 `cor:symbol-cup` 的逐字形式**：`[(a,b)_ζ] = (a) ∪ (b)`。

（`aUnit K p a ha` 就是 `a` 作为 `Kˣ`；CSA 实例是 `SymbolAlg` 的标准实例，与 `Hyp68`／`Hyp69` 同形。） -/
-- @source file=raw/L20261018.tex locator=label:cor:symbol-cup quote="[(a,b)_F]=(a)\cup(b)\in H^2(F,\mu_p)."
theorem symbolAlg_brauerClass_eq_verbatim (b : Kˣ)
    [Algebra.IsCentral K (SymbolAlg K p a (b : K) ζ)]
    [IsSimpleRing (SymbolAlg K p a (b : K) ζ)]
    [FiniteDimensional K (SymbolAlg K p a (b : K) ζ)] :
    ClassFieldTheory.brauerGroupEquivBr K
        (Additive.ofMul (BrauerGroup.mk (CSA.of K (SymbolAlg K p a (b : K) ζ))))
      = TauCeti.ClassFieldTheory.kummerBrauerClass ζ hζ (aUnit K p a ha) b := by
  haveI := finiteDimensional_range (p := p) (a := a) hζ ha
  haveI := isGalois_range (p := p) (a := a) hζ ha
  rw [symbolAlg_brauerClass_eq (p := p) (a := a) hζ ha b,
    kummerBrauerClass_swap (p := p) (a := a) hζ ha]
  exact neg_neg _

end

end SymbolCupBridge

#print axioms SymbolCupBridge.kummerCupPairing_skew
#print axioms SymbolCupBridge.kummerBrauerClass_swap
#print axioms SymbolCupBridge.symbolAlg_brauerClass_eq_verbatim
