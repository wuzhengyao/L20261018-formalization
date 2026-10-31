import Hyp282
import Hyp158
import Hyp77

/-!
# R1159（**第 3 项收尾：`[D] = (a₁)∪(b₁) + (a₂)∪(b₂)` —— `D` 的代数对象与杯积类完全对齐**）

## 本轮做什么

第 3 项（审计偏差 ③：「`D` 未作代数对象建模」）的两块证据早已在库：

* **`Hyp77.symbolAlg_brauerClass_eq_verbatim`**（`@source label:cor:symbol-cup` 逐字）：
  `[(a,b)_F] = (a)∪(b)`（**精确等式、无比例常数**）；
* **`Hyp158.brauerClass_tensorSymbol`**：`[Sym₁ ⊗ Sym₂] = [Sym₁]·[Sym₂]`。

本轮把它们**合成一条**：`[D] = [(a₁,b₁)]·[(a₂,b₂)] = (a₁)∪(b₁) + (a₂)∪(b₂)`
（`Br` 是乘性写法，`H²` 是加性写法；`brauerGroupEquivBr : Additive (BrauerGroup F) ≃+ Br F` 是加法等价）。

⟹ **偏差 ③ 关闭**：`D` 的**代数对象层**（`SymbolAlg` 的张量积）与其**上同调类**（杯积之和）在同一条定理里对齐。

## 本轮

| 声明 | 内容 |
|---|---|
| **`D_class_eq_cup_sum`** | ★★★★ **`[D] = (a₁)∪(b₁) + (a₂)∪(b₂)`**（论文 `D` 的类，`Br` 口径） |
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open Polynomial AdjoinRoot
open TauCeti

namespace L20261018

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

open SymbolCupBridge in
/-- ★★★★ **论文 `D = (a₁,b₁)_F ⊗ (a₂,b₂)_F` 的 Brauer 类 = 两个杯积类之和**。

由 `Hyp158`（张量积类可乘）＋ `Hyp77`（`[(a,b)]=(a)∪(b)` 逐字，两次）合成。 -/
theorem D_class_eq_cup_sum {a1 a2 : F} (ha1 : ∀ b : F, b ^ p ≠ a1) (ha2 : ∀ b : F, b ^ p ≠ a2)
    {b1 b2 : Fˣ}
    [NeZero p]
    [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a1 : F[X]))]
    [IsSplittingField F (SymbolKummerField.L F p a1) (Polynomial.X ^ p - Polynomial.C a1 : F[X])]
    [Fintype (SymbolKummerField.L F p a1 ≃ₐ[F] SymbolKummerField.L F p a1)]
    [FiniteDimensional F (SymbolKummerField.L F p a1)] [IsGalois F (SymbolKummerField.L F p a1)]
    [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a2 : F[X]))]
    [IsSplittingField F (SymbolKummerField.L F p a2) (Polynomial.X ^ p - Polynomial.C a2 : F[X])]
    [Fintype (SymbolKummerField.L F p a2 ≃ₐ[F] SymbolKummerField.L F p a2)]
    [FiniteDimensional F (SymbolKummerField.L F p a2)] [IsGalois F (SymbolKummerField.L F p a2)]
    [Algebra.IsCentral F (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ)]
    [IsSimpleRing (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ)]
    [FiniteDimensional F (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ)]
    [Algebra.IsCentral F (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)]
    [IsSimpleRing (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)]
    [FiniteDimensional F (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)] :
    ClassFieldTheory.brauerGroupEquivBr F
        (Additive.ofMul (BrauerGroup.mk (CSA.of F (TensorProduct F
          (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ)
          (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)))))
      = ClassFieldTheory.kummerBrauerClass ζ hζ (SymbolCupBridge.aUnit F p a1 ha1) b1
        + ClassFieldTheory.kummerBrauerClass ζ hζ (SymbolCupBridge.aUnit F p a2 ha2) b2 := by
  rw [brauerClass_tensorSymbol (p := p)]
  rw [show Additive.ofMul (BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ))
        * BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)))
      = Additive.ofMul (BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a1 (b1 : F) ζ)))
        + Additive.ofMul (BrauerGroup.mk (CSA.of F (SymbolPres.SymbolAlg F p a2 (b2 : F) ζ)))
    from rfl]
  rw [map_add]
  rw [SymbolCupBridge.symbolAlg_brauerClass_eq_verbatim (hζ := hζ) (a := a1) ha1 (b := b1)]
  rw [show SymbolCupBridge.aUnit F p a1 ha1 = SymbolCupBridge.aUnit F p a1 ha1 from rfl]
  rw [SymbolCupBridge.symbolAlg_brauerClass_eq_verbatim (hζ := hζ) (a := a2) ha2 (b := b2)]

end L20261018

#print axioms L20261018.D_class_eq_cup_sum
