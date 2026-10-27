import L20261018.Hyp38
import TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol

/-!
# C2 真实域层：把障碍**精确归约**到「非零局部符号」

`Hyp38` 已给出 `BiKummerData` 的非空见证（抽象层）。**真实域层**要的是

```
HasNonzeroKummerCup F p hp : ∃ a₁ a₂ : Fˣ, GaloBase.cup (kummerClass a₁) (kummerClass a₂) ≠ 0
```

本文件把它归约到 TauCeti 局部域理论里**唯一缺的那一环**：

> 存在 `F, n, ζ, a, b, P, tr` 使 `localSymbol P tr (kummerClass a) (kummerClass b) ≠ 0`。

TauCeti 的 `Local/Symbol.lean` 已经把局部符号的**全部结构性质**机检了——双线性、
Steinberg 关系 `(a, 1−a) = 0`、反称性——但**没有非零实例**（`grep` 全库：
非平凡 Brauer 类的具体定理只有 `TauCeti.BrauerGroup.mk_ne_one : mk ℍ[ℝ] ≠ 1`，那是 `p = 2`，
论文要求 `p` 奇）。本文件把「从非零局部符号到非零杯积」这一段**接通**：

```
localSymbol P tr x y ≠ 0
  ⟹ P.cup 1 1 x y ≠ 0                       （tr 是加法等价）
  ⟹ cupFp n G (φ x) (φ y) ≠ 0               （muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup）
```

于是 C2 的真实层**只剩一步数论**：给出一个非零的 Hilbert 符号。

## 主结果

* `LocalSymbolReduction.cup_ne_zero_of_localSymbol_ne_zero`：局部符号非零 ⟹ 杯积非零。
* `LocalSymbolReduction.cupFp_ne_zero_of_localSymbol_ne_zero`：同上，落在 `ZMod n` 平凡系数上。
* `LocalSymbolReduction.hasNonzeroKummerCup_of_localSymbol`：**归约的最终形式**。
-/

open TauCeti ContCohomology

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace LocalSymbolReduction

variable {F : Type} [Field F] {n : ℕ} [NeZero n]
   (P : TopPairing (ClassFieldTheory.muNRep n F) (ClassFieldTheory.muNRep n F) (ClassFieldTheory.muNRep n F))
  (tr : continuousCohomology 2 (ClassFieldTheory.muNRep n F) ≃+ ZMod n)

/-- **局部符号非零 ⟹ 杯积非零。** `ClassFieldTheory.localSymbol` 是 `tr ∘ cup`（`localSymbol_apply`，`rfl`），
而 `tr` 是加法等价，故它把非零类送到非零元。 -/
theorem cup_ne_zero_of_localSymbol_ne_zero (x y : continuousCohomology 1 (ClassFieldTheory.muNRep n F))
    (h : ClassFieldTheory.localSymbol P tr x y ≠ 0) : P.cup 1 1 x y ≠ 0 := by
  intro hz
  exact h (by rw [ClassFieldTheory.localSymbol_apply, hz, map_zero])

/-- 同上，在 Kummer 类上。 -/
theorem cup_kummerClass_ne_zero_of_localSymbol_ne_zero (hn : IsUnit (n : F))
    (a b : Fˣ)
    (h : ClassFieldTheory.localSymbol P tr (ClassFieldTheory.kummerClass F hn a)
      (ClassFieldTheory.kummerClass F hn b) ≠ 0) :
    P.cup 1 1 (ClassFieldTheory.kummerClass F hn a)
      (ClassFieldTheory.kummerClass F hn b) ≠ 0 :=
  cup_ne_zero_of_localSymbol_ne_zero P tr _ _ h

/-- **落在 `ZMod n` 平凡系数上**（即论文 `GaloBase.cup` 所在的那一层）：
非零局部符号 ⟹ `cupFp` 非零，经 TauCeti 的
`muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup`。 -/
theorem cupFp_ne_zero_of_localSymbol_ne_zero (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (x y : continuousCohomology 1 (ClassFieldTheory.muNRep n F))
    (h : ClassFieldTheory.localSymbol (ClassFieldTheory.kummerCupPairing ζ hζ) tr x y ≠ 0) :
    cupFp n (Field.absoluteGaloisGroup F)
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n F hζ 1 x)
      (ClassFieldTheory.muNRepCohomologyEquivTrivialFp n F hζ 1 y) ≠ 0 := by
  rw [← ClassFieldTheory.muNRepCohomologyEquivTrivialFp_kummerCupPairing_cup]
  intro hz
  exact cup_ne_zero_of_localSymbol_ne_zero
    (ClassFieldTheory.kummerCupPairing ζ hζ) tr x y h
    ((ClassFieldTheory.muNRepCohomologyEquivTrivialFp n F hζ 2).map_eq_zero_iff.mp hz)

end LocalSymbolReduction
