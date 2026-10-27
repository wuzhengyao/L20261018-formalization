import L20261018.Hyp79
/-!
# `μ_p ≅ ℤ/p` 作为 `ZMod p`-**线性**同构（③ 第二半的第一步）

`Hyp79.kummerCoeffEquivZMod` 只给出 `AddEquiv`。要提升到 `TopRep` 层（`TopRep.Hom` 里装的是
`ContinuousLinearMap`，即 `→ₗ[ZMod p]`），必须先有 `ZMod p`-线性性。

本文件补上：

* `kummerCoeffLinearMap : KummerCoeff K p →ₗ[ZMod p] ZMod p`
* `kummerCoeffLinearEquiv : KummerCoeff K p ≃ₗ[ZMod p] ZMod p`

**线性性的证法**：`ZMod p` 的元素都可写成 `↑c.val`（`ZMod.natCast_zmod_val`），
而 `ZMod p`-纯量乘与 `ℕ`-纯量乘通过 `Nat.cast_smul_eq_nsmul` 互换；再用 `map_nsmul`
（加法群同态尊重 `ℕ`-纯量乘）即可。**两侧都化到 `nsmul` 形式**是最省的对齐方式。
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open TauCeti

namespace SymbolCupBridge

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}

section

variable [NeZero p] (hζ : IsPrimitiveRoot ζ p)

include hζ

/-- **纯量乘的相容性**：`kummerCoeffEquivZMod` 是 `ZMod p`-线性的。 -/
theorem kummerCoeffEquivZMod_map_smul (c : ZMod p) (x : KummerCoeff K p) :
    kummerCoeffEquivZMod (p := p) (ζ := ζ) hζ (c • x)
      = c • kummerCoeffEquivZMod (p := p) (ζ := ζ) hζ x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  conv_rhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]

/-- **`μ_p ≅ ℤ/p` 作为 `ZMod p`-线性映射**。 -/
noncomputable def kummerCoeffLinearMap :
    KummerCoeff K p →ₗ[ZMod p] ZMod p where
  toFun := kummerCoeffEquivZMod (p := p) (ζ := ζ) hζ
  map_add' := fun x y => (kummerCoeffEquivZMod (p := p) (ζ := ζ) hζ).map_add x y
  map_smul' := kummerCoeffEquivZMod_map_smul (p := p) (ζ := ζ) hζ

/-- **`μ_p ≅ ℤ/p` 作为 `ZMod p`-线性同构**（双射性由 `AddEquiv` 直接给）。 -/
noncomputable def kummerCoeffLinearEquiv :
    KummerCoeff K p ≃ₗ[ZMod p] ZMod p :=
  LinearEquiv.ofBijective (kummerCoeffLinearMap (p := p) (ζ := ζ) hζ)
    (kummerCoeffEquivZMod (p := p) (ζ := ζ) hζ).bijective

end

end SymbolCupBridge

#print axioms SymbolCupBridge.kummerCoeffEquivZMod_map_smul
#print axioms SymbolCupBridge.kummerCoeffLinearMap
#print axioms SymbolCupBridge.kummerCoeffLinearEquiv
